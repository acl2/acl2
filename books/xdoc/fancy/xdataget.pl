#!/usr/bin/env perl

# XDOC Documentation System for ACL2
# Copyright (C) 2009-2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Jared Davis <jared@centtech.com>


# xdataget.pl: look up a key (or several keys) from the XDATA SQL database.
#
# This is a companion script for xdata2sql.pl.
# Typically the flow is:
#   - Create xdata.js using xdoc::save.
#   - Create xdata.db using xdata2sql.pl.
#   - Run xdataget.pl keys=COMMON-LISP____APPEND:ACL2____TOP to test it
#   - Copy xdata.db and xdataget.pl into your web server.
#
# Now if you point your browser to something like:
#    http://server/cgi-bin/xdataget.pl?keys=COMMON-LISP____APPEND:ACL2____TOP
#
# And you should see a JSON reply.

use warnings;
use strict;
use DBI;
use CGI;
use JSON;

my $cgi = CGI->new;
print $cgi->header("application/json");

my $arg = $cgi->param("keys") || "";

if (!($arg =~ /^[A-Za-z0-9:._\-]*$/))
{
    print "{\"error\":\"keys contain illegal characters, rejecting to prevent xss attacks.\"}\n";
    exit;
}

my @keys = split(':', $arg);

if (! -f "xdata.db") {
    print "{\"error\":\"xdata.db not found\"}\n";
    exit;
}

my $dbh = DBI->connect("dbi:SQLite:dbname=xdata.db", "", "", {RaiseError=>1});
my $query = $dbh->prepare("SELECT * FROM XTABLE WHERE XKEY=?");

my @results;
my $json = JSON->new;
for my $key (@keys) {
    $query->execute($key);
    my $ret = $query->fetchrow_hashref();

    if (!$ret) {
        push @results, { error => "no such topic." };
    }
    else {
        my $xparents = $json->decode($ret->{"XPARENTS"});
        my $xsrc = $json->decode($ret->{"XSRC"});
        my $xpkg = $json->decode($ret->{"XPKG"});
        my $xlong = $json->decode($ret->{"XLONG"});
        push @results, {
            parents => $xparents,
            src => $xsrc,
            pkg => $xpkg,
            long => $xlong
        };
    }
}
my $output = { results => \@results };
print $json->encode($output);

$query->finish();
$dbh->disconnect();
