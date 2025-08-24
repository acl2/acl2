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


# xdataget.pl: Interact with the XDATA SQL database, by either looking up some
# key(s) or searching a query with FTS5.
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
use HTML::Entities;

my $cgi = CGI->new;
print $cgi->header("application/json");

my $arg_keys = $cgi->param("keys") || "";
my $arg_search = $cgi->param("search") || "";

my $json = JSON->new;

sub lookup_keys {
    if (!($arg_keys =~ /^[A-Za-z0-9:._\-]*$/)) {
        print $json->encode(
            { error => "Keys contain illegal characters, rejecting to prevent xss attacks." });
        exit;
    }

    my @keys = split(':', $arg_keys);

    if (! -f "xdata.db") {
        print $json->encode({ error => "xdata.db not found" });
        exit;
    }

    my $dbh = DBI->connect("dbi:SQLite:dbname=xdata.db", "", "", {RaiseError=>1});
    my $query = $dbh->prepare("SELECT * FROM xtable WHERE xkey=?");

    my @results;
    for my $key (@keys) {
        $query->execute($key);
        my $ret = $query->fetchrow_hashref();

        if (!$ret) {
            push @results, { error => "no such topic." };
        }
        else {
            my $xparents = $json->decode($ret->{"xparents"});
            my $xsrc = $json->decode($ret->{"xsrc"});
            my $xpkg = $json->decode($ret->{"xpkg"});
            my $xlong = $json->decode($ret->{"xlong"});
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
}

sub escape_fts5_query {
    my ($query) = @_;

    # Add quotes around characters that would otherwise be interpreted specially
    # by FTS5.
    $query =~ s/-/"-"/g;
    $query =~ s/\*/"\*"/g;
    $query =~ s/\^/"\^"/g;
    $query =~ s/\+/"\+"/g;

    return $query;
}

sub search {
    if (!($arg_search =~ /^[A-Za-z0-9:._\- \"\^\*\+]*$/)) {
        print $json->encode(
            { error => "Search contains illegal characters, rejecting to prevent xss attacks." });
        exit;
    }

    if (! -f "xdata.db") {
        print $json->encode({ error => "xdata.db not found" });
        exit;
    }

    my $dbh = DBI->connect("dbi:SQLite:dbname=xdata.db", "", "", {RaiseError=>1});
    my $query = $dbh->prepare(q{
        SELECT xkey,
               bm25(xtable_fts, 0.0, 100.0, 5.0, 1.0) as score
        FROM xtable_fts
        WHERE xtable_fts MATCH ?
        ORDER BY score
        LIMIT 100
    });
    $query->execute(escape_fts5_query($arg_search));

    my $rows = $query->fetchall_arrayref({});
    my $json = JSON->new;
    my $json_output = $json->encode({results => \@$rows});
    print $json_output;

    $query->finish();
    $dbh->disconnect();
}

if ($arg_keys ne "") {
    lookup_keys();
} elsif ($arg_search ne "") {
    search();
} else {
    print $json->encode(
        { error => "No query string parameter provided." });
    exit;
}
