#!/usr/bin/env perl

# XDOC Documentation System for ACL2
# Copyright (C) 2009-2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

print "{\"results\":[\n";
for(my $i = 0; $i < @keys; ++$i)
{
    my $key = $keys[$i];
    $query->execute($key);
    my $ret = $query->fetchrow_hashref();
    if (!$ret) {
	print "  \"Error: no such topic.\"";
    }
    else {
	my $val = $ret->{"XDATA"};
	print "  $val";
    }
    if ($i != @keys-1) {
	print ",\n";
    }
}
print "\n]}\n";

$query->finish();
$dbh->disconnect();


