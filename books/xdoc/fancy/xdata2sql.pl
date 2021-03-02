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

use warnings;
use strict;
use DBI;
use JSON::XS;
use File::Temp qw/ tempdir /;
use Cwd;
use File::Copy;

print <<END;

-------------------------------------------------------------------------------

xdata2sql.pl: Convert xdata.js into xdata.db (an sqlite3 database)

   NOTE: Most folks don\'t need to run this at all!
         If you just want to:
          - browse an XDOC manual on your local hard drive, or
          - share an XDOC manual on your fast intranet
         then ignore this script and just see index.html.

The main use for this script is to share XDOC manuals on the internet.  In this
scenario, just having the web browser load in the entire (generally 20+ MB)
xdata.js file is not very practical, because some users will have slow
connections and will take too long to load the file.

There are many ways to solve this.  Our approach is to convert xdata.js into an
sqlite3 database, and then use a server-side script that will allow us to
access topics only as they are requested.

-------------------------------------------------------------------------------

END

print "; Converting xdata.js\n\n";

sub read_whole_file {
  my $filename = shift;
  open (my $fh, "<", $filename) or die("Can't open $filename: $!\n");
  local $/ = undef;
  my $ret = <$fh>;
  close($fh);
  return $ret;
}

if (! -f "xdata.js") {
    print "Error: xdata.js not found.\n";
    exit(1);
}


print "; Reading file\n";

my $javascript = read_whole_file("xdata.js");


print "; Checking file\n";

my $json;
my $start = "var xdata = ";
if (length($start) < length($javascript)
    && substr($javascript, 0, length($start)) eq $start
    && substr($javascript, length($javascript)-1, 1) eq ";")
{
    my $stop = length($javascript) - length($start) - length(";");
    $json = substr($javascript, length($start), $stop);
}
else {
    print "Error: xdata.js does not have the expected format\n";
    exit(1);
}


print "; Parsing JSON data.\n";
my $xs = new JSON::XS;
my $xdata = $xs->decode($json);
if (!(ref($xdata) eq "HASH")) {
    print "Error: JSON object within xdata.js not a hash?\n";
    exit(1);
}

if (-f "xdata.db") {
    print "; Deleting old xdata.db.\n";
    unlink("xdata.db");
}


print "; Creating new xdata.db.\n";

my $curdir = cwd;
my $dir = tempdir( "xdata2sql_tmpXXXXXX", CLEANUP => 1, TMPDIR => 1);
print "; Using temporary dir $dir\n";

chdir($dir) or die("can't change to temp directory $dir\n");

my $dbh = DBI->connect("dbi:SQLite:dbname=xdata.db", "", "",
		       {RaiseError=>1, AutoCommit=>0})
    or die $DBI::errstr;

print "; Creating xdoc_data table.\n";

$dbh->do("CREATE TABLE XTABLE ("
	 . "XKEY TEXT PRIMARY KEY NOT NULL,"
	 . "XDATA TEXT)");


print "; Populating xdoc_data table.\n";
my $query = $dbh->prepare("INSERT INTO XTABLE (XKEY, XDATA) VALUES (?, ?)");

while(my ($key,$val) = each %$xdata)
{
    my $enc = $xs->encode($val);
    $query->bind_param(1, $key);
    $query->bind_param(2, $enc);
    $query->execute();
}

$dbh->commit();
$dbh->disconnect();

print "; Moving xdata.db back to $curdir\n";
move("xdata.db", "${curdir}/xdata.db");


print "; All done.\n\n";


print "To actually use the database, see xdataget.pl.\n\n";
