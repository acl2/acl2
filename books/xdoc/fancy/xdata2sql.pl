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

if (! -f "xindex.js") {
    print "Error: xindex.js not found.\n";
    exit(1);
}


print "; Reading file\n";

my $xdata_javascript = read_whole_file("xdata.js");
my $xindex_javascript = read_whole_file("xindex.js");


print "; Checking files\n";

my $xdata_json;
my $start = "var xdata = ";
if (length($start) < length($xdata_javascript)
    && substr($xdata_javascript, 0, length($start)) eq $start
    && substr($xdata_javascript, length($xdata_javascript)-1, 1) eq ";")
{
    my $stop = length($xdata_javascript) - length($start) - length(";");
    $xdata_json = substr($xdata_javascript, length($start), $stop);
}
else {
    print "Error: xdata.js does not have the expected format\n";
    exit(1);
}

my $xindex_json;
my $start = "var xindex = ";
if (length($start) < length($xindex_javascript)
    && substr($xindex_javascript, 0, length($start)) eq $start
    && substr($xindex_javascript, length($xindex_javascript)-1, 1) eq ";")
{
    my $stop = length($xindex_javascript) - length($start) - length(";");
    $xindex_json = substr($xindex_javascript, length($start), $stop);
}
else {
    print "Error: xindex.js does not have the expected format\n";
    exit(1);
}


print "; Parsing JSON data.\n";
my $xs = new JSON::XS;
my $xdata = $xs->decode($xdata_json);
if (!(ref($xdata) eq "HASH")) {
    print "Error: JSON object within xdata.js not a hash?\n";
    exit(1);
}

my $xs = new JSON::XS;
my $xindex = $xs->decode($xindex_json);

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

print "; Creating xtable.\n";

$dbh->do(q{
    CREATE TABLE xtable (
        xkey TEXT PRIMARY KEY NOT NULL,
        xtopic TEXT,
        xparents TEXT,
        xsrc TEXT,
        xpkg TEXT,
        xshort TEXT,
        xlong TEXT)
});


print "; Populating xtable.\n";

my $xdata_query = $dbh->prepare(q{
    INSERT INTO xtable (xkey, xparents, xsrc, xpkg, xlong)
    VALUES (?, ?, ?, ?, ?)
});
while(my ($key,$val) = each %$xdata)
{
    $xdata_query->bind_param(1, $key);
    $xdata_query->bind_param(2, $xs->encode($val->[0]));
    $xdata_query->bind_param(3, $xs->encode($val->[1]));
    $xdata_query->bind_param(4, $xs->encode($val->[2]));
    $xdata_query->bind_param(5, $xs->encode($val->[3]));

    $xdata_query->execute();
}

my $xindex_query = $dbh->prepare(q{
    UPDATE xtable
    SET xtopic=?, xshort=?
    WHERE xkey=?;
});
foreach my $val (@$xindex)
{
    $xindex_query->bind_param(1, $xs->encode($val->[2]));
    $xindex_query->bind_param(2, $xs->encode($val->[4]));
    $xindex_query->bind_param(3, $val->[0]);

    $xindex_query->execute();
}

print "; Creating xtable_fts.\n";

$dbh->do(q{
    CREATE VIRTUAL TABLE xtable_fts
    USING fts5(
        xkey,
        xtopic,
        xshort,
        xlong,
        content='xtable',
        content_rowid='rowid')
});

print "; Populating xtable_fts.\n";
$dbh->do(q{
    INSERT INTO xtable_fts(xkey, xtopic, xshort, xlong)
    SELECT xkey, xtopic, xshort, xlong FROM xtable
});

$dbh->commit();
$dbh->disconnect();

print "; Moving xdata.db back to $curdir\n";
move("xdata.db", "${curdir}/xdata.db");


print "; All done.\n\n";


print "To actually use the database, see xdataget.pl.\n\n";
