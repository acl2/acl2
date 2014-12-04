#!/usr/bin/env perl

# XDOC Documentation System for ACL2
# Copyright (C) 2014 Sebaastian Joosten
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
# Contributing authors: Jared Davis <jared@centtech.com>
#                       Sebastiaan Joosten
#                       David L. Rager <ragerdl@gmail.com>

use warnings;
use strict;
use DBI;
use JSON::XS;

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


print "; Reading xdata file\n";

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

if (-f "xdata-seo.db") {
    print "; Deleting old xdata-seo.db.\n";
    unlink("xdata-seo.db");
}

print "; Creating new xdata-seo.db.\n";
my $dbh = DBI->connect("dbi:SQLite:dbname=xdata-seo.db", "", "",
		       {RaiseError=>1, AutoCommit=>0})
    or die $DBI::errstr;

print "; Creating xdoc_data table.\n";

$dbh->do("CREATE TABLE xdoc_data ("
	 . "XKEY TEXT PRIMARY KEY NOT NULL,ID INT,"
	 . "PARENTS TEXT,SOURCE TEXT,PACKAGE TEXT,LONGDESC TEXT,"
	 . "TITLE TEXT,NAME TEXT,PARENTIDS TEXT,CHILDREN TEXT,SHORTDESC TEXT)");

print "; Populating xdoc_data table.\n";
my $query = $dbh->prepare("INSERT INTO xdoc_data (XKEY, PARENTS, CHILDREN, SOURCE, PACKAGE, LONGDESC) VALUES (?, ?, '', ?, ?, ?)");
while(my ($key,$val) = each %$xdata)
{
    $query->bind_param(1, $key);
    $query->bind_param(2, $xs->encode(@$val[0]));
    $query->bind_param(3, @$val[1]);
    $query->bind_param(4, @$val[2]);
    $query->bind_param(5, @$val[3]);
    $query->execute();
}
$query->bind_param(1, 'DOCINDEX');
$query->bind_param(2, '');
$query->bind_param(3, '');
$query->bind_param(4, '');
$query->bind_param(5, '');
$query->execute();
$query->bind_param(1, 'DOCNOTFOUND');
$query->bind_param(2, '');
$query->bind_param(3, '');
$query->bind_param(4, '');
$query->bind_param(5, '<p>Sorry friend, the topic you were trying to reach doesn\'t exist.</p><p>Sometimes this happens because we make a link to the wrong package or just misspell something. A quick search (or even jump to) might help you find what you want.</p>');
$query->execute();

if (! -f "xindex.js") {
    print "Error: xindex.js not found.\n";
    exit(1);
}


print "; Reading xindex file\n";

$javascript = read_whole_file("xindex.js");


print "; Checking file\n";

$start = "var xindex = ";
if (length($start) < length($javascript)
    && substr($javascript, 0, length($start)) eq $start
    && substr($javascript, length($javascript)-1, 1) eq ";")
{
    my $stop = length($javascript) - length($start) - length(";");
    $json = substr($javascript, length($start), $stop);
}
else {
    print "Error: xindex.js does not have the expected format\n";
    exit(1);
}

print "; Parsing JSON data.\n";
$xs = new JSON::XS;
$xdata = $xs->decode($json);
if (!(ref($xdata) eq "ARRAY")) {
    print "Error: JSON object within xindex.js not an array?\n";
    exit(1);
}

print "; Populating xdoc_data table some more.\n";
$query = $dbh->prepare("UPDATE xdoc_data SET TITLE=?, NAME=?, PARENTIDS=?, SHORTDESC=?, ID=? WHERE XKEY=?");
my $query2 = $dbh->prepare("UPDATE xdoc_data SET CHILDREN=CHILDREN || ',' || ? WHERE XKEY=?");
my $val;
my $i=0;
foreach $val (@$xdata)
{
    $query->bind_param(1, @$val[1]);
    $query->bind_param(2, @$val[2]);
    $query->bind_param(3, $xs->encode(@$val[3]));
    $query->bind_param(4, @$val[4]);
    $query->bind_param(5, $i);
    $query->bind_param(6, @$val[0]);
    $query->execute();
    my $children = @$val[3];
    my $parent;
    foreach $parent (@$children){
      if($parent>-1){
        my $parentRef = @$xdata[$parent];
        $query2->bind_param(2, @$parentRef[0]);
        $query2->bind_param(1, @$val[0]);
        $query2->execute();
      } # ignore broken parents
    }
    $i=$i+1;
}
$query->bind_param(1, 'ACL2 Index');
$query->bind_param(2, 'ACL2 Index');
$query->bind_param(3, '');
$query->bind_param(4, '');
$query->bind_param(5, -1);
$query->bind_param(6, 'DOCINDEX');
$query->execute();
$query->bind_param(1, 'ACL2 Documentation page not found');
$query->bind_param(2, '');
$query->bind_param(3, '');
$query->bind_param(4, '');
$query->bind_param(5, -2);
$query->bind_param(6, 'DOCNOTFOUND');
$query->execute();
$dbh->do("CREATE INDEX id_index ON xdoc_data (ID)");

$dbh->commit();
$dbh->disconnect();

print "; All done\n\n";

