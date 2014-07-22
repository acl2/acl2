#!/usr/bin/env perl

# Xdoc to HTML Converter
# Copyright (C) 2014 David Rager (ragerdl@cs.utexas.edu)
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

use warnings;
use strict;
use JSON::XS;
use XML::LibXML;
use XML::LibXSLT;

print <<END;

-------------------------------------------------------------------------------

xdata2html.pl: Convert xdata.js and xindex.js into HTML files so
               search engines can crawl our doucmentation.

   NOTE: Only those who are trying make their Xdoc manual accessible
         to search engines need to run this script.  Otherwise, they
         should just use index.html.

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

sub wrap_xdoc_fragment {
	my $str = shift;
    my $wrap = "<!DOCTYPE xdoc [";
    $wrap .= "<!ENTITY mdash \"&#8212;\">";
    $wrap .= "<!ENTITY rarr \"&#8594;\">";
    $wrap .= "<!ENTITY nbsp \"&#160;\">";
    $wrap .= "]>";
    $wrap .= "<root>$str</root>";
    return $wrap;
}

if (! -f "xdata.js") {
    print "Error: xdata.js not found.\n";
    exit(1);
}

print "; Reading file\n";

my $xdatastr = read_whole_file("xdata.js");
print "; Checking xdata file\n";

my $json;
my $start = "var xdata = ";
if (length($start) < length($xdatastr)
    && substr($xdatastr, 0, length($start)) eq $start
    && substr($xdatastr, length($xdatastr)-1, 1) eq ";")
{
    my $stop = length($xdatastr) - length($start) - length(";");
    $json = substr($xdatastr, length($start), $stop);
}
else {
    print "Error: xdata.js does not have the expected format\n";
    exit(1);
}

print "; Parsing JSON data.\n";
my $xsd = new JSON::XS;
my $xdata = $xsd->decode($json);
if (!(ref($xdata) eq "HASH")) {
    print "Error: JSON object within xdata.js not a hash?\n";
    exit(1);
}


my $xindexstr = read_whole_file("xindex.js");
print "; Checking xindex file\n";

if (! -f "xindex.js") {
    print "Error: xindex.js not found.\n";
    exit(1);
}

$start = "var xindex = ";
if (length($start) < length($xindexstr)
    && substr($xindexstr, 0, length($start)) eq $start
    && substr($xindexstr, length($xindexstr)-1, 1) eq ";")
{
    my $stop = length($xindexstr) - length($start) - length(";");
    $json = substr($xindexstr, length($start), $stop);
}
else {
    print "Error: xindex.js does not have the expected format\n";
    exit(1);
}

print "; Parsing JSON index.\n";
my $xsi = new JSON::XS;
my $xindex = $xsi->decode($json);
if (!(ref($xindex) eq "ARRAY")) {
    print "Error: JSON object within xindex.js not a hash?\n";
    exit(1);
}

my %shorts = ();
my %human_readable_names = ();
foreach my $entry (@$xindex) {
	$shorts{$entry->[0]} = $entry->[4];
	$human_readable_names{$entry->[0]} = $entry->[1];
}

my $xml_parser  = XML::LibXML->new;
my $xslt_parser = XML::LibXSLT->new;
my $xsl = $xml_parser->parse_file("render-html.xsl");
my $stylesheet  = $xslt_parser->parse_stylesheet($xsl);

my $progress = 0;
while(my ($key,$val) = each %$xdata)
{
	my $filename = "HTML/$key.html";
	open (my $fh, ">", $filename) or die "Could not open $filename";

    my $enc = $xsd->encode($val);
	my $long = $val->[3];
	my $human_readable_name = $human_readable_names{$key};
	my $short = $shorts{$key};
	my $pagexml = "";
	$pagexml .= "<p>$short</p>\n";
	$pagexml .= "$long";
	$pagexml = wrap_xdoc_fragment($pagexml);
	my $xml = $xml_parser->parse_string($pagexml);
	my $results = "";
    $results = $stylesheet->transform($xml);
	my $output = $stylesheet->output_string($results);


	my $pagehtml .= "<html>\n<head>\n";
	$pagehtml .= "<meta charset=\"UTF-8\">\n";
	$pagehtml .= "<title>$human_readable_name</title>\n";
	# To debug this script, you may need to comment out the
	# javascript, since it causes the browser to immediately redirect.
	# Since it's javascript, this redirect should not be run by search
	# engines, allowing them to crawl this HTML page.
	$pagehtml .= "<script language=\"javascript\">\n";
	$pagehtml .= "<!--\n";
	$pagehtml .= "  location.replace(\"../index.html?topic=$key\");\n";
	$pagehtml .= "//-->\n";
	$pagehtml .= "</script>\n";
	$pagehtml .= "<link rel=\"stylesheet\" type=\"text/css\" href=\"../style.css\"/>\n";
    $pagehtml .= "</head>\n<body>\n\n<h3>";
    $pagehtml .= "$key";
	$pagehtml .= "</h3>\n\n";
	$pagehtml .= "$output";
	$pagehtml .= "</body>\n</html>\n";

	print $fh "$pagehtml";

	if ($progress % 500 == 0) {
		print "Done generating $progress HTML files\n";
	}
	$progress++;
}

print "; All done.\n\n";
