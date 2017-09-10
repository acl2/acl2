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
    $wrap .= "<!ENTITY ndash \"&#8211;\">";
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
	my $results = "";
	my $shortxml = "";
	$shortxml = "<p>$short</p>";
	$shortxml = wrap_xdoc_fragment($shortxml);
	$shortxml = $xml_parser->parse_string($shortxml);
	$results = $stylesheet->transform($shortxml);
	my $short_output = $stylesheet->output_string($results);

	my $bothxml = "";
	$bothxml .= "<p>$short</p>$long";
	$bothxml = wrap_xdoc_fragment($bothxml);

	$bothxml = $xml_parser->parse_string($bothxml);
	$results = $stylesheet->transform($bothxml);
	my $both_output = $stylesheet->output_string($results);


	my $pagehtml .= "<html>\n<head>\n";
	$pagehtml .= "<meta charset=\"UTF-8\">\n";
	$pagehtml .= "<title>$human_readable_name</title>\n";
	# I thought it would be nice to include a description, but
	# topics like BOOKS_CERTIFICATION need their links escaped.
	# Too hard for now.
	# $pagehtml .= "<meta name=\"description\" content=\"$short_output\">\n";
	$pagehtml .= "<link rel=\"stylesheet\" type=\"text/css\" href=\"../style.css\"/>\n";

	# The below javascript causes the client to redirect.  In a
	# move of desperation to be re-indexed by search engines, we
	# are removing the redirect.  It appears that Googlebot crawls
	# the static page so long as the timout is at least 5 seconds
	# (it could be 4 seconds, but I didn't test it -- 3 seconds
	# results in google crawling the redirected page [index.html],
	# which isn't our goal [because it will fail to do so in a
	# productive way]).  But, search results didn't reinforce this
	# idea, so we are just removing the redirect.

	# $pagehtml .= "<script language=\"javascript\">\n";
	# $pagehtml .= "<!--\n";
	# $pagehtml .= "  setTimeout(function () {
        #               window.location = \"../index.html?topic=$key\";
        #             }, 5000);\n";
	# $pagehtml .= "//-->\n";
	# $pagehtml .= "</script>\n";

# One can instead call the following to prevent the redirect from
# showing up in the history.
# window.location.replace(\"../index.html?topic=$key\");

	$pagehtml .= "</head>\n<body>\n\n";
	# $pagehtml .= "<h3>Redirecting to $human_readable_name ";
	# $pagehtml .= "in the <a href=\"../index.html?topic=$key\">Full Manual</a></h3>\n\n";

# Since we can't get Google to search the static pages with
# redirecting enabled, we have fallen back to having no redirect.

	$pagehtml .= "<h3><a href=\"../index.html?topic=$key\">Click for ";
	$pagehtml .= "$human_readable_name";
	$pagehtml .= " in the Full Manual</a></h3>\n\n";

	$pagehtml .= "$both_output";
	$pagehtml .= "</body>\n</html>\n";

	print $fh "$pagehtml";

	$progress++;
	if ($progress % 500 == 0) {
		print "; Done generating $progress HTML files\n";
	}
}

print "; All done. Generated $progress HTML files.\n\n";
