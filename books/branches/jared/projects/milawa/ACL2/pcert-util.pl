#!/usr/bin/env perl

# Milawa - A Reflective Theorem Prover
# Copyright (C) 2005-2009 Kookamara LLC
#
# Contact:
#
#   Kookamara LLC
#   11410 Windermere Meadows
#   Austin, TX 78759, USA
#   http://www.kookamara.com/
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
# Original author: Jared Davis <jared@kookamara.com>

# pcert-util.pl
# Helper routines for pcert.pl and pcert-scan.pl

use strict;
use warnings;

sub trim
{
    my $str = shift;
    $str =~ s/^\s+//;
    $str =~ s/\s+$//;
    return $str;
}

sub read_image_file
{
    my $path = shift;
    open (my $fh, "<", $path) or die "Can't open file: $!";
    local $/ = undef;
    my $content = <$fh>;
    close $fh;
    $content = trim($content);
    return $content if ($content =~ m/^[A-Za-z0-9_\-.\/]+$/);
    die "Image file $path contains invalid content $content";
}

sub infer_book_image
{
    my $bookname = shift; # bookname with no extension
    my $default_img = shift;
    my ($vol, $dir, $file) = File::Spec->splitpath($bookname);
    my $base     = File::Spec->catpath($vol, $dir, "");
    my $bookimg  = File::Spec->catpath($vol, $dir, "$bookname.image");
    my $certimg  = File::Spec->catpath($vol, $dir, "cert.image");
    my $relimage = (-f $bookimg) ? read_image_file($bookimg)
	         : (-f $certimg) ? read_image_file($certimg)
   	         : $default_img;
    # Quick hack to make this work for Milawa.  In general we should
    # add support for a --bindir as in cert.pl
    # my $absimage = File::Spec->rel2abs($relimage, $base);
    return $relimage;
}

sub collect_include_books
{
    # Returns an array of [bookname . dir] entries
    my $filename = shift;
    open(my $fd, "<", $filename) or die("can't open $filename: $!");
    my $regexp = "^[^;]*\\(include-book[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @ret = ();
    while(<$fd>) {
	my @tmp = ($_ =~ m/$regexp/i);
	if (@tmp) {
	    push(@ret, [$tmp[0], $tmp[1] || ""])
	}
    }
    close($fd);
    return \@ret;
}

sub pcert_book
{
    my $bookname = shift; # bookname with no extension
    my $absimage = shift; # full path to book image

    if (! -x $absimage) {
	die "$absimage (needed for $bookname) is not executable!";
    }

    my ($vol, $dir, $file) = File::Spec->splitpath($bookname);
    my $base = File::Spec->catpath($vol, $dir, "");
    chdir($base);

    $ENV{"ACL2_CUSTOMIZATION"} = "NONE";

    my $instrs = "(in-package \"ACL2\")
(provisionally-certify \"$file\")
(exit 0)
";

#    print "INSTRS = \n$instrs\n";

    $SIG{PIPE} = 'IGNORE';
    open(my $fd, "|$absimage") or die("can't run $absimage: $!");
    print $fd $instrs;
    close($fd);

    my $status = $? >> 8;
    if ($status == 44) {
        # see interface/pcert.lisp -- we return 44 only on success.
        return 1;
    }
    return 0;
}

1;
