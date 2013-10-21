#!/usr/bin/env perl

# Milawa pcert-util.pl
# Copyright (C) 2005-2012 by Jared Davis <jared@cs.utexas.edu>
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program (see the file COPYING); if not, write to the
# Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

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
