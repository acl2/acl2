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


# pcert.pl -- This is a new implementation of Milawa's pcert mechanism which is
# separated from OMake.  Milawa's pcert system predates that of ACL2's.  It is
# rather specialized and probably doesn't make sense for projects other than
# Milawa.  This requires that the book's dependencies are up to date.

use strict;
use warnings;
use File::Spec;
use FindBin qw($RealBin);

my $MODIFIED_ACL2 = File::Spec->rel2abs("$RealBin/modified-acl2");
(do "$RealBin/pcert-util.pl") or die ("Error loading $RealBin/pcert-util.pl:\n!: $!\n\@: $@\n");

my $HELP = <<END;
Usage: pcert.pl bookname
Milawa\'s provisional certification system.
END

if (@ARGV != 1)
{
    print "Error: Expected exactly one argument.\n";
    print $HELP;
    exit(1);
}

# Bookname without extension
my $BOOKNAME = ($ARGV[0] =~ m/(.*)\.lisp$/) ? $1
             : ($ARGV[0] =~ m/(.*)\.mpcert$/) ? $1
             : $ARGV[0];

if (! -f "$BOOKNAME.lisp") {
    print "Error: $BOOKNAME.lisp does not exist.\n";
    print $HELP;
    exit(1);
}

my $RELIMAGE = infer_book_image($BOOKNAME, $MODIFIED_ACL2);

my ($vol, $dir, $file) = File::Spec->splitpath($BOOKNAME);
my $base     = File::Spec->catpath($vol, $dir, "");
my $ABSIMAGE = File::Spec->rel2abs("../../acl2-images/$RELIMAGE", $base);

#print "BOOKNAME is $BOOKNAME\n";
#print "ABSIMAGE is $ABSIMAGE\n";

my $okp = pcert_book($BOOKNAME, $ABSIMAGE);

if ($okp) {
    exit(0);
}

exit(1);

