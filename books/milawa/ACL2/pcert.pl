#!/usr/bin/env perl

# Milawa pcert.pl
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

