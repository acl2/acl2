#!/usr/bin/env perl

# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
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

# errcheck.pl - Scans output files for anything that looks like a failure,
#               e.g., "fail" or "error".  Exits with status 1 if there is any
#               such line found, for use in Makefiles.

# Usage: errcheck.pl [file1] [file2] ...

use strict;
use warnings;

sub check_file_for_errors
{
    my $filename = shift;

    open(my $file, "<", $filename) or die("Error opening $filename: $!");

    my $loc = 1;
    while(my $line = <$file>)
    {
        chomp($line);

        my $error = ($line =~ m/.*fail.*/i) || ($line =~ m/.*error.*/i);
	$error = $error && ! ($line =~ m/.*errors: 0,.*/);

	if ($error) {
	    print "** In $filename, line $loc looks like an error:\n";
	    print "** $line\n";
	    exit(1);
	}

	$loc = $loc + 1;
    }
}

foreach my $i (0 .. $#ARGV)
{
    my $filename = $ARGV[$i];
    check_file_for_errors($filename);
    print "Checked $filename\n";
}

exit(0);
