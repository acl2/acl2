#!/usr/bin/env perl

# VL Verilog Toolkit
# Copyright (C) 2008-2014 Centaur Technology
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
