#!/usr/bin/env perl

# memsum.pl
# Copyright (C) 2015 Centaur Technology
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

use strict;
use warnings;
use File::Find;
use File::Spec;
use List::Util qw(sum max);

# Summarize Full GC messages from .cert.out files.
#
# Usage: memsum.pl
#
#   - Recursively scans the file system for .cert.out files
#   - Greps through them for full gc messages
#   - Prints a report that you can read.

sub nice_size
{
    my $bytes = shift;
    if ($bytes < 1024) {
	return $bytes . "b";
    }
    elsif ($bytes < 1024*1024) {
	return sprintf("%.2f", ($bytes / 1024)) . "kb";
    }
    elsif ($bytes < 1024*1024*1024) {
	return sprintf("%.2f", ($bytes / (1024*1024))) . "mb";
    }
    else {
	return sprintf("%.2f", ($bytes / (1024*1024*1024))) . "gb";
    }
}

sub collect_gc_messages
{
    my $filename = shift;
    my $fh;
    if (!open ($fh, "<", $filename)) {
	die "Failed to open $filename\n";
    }

    my @gcs = ();
    while (my $line = <$fh>) {
	if ($line =~ /;;; Starting full GC,[ \t]*([0-9,]*)[ \t]*bytes allocated\./) {
	    my $alloc = $1;    # Extract how many bytes were allocated
	    $alloc =~ s/,//g;  # Remove all commas
	    push(@gcs, $alloc);
	}
    }

    close($fh);

    my $numgcs = @gcs;
    my $avgbytes = ($numgcs == 0) ? 0 : sum(@gcs) / @gcs;
    my $maxbytes = ($numgcs == 0) ? 0 : max(@gcs);

    my $ret = {};
    $ret->{'filename'} = $filename;
    $ret->{'numgcs'} = $numgcs;
    $ret->{'maxbytes'} = $maxbytes;
    $ret->{'avgbytes'} = $avgbytes;
    return $ret;
}

my @ENTRIES = ();

sub consider_file
{
    my $filename = $_;
    return unless ($filename =~ /.cert.out$/);
    push(@ENTRIES, collect_gc_messages($filename));
}

find({ wanted => \&consider_file, no_chdir => 1 }, ".");

my @SORTED = sort { $b->{'maxbytes'} <=> $a->{'maxbytes'} } @ENTRIES;

my $maxlen = 0;
foreach my $ent (@SORTED) {
    my $thislen = length($ent->{'filename'});
    if ($thislen > $maxlen) {
	$maxlen = $thislen;
    }
}

printf("%-" . $maxlen . "s  %10s  %10s  %10s\n", "File", "Max", "Avg", "Full GCs");

foreach my $ent (@SORTED) {
    printf("%-" . $maxlen . "s  %10s  %10s  %10s\n",
	   $ent->{'filename'},
	   nice_size($ent->{'maxbytes'}),
	   nice_size($ent->{'avgbytes'}),
	   $ent->{'numgcs'});

}

