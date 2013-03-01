#!/usr/bin/env perl

# clean.pl -- clean up targets from cert.pl
# Copyright 2008-2009 by Sol Swords and Jared Davis
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
# details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 675 Mass
# Ave, Cambridge, MA 02139, USA.
#
# NOTE.  This file is not part of the standard ACL2 books build process; it is
# part of an experimental build system that is not yet intended, for example,
# to be capable of running the whole regression.  The ACL2 developers do not
# maintain this file.  Please contact Sol Swords <sswords@cs.utexas.edu> with
# any questions/comments.

use strict;
use warnings;

use Getopt::Long qw(:config bundling_override);

my $helpstr = '
\nclean.pl: clean up generated files from running cert.pl

Usage:
perl clean.pl --targets targets

Where targets is a file that contains a list of Lisp files, one per line.  This
file just removes temporary files like foo.cert, foo.cert.out, etc.  Ordinarily
there would be no reason to call this file by hand, instead it would usually be
run by invoking "make clean" or similar.
';

my $targets = "";

GetOptions ("help|h" => sub { print $helpstr;
			      exit 0 ; },
            "targets=s" => \$targets);

if (! $targets) {
    print "clean.pl: targets file is required!\n";
    exit(1);
}

if (! -f $targets) {
    print "clean.pl: not a file: $targets\n";
    exit(1);
}

print "TARGETS is $targets\n";

my @rm;
open(FD, "<$targets") or die("can't open $targets: $!");
while (my $line = <FD>) {
    chomp($line);
    if (! ($line =~ m/^(.*).lisp$/)) {
	print "Invalid target line: $line\n";
	next;
    }
    my $book = $1;
    push(@rm, "$book.cert");
    push(@rm, "$book.pcert1");
    push(@rm, "$book.pcert0");
    push(@rm, "$book.acl2x");
    push(@rm, "$book.cert.out");
    push(@rm, "$book.cert.time");
    push(@rm, "$book.pcert1.out");
    push(@rm, "$book.pcert0.out");
    push(@rm, "$book.acl2x.out");
    push(@rm, "$book.cert.time");
    push(@rm, "$book.pcert1.time");
    push(@rm, "$book.pcert0.time");
    push(@rm, "$book.acl2x.time");
    push(@rm, "$book.o");
    push(@rm, "$book.h");
    push(@rm, "$book.c");
    push(@rm, "$book.acl2x");
    push(@rm, "$book.port");
    push(@rm, "$book.bin");
    push(@rm, "$book.sbin");
    push(@rm, "$book.lbin");
    push(@rm, "$book.fasl");
    push(@rm, "$book.ufsl");
    push(@rm, "$book.64ufasl");
    push(@rm, "$book.ufasl");
    push(@rm, "$book.pfsl");
    push(@rm, "$book.dfsl");
    push(@rm, "$book.d64fsl");
    push(@rm, "$book.dx32fsl");
    push(@rm, "$book.dx64fsl");
    push(@rm, "$book.lx32fsl");
    push(@rm, "$book.lx64fsl");
    push(@rm, "$book.wx32fsl");
    push(@rm, "$book.wx64fsl");
    push(@rm, "$book.sparcf");
    push(@rm, "$book.axpf");
    push(@rm, "$book.x86f");
    push(@rm, "$book.ppcf");
    push(@rm, "$book.fas");
    push(@rm, "$book.lib");
    push(@rm, "$book.sse2f");
}

close(FD);

my $num_to_remove = @rm;
print "clean.pl: about to try removing as many as $num_to_remove files.\n";
my $start = time();
my $num_removed = unlink(@rm);
my $end = time();
my $elapsed = $end - $start;
print "clean.pl: removed $num_removed files in $elapsed seconds.\n";
exit(0);


