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

use strict;
use warnings;
use File::Spec;
use FindBin qw($RealBin);
use Cwd;

my $MODIFIED_ACL2 = File::Spec->rel2abs("$RealBin/modified-acl2");
(do "$RealBin/pcert-util.pl") or die ("Error loading $RealBin/pcert-util.pl:\n!: $!\n\@: $@\n");

sub build_depgraph
{
    my $path = shift;      # Should be /path/to/bookname {with no extension}
    my $deps = shift;      # Hash, main graph, bookname -> deps hash
    my $deporder = shift;  # Array, dependency ordered list of books

#    print "Starting $path\n";

    my ($vol, $dir, $file) = File::Spec->splitpath($path);
    my $look = $deps->{$path} || "";
    die "Circular dependencies for $path" if ($look eq "EXPLORING");
    return if $look; # already dealt with this book
    $deps->{$path} = "EXPLORING";

    my %selfdeps = ();
    my $includes = collect_include_books("$path.lisp");
    foreach my $entry (@$includes)
    {
	my $bookname = $entry->[0];
	my $dirpart = $entry->[1];
	if ($dirpart) { die "Add :dir support\n"; }
	my $subbook = File::Spec->catpath($vol, $dir, $bookname);
	$selfdeps{$subbook} = 1;
#	print "$path: $subbook\n";
	build_depgraph($subbook, $deps, $deporder);
	# Assuming we fully explored subbook and got all its deps, we
	# just need to jam them into our own deps.
	my $subdeps = $deps->{$subbook};
	if ($subdeps) {
	    foreach(keys %$subdeps) {
#		print "$path: inheriting $_ from $subbook\n";
		$selfdeps{$_} = 1;
	    }
	}
    }

    push(@$deporder, $path);
    $deps->{$path} = \%selfdeps;

#    print "Done $path\n";
}

my %deps = ();
my @deporder = ();
foreach(@ARGV) {
    build_depgraph($_, \%deps, \@deporder);
}

my $ndeps = @deporder;
print "# pcert-scan.pl deps for $ndeps files\n\n";


foreach my $book (@deporder)
{
    my $bookdeps = $deps{$book};
    my $bookimg = infer_book_image($book, $MODIFIED_ACL2);
    my $relimg = File::Spec->abs2rel($bookimg);
    my $mangle = $book;
    $mangle =~ s|/|__|g;
    print "PCDEPS_FOR_$mangle := \\\n";
    print "    $book.lisp \\\n";
    foreach(keys %$bookdeps) {
	print "    $_.lisp \\\n";
    }
    # BOZO path stuff isn't very general here.
    print "    acl2-images/$relimg\n\n";

    print "$book.mpcert : \$(PCDEPS_FOR_$mangle)\n\n";
}


print "ALL_PCERTS := \\\n";
foreach my $book (@deporder)
{
    print "    $book.mpcert \\\n";
}
print "\n\n";
