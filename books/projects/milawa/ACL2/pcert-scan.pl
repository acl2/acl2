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
