#!/usr/bin/env perl

# cert.pl build system
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
# Original authors: Sol Swords <sswords@centtech.com>
#                   Jared Davis <jared@centtech.com>

# clean.pl -- clean up targets from cert.pl

use strict;
use warnings;
use File::Find;
use File::Spec;
use Getopt::Long qw(:config bundling_override);

my $dryrun = 0;

my $helpstr = 'clean.pl: clean up generated files from running cert.pl

This script removes temporary files like foo.cert, foo.cert.out, foo.time,
etc., which arise from certifying ACL2 books with cert.pl or similar.

The cleaning is done in:
  - your current directory, and
  - all subdirectories of the current directory, recursively.

Usage: clean.pl [OPTIONS]

Options:

    -h          Show this help message and exit immediately
    --help

    --dryrun    Print what will be deleted, but do NOT actually delete
                any files.

';

GetOptions ("help|h" => sub { print $helpstr; exit 0 ; },
	    "dryrun" => \$dryrun
    );

# General idea: @rm is an accumulator for files we are going to remove.  We're
# going to put a bunch of stuff into @rm, then remove them all at once with
# unlink.

my @rm;


# We will unconditionally delete every file that ends with one of the following
# extensions.  We think this is safe because these extensions shouldn't be used
# for anything other than generated ACL2/Lisp stuff.  It's nicer to delete ANY
# files of these extensions, rather than just files corresponding to books, so
# that if you delete books after certifying them, etc., the generated files
# still get cleaned up.

my %delete_extensions = (
    ".out"     => 1, # Output log from certification
    ".cert"    => 1, # ACL2 certificate
    ".pcert1"  => 1, # ACL2 provisional certificate
    ".pcert0"  => 1, # ACL2 provisional certificate
    ".acl2x"   => 1, # ACL2 expansion file (for two-pass certification)
    ".port"    => 1, # ACL2 portcullis file (for two-pass certification)?
    ".time"    => 1, # Time stamp file from certification
    ".o"       => 1, # Compiled files from GCL
    ".bin"     => 1, # ???
    ".sbin"    => 1, # ???
    ".lbin"    => 1, # ???
    ".fasl"    => 1, # Compiled Lisp files for SBCL
    ".ufsl"    => 1, # ???
    ".64ufasl" => 1, # ???
    ".pfsl"    => 1, # ???
    ".dfsl"    => 1, # ???
    ".d64fsl"  => 1, # Compiled Lisp file for CCL/Darwin_64
    ".dx32fsl" => 1, # Compiled Lisp file for CCL/Darwin_x86_32
    ".dx64fsl" => 1, # Compiled Lisp file for CCL/Darwin_x86_64
    ".lx32fsl" => 1, # Compiled Lisp file for CCL/Linux_x86_32
    ".lx64fsl" => 1, # Compiled Lisp file for CCL/Linux_x86_64
    ".fx32fsl" => 1, # Compiled Lisp file for CCL/FreeBSD_x86_32
    ".fx64fsl" => 1, # Compiled Lisp file for CCL/FreeBSD_x86_64
    ".wx32fsl" => 1, # Compiled Lisp file for CCL/Windows_x86_32
    ".wx64fsl" => 1, # Compiled Lisp file for CCL/Windows_x86_64
    ".sparcf"  => 1, # ???
    ".axpf"    => 1, # ???
    ".x86f"    => 1, # ???
    ".ppcf"    => 1, # ???
    ".fas"     => 1, # ???
    ".lib"     => 1, # ???
    ".sse2f"   => 1  # ???
    );

my %keep_extensions = (
    ".lisp" => 1,
    ".acl2" => 1,
    # Not .lsp because sometimes there are temp-emacs-file.lsp or
    # @expansion.lsp files to remove
);


# Main scan for files with the above extensions:

sub consider_file
{
    my $what = $_;
    my $lastdot = rindex($what, '.');
    my $ext = substr($what, $lastdot);

    if ($keep_extensions{$ext})
    {
	# Obviously we want to keep it, just stop now.
	return;
    }

    if (! -f $what)
    {
	# Not even a regular file, don't do anything.
	return;
    }

    if ($delete_extensions{$ext})
    {
	# Definitely want to get rid of it
	push(@rm, $what);
	return;
    }

    if ($ext eq ".c" || $ext eq ".h")
    {
	# Hack.  GCL ends up generating .h and .c files that sometimes get left
	# behind.  We definitely don't want to delete all .c and .h files, so
	# try to only delete these if they seem safe to delete.

	# BOZO is this a good solution?  Are GCL temp files always named
	# gazonk somethingorother?

	if ($what =~ /gazonk/) {
	    push(@rm, $what);
	}
	return;
    }

    # There are a few more files we may want to remove.
    my ($vol,$dirs,$file) = File::Spec->splitpath($what);

    if ($ext eq ".lsp")
    {
	if ($file eq "temp-emacs-file.lsp") {
	    push(@rm, $what);
	}
	elsif ($file =~ /^(.*)\@expansion.lsp/) {
	    push(@rm, $what);
	}
	return;
    }

    if ($file eq "Makefile-tmp") {
	push(@rm, $what);
	return;
    }

    if ($file eq "Makefile-deps") {
	push(@rm, $what);
	return;
    }

    if ($file eq "worklispext") {
	# Generated by ACL2 during save-exec, see Issue 305.
	push(@rm, $what);
	return;
    }

    if ($file =~ /^workxxx.*$/) {
	push(@rm, $what);
	return;
    }

    if ($file =~ /^TMP/) {
	push(@rm, $what);
	return;
    }

    if ($ext eq ".wrap" && $file =~ /^startjob./) {
	# Centaur specific thing, delete startjob*.wrap
	push(@rm, $what);
	return;
    }
}

print "clean.pl: scanning for generated files\n";
my $start = time();
find({ wanted => \&consider_file, no_chdir => 1 }, ".");
my $end = time();
my $elapsed = $end - $start;
my $numfiles = @rm;
print "clean.pl: found $numfiles targets ($elapsed seconds)\n";

if ($dryrun) {
    print "clean.pl: not deleting anything due to --dryrun\n";
    print "clean.pl: would have deleted:\n";
    foreach(@rm) { print "  $_\n"; }
    print "\n";
    exit(0);
}
else {
    $start = time();
    my $numremoved = unlink(@rm);
    $end = time();
    $elapsed = $end - $start;
    print "clean.pl: deleted $numremoved files ($elapsed seconds)\n";
}

exit(0);


