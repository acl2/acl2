#!/usr/bin/env perl

######################################################################
## NOTE.  This file is not part of the standard ACL2 books build
## process; it is part of an experimental build system that is not yet
## intended, for example, to be capable of running the whole
## regression.  The ACL2 developers do not maintain this file.
##
## Please contact Sol Swords <sswords@cs.utexas.edu> with any
## questions/comments.
######################################################################

# Copyright 2008 by Sol Swords.



#; This program is free software; you can redistribute it and/or modify
#; it under the terms of the GNU General Public License as published by
#; the Free Software Foundation; either version 2 of the License, or
#; (at your option) any later version.

#; This program is distributed in the hope that it will be useful,
#; but WITHOUT ANY WARRANTY; without even the implied warranty of
#; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#; GNU General Public License for more details.

#; You should have received a copy of the GNU General Public License
#; along with this program; if not, write to the Free Software
#; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.



# This script scans for dependencies of some ACL2 .cert files.
# Run "perl cert.pl -h" for usage.

# This script scans for include-book forms in the .lisp file
# corresponding to each .cert target and recursively maps out the
# dependencies of all files needed.  When it is finished, it writes
# out a file Makefile-tmp which can be used to make all the targets.

# This script assumes that the ACL2 system books directory is where it
# itself is located.  Therefore, if you call this script from a
# different directory, it should still be able to resolve ":dir
# :system" include-books.  It also scans the relevant .acl2 files for
# each book for add-include-book-dir commands.



use strict;
use warnings;
use File::Basename;

my %seen = ( );

my $use_pfiles = 0;
my $write_pfiles = 0;



sub rm_dotdots {
    my $path = shift;
    while ($path =~ s/( |\/)[^\/\.]+\/\.\.\//$1/g) {}
    return $path;
}

sub rel_path {
    my $base = shift;
    my $path = shift;
    if (substr($path,0,1) eq "/") {
	return $path;
    } else {
	return rm_dotdots("$base/$path");
    }
}

sub rec_readlink {
    my $file = shift;
    my $last = $file;
    my $dest;
    while ($dest = readlink $last) {
	$last = rel_path(dirname($last),$dest);
    }
    return $last;
}

# This sets the location of :dir :system as the directory where this
# script sits.
my $this_script = rec_readlink(substr(`which $0`, 0 ,-1));
my %dirs = ( "SYSTEM" => dirname($this_script) );
print "System dir is " . dirname($this_script) . "\n";
my $local_dirs = 0;


my @targets = ();
my $jobs = 1;
my $clean_certs = 0;
my $no_build = 0;
my $clean_pfiles = 0;
my $print_deps = 0;
my $no_makefile = 0;
my $mf_name = "Makefile-tmp";
my $all_deps = 0;

while (my $arg = shift(@ARGV)) {
    if ($arg eq "--help" || $arg eq "-h") {
	print '
cert.pl: Automatic dependency analysis for certifying ACL2 books.

Usage:
perl cert.pl <options, targets>

where targets are filenames of ACL2 files or certificates to be built
and options are as follows:

   --jobs <n>
   -j <n>
           Use n processes to build certificates in parallel.

   --use-pfiles
   -u
           Read files with \".p\" extensions to obtain pre-cached
           dependency information.


   --write-pfiles
   -w
           Write out files with ".p" extensions to cache dependency
           information.

   --all-deps
   -d
           Write out dependency information for all targets
           encountered, including ones which don\'t need updating.

   --clean-certs
   -cc
           Delete each certificate file and corresponding .out file
           encountered in the dependency search.  Warning: Unless the
           "-n"/"--no-build" flag is given, the script will then
           subsequently rebuild these files.

   --clean-pfiles
   -cp
           Delete each depencency cache ".p" file encountered.
           Implies "-u".  Warning 1:  Unless the "-w"/
           "--no-write-pfiles" flag is given, these will then be
           recreated.  Warning 2:  Unless the "-n"/ "--no-build" flag
           is given, the script will then go on to certify the books.

   --no-build
   -n
           Don\'t call make in order to certify the books; just run
           this script for "side effects" such as cleaning or
           generating dependency cache files.

   --clean-all
   -c
           Just clean up certificates and dependency cache files,
           don\'t generate new cache files or build certificates.
           Equivalent to "-n -w -cc -cp".

   -o <makefile-name>
           Determines where to write the dependency information;
           default is Makefile-tmp.

   --verbose-deps
   -v
           Print out dependency information as it\'s discovered.

   --makefile-only
   -m
           Write out a file Makefile-tmp containing the dependency
           graph, but don\'t run make.

   --static-makefile-mode <makefile-name>
   -s <makefile-name>
           Equivalent to -u -w -d -m -o <makefile-name>.  Useful for
           building a static makefile for your targets, which will
           suffice for certifying them as long as the dependencies
           between source files don\'t change.

';
	exit 0;
    } elsif ($arg eq  "--jobs" || $arg eq "-j") {
	$jobs = shift @ARGV;
    } elsif ($arg eq "--use-pfiles" || $arg eq "-u") {
	$use_pfiles = 1;
    } elsif ($arg eq "--write-pfiles" || $arg eq "-w") {
	$write_pfiles = 1;
    } elsif ($arg eq "--clean-certs" || $arg eq "-cc") {
	$clean_certs = 1;
    } elsif ($arg eq "--no-build" || $arg eq "-n") {
	$no_makefile = 1;
    } elsif ($arg eq "--clean-pfiles" || $arg eq "-cp") {
	$clean_pfiles = 1;
    } elsif ($arg eq "--clean-all" || $arg eq "-c") {
        $clean_pfiles = $no_makefile = $clean_certs = 1;
        $write_pfiles = $use_pfiles = 0;
    } elsif ($arg eq "--verbose-deps" || $arg eq "-v") {
	$print_deps = 1;
    } elsif ($arg eq "--makefile-only" || $arg eq "-m") {
	$no_build = 1;
    } elsif ($arg eq "-o") {
	$mf_name = shift @ARGV;
    } elsif ($arg eq "--all-deps" || $arg eq "-d") {
	$all_deps = 1;
    } elsif ($arg eq "--static-makefile-mode" || $arg eq "-s") {
	$mf_name = shift @ARGV;
	$use_pfiles = $write_pfiles = 0;
	$all_deps = $no_build = 1;
    } else {
	push(@targets, $arg);
    }
}



sub lookup_colon_dir {
    my $name = uc(shift);
    my $dirpath = ($local_dirs && $local_dirs->{$name})
	|| $dirs{$name} ;
    return $dirpath;
}

sub get_include_book {
    my $base = shift;
    my $the_line = shift;
    my $regexp = "^[^;]*\\(include-book[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	if ($res[1]) {
	    my $dirpath = lookup_colon_dir($res[1]);
	    unless ($dirpath) {
		print "Error: Unknown :dir entry $res[1] for $base\n";
		return 0;
	    }
	    return rel_path($dirpath, "$res[0].cert");
	} else {
	    my $dir = dirname($base);
	    return rel_path($dir, "$res[0].cert");
	}
    }
    return 0;
}

sub get_depends_on {
    my $base = shift;
    my $the_line = shift;
    my $regexp = "\\(depends-on[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	if ($res[1]) {
	    my $dirpath = lookup_colon_dir($res[1]);
	    unless ($dirpath) {
		print "Error: Unknown :dir entry $res[1] for $base\n";
		return 0;
	    }
	    return rel_path($dirpath, "$res[0]");
	} else {
	    my $dir = dirname($base);
	    return rel_path($dir, "$res[0]");
	}
    }
    return 0;
}


# Possible more general way of recognizing a Lisp symbol:
# ((?:[^\\s\\\\|]|\\\\.|(?:\\|[^|]*\\|))*)
# - repeatedly matches either: a non-pipe, non-backslash, non-whitespace character,
#                              a backslash and subsequently any character, or
#                              a pair of pipes with a series of intervening non-pipe characters.
# For now, stick with a dumber, less error-prone method.


sub get_ld {
    my $base = shift;
    my $the_line = shift;

    # Check for LD commands
    my $regexp = "^[^;]*\\(ld[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	if ($res[1]) {
	    my $dirpath = lookup_colon_dir($res[1]);
	    unless ($dirpath) {
		print "Error: Unknown :dir entry $res[1] for $base\n";
		return 0;
	    }
	    return rel_path($dirpath, $res[0]);
	} else {
	    my $dir = dirname($base);
	    return rel_path($dir, $res[0]);
	}
    }
    return 0;
}

sub get_add_dir {
    my $base = shift;
    my $the_line = shift;

    # Check for ADD-INCLUDE-BOOK-DIR commands
    my $regexp = "^[^;]*\\(add-include-book-dir[\\s]+:([^\\s]*)[\\s]*\"([^\"]*)\\/\"";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	$local_dirs = $local_dirs || {};
	my $name = uc($res[0]);
	my $basedir = dirname($base);
	$local_dirs->{$name} = rel_path($basedir, $res[1]);
    }
    return 0;
}


sub newer_than {
    my $file1 = shift;
    my $file2 = shift;
    return ((stat($file1))[9]) > ((stat($file2))[9]);
}

sub excludep {
    my $prev = shift;
    my $dirname = dirname($prev);
    while ($dirname ne $prev) {
	if (-e rel_path($dirname, "cert_pl_exclude")) {
	    return 1;
	}
	$prev = $dirname;
	$dirname = dirname($dirname);
    }
    return 0;
}

sub scan_ld {
    my $fname = shift;
    my $deps = shift;

    if ($fname) {
	push (@{$deps}, $fname);
	open(my $ld, "<", $fname);
	while (my $the_line = <$ld>) {
	    my $res = get_include_book($fname, $the_line) || get_depends_on($fname, $the_line);
	    if ($res) {
		push(@{$deps}, $res);
	    } else {
		$res = get_ld($fname, $the_line);
		if ($res) {
		    scan_ld($res, $deps);
		} else {
		    get_add_dir($fname, $the_line);
		}
	    }
	}
	close($ld);
    }
}

sub scan_book {
    my $fname = shift;
    my $deps = shift;

    if ($fname) {
	# Scan the lisp file for include-books.
	open(my $lisp, "<", $fname);
	while (my $the_line = <$lisp>) {
	    my $res = get_include_book($fname, $the_line) || get_depends_on($fname, $the_line);
	    if ($res) {
		push(@{$deps},$res);
	    }
	}
	close($lisp);
    }
}
    

sub add_deps {
    my $target = shift;

    if (exists $seen{$target}) {
	# We've already calculated this file's dependencies.
	return;
    }

    if ($target !~ /\.cert$/) {
	return;
    }

    if (excludep($target)) {
	return;
    }

    my $base = $target;
    $base =~ s/\.cert$//;
    my $pfile = $base . ".p";
    my $lispfile = $base . ".lisp";

    # Clean the cert and out files if we're cleaning.
    if ($clean_certs) {
	my $outfile = $base . ".out";
	unlink($target) if (-e $target);
	unlink($outfile) if (-e $outfile);
    }

    # First check that the corresponding .lisp file exists.
    if (! -e $lispfile) {
	print "Error: Need $lispfile to build $target.\n";
	return;
    }

    $seen{$target} = [ $lispfile ];
    my $deps = $seen{$target};

    # If a corresponding .acl2 file exists or otherwise if a
    # cert.acl2 file exists in the directory, we need to scan that for dependencies as well.
    my $acl2file = $base . ".acl2";
    if (! -e $acl2file) {
	$acl2file = rel_path(dirname($base), "cert.acl2");
	if (! -e $acl2file) {
	    $acl2file = 0;
	}
    }

    if (-e $pfile && $clean_pfiles) {
	unlink($pfile);
    }

    if ((! $use_pfiles) || (! -e $pfile) || (newer_than($lispfile, $pfile))
	|| ($acl2file && newer_than($acl2file, $pfile))) {
	# Recreate the pfile and calculate the deps.

	$local_dirs = 0;
	
	# Scan the .acl2 file first so that we get the add-include-book-dir
	# commands before the include-book commands.
	scan_ld($acl2file, $deps);

	# Scan the lisp file for include-books.
	scan_book($lispfile, $deps);

	$local_dirs = 0;
	
	if ($write_pfiles) {
	    # Print the dependencies to the pfile.
	    open (my $p, ">", $pfile);
	    foreach my $dep (@{$deps}) {
		print $p $dep . "\n";
	    }
	    close($p);
	}
    } else {

	# Read the dependencies from the pfile instead of regenerating them.
	open(my $p, "<", $pfile);
	while (my $the_line = <$p>) {
	    # Chop the newline off and add to deps.
	    push(@{$deps}, substr($the_line, 0, -1));
	}
	close($p);
    }

    if ($print_deps) {
	print "Dependencies for $target:\n";
	foreach my $dep (@{$deps}) {
	    print "$dep\n";
	}
	print "\n";
    }

    foreach my $dep (@{$deps}) {
	add_deps($dep);
    }

    # If there is an .image file corresponding to this file or a
    # cert.image in this file's directory, add a dependency on the
    # ACL2 image specified in that file.
    my $imagefile = $base . ".image";
    if (! -e $imagefile) {
	$imagefile = rel_path(dirname($base), "cert.image");
	if (! -e $imagefile) {
	    $imagefile = 0;
	}
    }
    if ($imagefile) {
	open(my $im, "<", $imagefile);
	my $line = <$im>;
	if ($line) {
	    if (substr($line,-1,1) eq "\n") {
		chop $line;
	    }
	    my $image = rel_path(dirname($base), $line);
	    if (! -e $image) {
		$image = substr(`which $line`,0,-1);
	    }
	    if (-e $image) {
		push(@{$deps}, rec_readlink($image));
	    }
	}
    }
    

    # If this target needs an update or we're in all_deps mode, we're
    # done, otherwise we'll delete its entry in the dependency table.
    unless ($all_deps) {
	my $needs_update = (! -e $target);
	if (! $needs_update) {
	    foreach my $dep (@{$deps}) {
		if ((-e $dep && newer_than($dep, $target)) || $seen{$dep}) {
		    $needs_update = 1;
		    last;
		}
	    }
	}
	if (! $needs_update) {
	    $seen{$target} = 0;
	}
    }

}

foreach my $target (@targets) {
    $target =~ s/\.lisp$/.cert/;
    add_deps($target);
}


unless ($no_makefile) {
    my $acl2 = $ENV{"ACL2"};
    unless ($acl2) {
	## die "Error: Shell variable ACL2 should be set for this to work correctly.\n";
	print "ACL2 defaults to acl2\n";
	$acl2 = "acl2";
    }
    # Build the makefile and run make.
    open (my $mf, ">", $mf_name) or die "Failed to open output file $mf_name\n";
    print $mf '
ACL2 := ' . $acl2 . '
include ' . rel_path(dirname($this_script), "make_cert") . '
.PHONY: all
all:
';
    while ((my $key, my $value) = each %seen) {
	if ($value) { 
	    print $mf "all : $key\n";
	    my @the_deps = @{$value};
	    foreach my $dep (@the_deps) {
		print $mf "$key : $dep\n";
	    }
	}
    }
    close($mf);
    
    unless ($no_build) {
	exec("make", "-j", $jobs, "-f", $mf_name);
    }
}




