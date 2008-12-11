#!/usr/bin/perl

# This script scans for dependencies of some ACL2 .cert files.  To
# run, execute
# perl cert.pl book1.cert book2.cert ...
# More command line options are forthcoming.

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

my $use_pfiles = 1;
my $write_pfiles = 1;



# This sets the location of :dir :system as the directory where this script sits.
my %dirs = ( "SYSTEM" => dirname($0) );

my $local_dirs = 0;


my @targets = ();
my $jobs = 1;
my $clean_certs = 0;
my $no_build = 0;
my $clean_pfiles = 0;

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

   --no-use-pfiles
   -u
           Don\'t look at files with \".p\" extensions to obtain
           pre-cached dependency information.

   --no-write-pfiles
   -w
           Don\'t write out files with ".p" extensions containing
           cached dependency information.

   --clean-certs
   -cc
           Delete each certificate file encountered in the dependency
           search.  Warning: Unless the "-n"/"--no-build" flag is
           given, the script will then subsequently rebuild these
           files.

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

';
        exit 0;
    } elsif ($arg eq  "--jobs" || $arg eq "-j") {
	$jobs = shift @ARGV;
    } elsif ($arg eq "--no-use-pfiles" || $arg eq "-u") {
	$use_pfiles = 0;
    } elsif ($arg eq "--no-write-pfiles" || $arg eq "-w") {
	$write_pfiles = 0;
    } elsif ($arg eq "--clean-certs" || $arg eq "-cc") {
	$clean_certs = 1;
    } elsif ($arg eq "--no-build" || $arg eq "-n") {
	$no_build = 1;
    } elsif ($arg eq "--clean-pfiles" || $arg eq "-cp") {
	$clean_pfiles = 1;
    } elsif ($arg eq "--clean-all" || $arg eq "-c") {
        $clean_pfiles = $no_build = $clean_certs = 1;
        $write_pfiles = $use_pfiles = 0;
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
	    my $path = "$dirpath/$res[0].cert";
	    while ($path =~ s/( |\/)[^\/\:]*\/\.\.\//$1/g) {}
	    return $path;
	} else {
	    my $dir = dirname($base);
	    my $path = "$dir/$res[0].cert";
	    while ($path =~ s/( |\/)[^\/\:]*\/\.\.\//$1/g) {}
	    return $path;
	}
    }
    return 0;
}

# Possible more general way of recognizing a Lisp symbol:
# ((?:[^\\s\\\\|]|\\\\.|(?:\\|[^|]*\\|))*)
# - repeatedly matches either: a non-bar, non-backslash, non-whitespace character,
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
	    my $path = "$dirpath/$res[0]";
	    while ($path =~ s/( |\/)[^\/\:]*\/\.\.\//$1/g) {}
	    return $path;
	} else {
	    my $dir = dirname($base);
	    my $path = "$dir/$res[0]";
	    while ($path =~ s/( |\/)[^\/\:]*\/\.\.\//$1/g) {}
	    return $path;
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
	my $path = "$basedir/$res[1]";	
	while ($path =~ s/( |\/)[^\/\:]*\/\.\.\//$1/g) {}
	$local_dirs->{$name} = $path;
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
	if (-e ($dirname . "/cert_pl_exclude")) {
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
	    my $res = get_include_book($fname, $the_line);
	    if ($res) {
		push(@{$deps}, $res);
	    } else {
		$res = get_ld($fname, $the_line);
		if ($res) {
		    scan_ld($res, $deps);
		} else {
		    $res = get_add_dir($fname, $the_line);
		}
	    }
	}
	close($ld);
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

    if (-e $target && $clean_certs) {
	unlink($target);
    }

    my $base = $target;
    $base =~ s/\.cert$//;
    my $pfile = $base . ".p";
    my $lispfile = $base . ".lisp";

    # First check that the corresponding .lisp file exists.
    if (! -e $lispfile) {
	print "Error: Need $lispfile to build $target.\n";
	return;
    }

    $seen{$target} = [ $lispfile ];
    my $deps = $seen{$target};

    # If a corresponding .acl2 file exists or otherwise if a
    # cert.acl2 file exists in the directory, we need to scan that for dependencies as well.
    my $acl2file = $base . "acl2";
    if (! -e $acl2file) {
	$acl2file = dirname($base) . "/cert.acl2";
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
	open(my $lisp, "<", $lispfile);
	while (my $the_line = <$lisp>) {
	    my $res = get_include_book($base, $the_line);
	    if ($res) {
		push(@{$deps},$res);
	    }
	}
	close($lisp);

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
	# Read the dependencies from the pfile.
	open(my $p, "<", $pfile);
	while (my $the_line = <$p>) {
	    $the_line =~ s/\n$//;
	    push(@{$deps}, $the_line);
	}
	close($p);
    }
    
    foreach my $dep (@{$deps}) {
	add_deps($dep);
    }

    # If this needs an update, we're done, otherwise we need to delete
    # its entry in the dependency table. 
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

#    print "Done calculating dependencies for $target\n";
}

print "Starting dependency calculation\n";
foreach my $target (@targets) {
    $target =~ s/\.lisp$/.cert/;
    add_deps($target);
}


unless ($no_build) {
# Build the makefile and run make.
    open (my $mf, ">", "Makefile-tmp");
    print "Done adding dependencies\n";
    print $mf "
ACL2 := " . $ENV{"ACL2"} . "
include " . dirname($0) . "/make_cert
.PHONY: all

    all :
    ";
    while ((my $key, my $value) = each %seen) {
	if ($value) { 
#	print "Dependencies for $key:\n";
	    print $mf "all : $key\n";
	    my @the_deps = @{$value};
	    foreach my $dep (@the_deps) {
#	    print "$dep\n";
		print $mf "$key : $dep\n";
	    }
	}
    }
    close($mf);

    exec("make", "-j", $jobs, "-f", "Makefile-tmp");
}




