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
use Storable;
use FindBin qw($RealBin);
use Getopt::Long qw(:config bundling_override);

(do "$RealBin/certlib.pl") or die ("Error loading $RealBin/certlib.pl:\n!: $!\n\@: $@\n");

# use lib "/usr/lib64/perl5/5.8.8/x86_64-linux-thread-multi/Devel";
# use Devel::DProf;

my @orig_cmd_line_args = ();
push (@orig_cmd_line_args, @ARGV);

my $base_path = 0;

my @user_targets = ();
my $jobs = 1;
my $no_build = 0;
my $no_makefile = 0;
my $no_boilerplate = 0;
my $mf_name = "Makefile-tmp";
my @includes = ();
my @include_afters = ();
my $svn_mode = 0;
my $quiet = 0;
my @run_sources = ();
my $make = $ENV{"MAKE"} || "make";
my @make_args = ();
my $acl2 = $ENV{"ACL2"};
my $acl2_books = $ENV{"ACL2_SYSTEM_BOOKS"};
my $keep_going = 0;
my $var_prefix = "CERT_PL";
my %certlib_opts = ( "debugging" => 0,
		     "clean_certs" => 0,
		     "print_deps" => 0,
		     "all_deps" => 0,
                     "believe_cache" => 0 );
my $cache_file = 0;
my $bin_dir;

$base_path = abs_canonical_path(".");

my $summary_str = "\ncert.pl: Automatic dependency analysis for certifying ACL2 books.\n";


my $helpstr = '
Usage:
perl cert.pl <options, targets>

where targets are filenames of ACL2 files or certificates to be built
and options are as listed below.  Cert.pl scans the filenames for
dependencies and recursively scans their dependencies as well.
It then (optionally) builds a makefile and (optionally) runs it so as
to certify the named targets.

Cert.pl begins computing the dependencies for a book by ensuring that
its .lisp file exists.  It then looks for either a corresponding .acl2
file or a cert.acl2 file in its directory and scans that if it finds
one, treating dependencies found in that scan as dependencies of the
book.  It recognizes LD forms in these .acl2 files and scans the
loaded files as well.  When that is finished, it scans the book
itself.

Cert.pl recognize several kinds of forms as producing or affecting
dependencies.  All such forms must be contained on a single line or
cert.pl will not recognize them.  As such, if you want to hide, say,
an include-book from cert.pl, you may insert a line break somewhere
inside it.  Certain forms will also be ignored if they occur after a
semicolon on the same line (a Lisp comment); the exceptions are noted.
The following forms are recognized:

 - (include-book "<bookname>" [:dir :<dirname>])
     Adds the included book\'s :cert file as a dependency of the
current book.

 - (add-include-book-dir :<dirname> "<dirpath>")
     Registers an association between the given dirname and dirpath so
that we may correctly decode include-book and other forms with :dir
:<dirname>.

 - (depends-on "<filename>" [:dir :<dirname>])
     Adds the named file as a dependency of the current book.  May
occur in a comment, since depends-on is not defined in ACL2.

 - (loads "<filename>" [:dir :<dirname>])
     Adds the named file as a dependency of the current book, and also
recursively scans that file for dependencies as if it were part of the
current file.  May occur in a comment, since it is not defined in
ACL2.

 - (ld "<filename>" [:dir :<dirname>])
     Ignored when it occurs while scanning the main book, as opposed
to an .acl2 file or a file recursively LD\'d by an .acl2 file, this
causes cert.pl to recursively scan the LD\'d file for dependencies as
if it were part of the current file.

 - ;; two-pass certification
     If this line occurs in the file, it means that the current book
is intended to be certified in two passes.  The dependencies computed
for the current book are thus not dependencies of the .cert file, but
of the .acl2x file, and the .acl2x file is the only dependency of the
cert file.

See files make-targets and regression-targets for example uses of
cert.pl.

An advanced feature of cert.pl is the ability to set up Make variables
that contain the recursive dependencies of certain sources.  For example,

 cert.pl -s my_mkfile  AB: a.cert b.cert CDE: c.cert e.cert d.cert

creates a makefile, my_mkfile, that (in addition to containing the
usual dependency graph, defines variables AB_SOURCES, AB_CERTS,
CDE_SOURCES, and CDE_CERTS.  AB_SOURCES contains all non-cert files
that a.cert and b.cert recursively depend on, AB_CERTS contains all
cert files they depend on, and similarly for CDE_SOURCES and
CDE_CERTS.  This is sometimes useful in case you wish to set up a
makefile with several distinct targets that depend on overlapping sets
of books.

OPTIONS:

   --help
   -h
           Display this help and exit.

   --jobs <n>
   -j <n>
           Use n processes to build certificates in parallel.

   --all-deps
   -d
           Write out dependency information for all targets
           encountered, including ones which don\'t need updating.

   --acl2 <cmd>
   -a <cmd>
           Use <cmd> as the ACL2 executable, overriding the ACL2
           environment variable and the location of an executable
           named \"acl2\" in the PATH.

   --acl2-books <dir>
   -b <dir>
           Use <dir> as the ACL2 system books directory, overriding
           the ACL2_SYSTEM_BOOKS environment variable, the location of
           acl2 in the PATH, and the location of this script.

   --clean-certs
   --cc
           Delete each certificate file and corresponding .out and
           .time file encountered in the dependency search.  Warning:
           Unless the "-n"/"--no-build" flag is given, the script will
           then subsequently rebuild these files.

   --no-build
   -n
           Don\'t create a makefile or call make; just run this script
           for "side effects" such as cleaning or generating
           dependency cache files.

   --clean-all
   -c
           Just clean up certificates and dependency cache files,
           don\'t generate new cache files or build certificates.
           Equivalent to "-n -cc".

   -o <makefile-name>
           Determines where to write the dependency information;
           default is Makefile-tmp.

   --verbose-deps
   -v
           Print out dependency information as it\'s discovered.

   --makefile-only
   -m
           Don\'t run make after running the dependency analysis.

   --static-makefile <makefile-name>
   -s <makefile-name>
           Equivalent to -d -m -o <makefile-name>.  Useful for
           building a static makefile for your targets, which will
           suffice for certifying them as long as the dependencies
           between source files don\'t change.

   --no-boilerplate
           Omit from the makefile the inclusion of make_cert, which
           provides the rule for building a certificate, and the
           settings of the ACL2 and ACL2_SYSTEM_BOOKS variables.  This
           will create a makefile containing the list of certificates
           and dependencies between them and the sources, suitable for
           including in another makefile.

   --var-prefix <name>
           By default, cert.pl will write a makefile containing
           settings of the variables CERT_PL_SOURCES and
           CERT_PL_CERTS.  If this flag is provided, then the
           variables are named <name>_SOURCES and <name>_CERTS
           instead.  This is useful for situations in which an outer
           makefile includes more than one makefile generated by
           cert.pl.

   --include <makefile-name>
   -i <makefile-name>
           Include the specified makefile via an include command in
           the makefile produced.  Multiple -i arguments may be given
           to include multiple makefiles.  The include commands occur
           before the dependencies in the makefile.

   --include-after <makefile-name>
   -ia <makefile-name>
           Include the specified makefile via an include command in
           the makefile produced.  Multiple -ia arguments may be given
           to include multiple makefiles.  The include commands occur
           after the dependencies in the makefile.

   --relative-paths <dir>
   -r <dir>
           Use paths relative to the given directory rather than
           the current directory.

   --targets <file>
   -t <file>
           Add as targets the files listed in <file>.  Whitespace is
           ignored, # comments out the rest of a line, and filenames
           are listed one per line.

   --deps-of <file>
   -p <file>
           Add as targets the dependencies of file.  That is, file is
           not itself added as a target, but anything necessary for
           its certification will be.


   --quiet
   -q
           Don\'t print any asides except for errors and output from
           --source-cmd commands.

   --debug
           Print some debugging info as the program runs.

   --source-cmd <command-str>
           Run the following command on each source file.  The actual
           command line is created by replacing the string {} with the
           target file in the command string.  For example:
               cert.pl top.lisp -n -d --source-cmd "echo {}; wc {}"
           Any number of --source-cmd directives may be given; the
           commands will then be run in the order in which they are given.

   --tags-file <tagfile>
           Create an Emacs tags file containing the tags for all
           source files.  Equivalent to
           --source-cmd "etags -a -o tagfile {}".

   --svn-status
           Traverse the dependency tree and run "svn status" on each
           source file in the tree.  Equivalent to
           --source-cmd "svn status --no-ignore {}".

   --make-args <arg>
           Add command line arguments to make.  Multiple such
           directives may be given.

   --keep-going
   -k
           Passes the -k/--keep-going flag to make, which causes it to
           build as many targets as possible even after an error. Same
           as "--make-args -k".

   --bin <directory>

          Sets the location for ACL2 image files.  Cert.pl supports
          the use of different ACL2 images to certify different books.
          If for a book named foo.lisp either a file foo.image or
          cert.image exists in the same directory, then cert.pl reads
          a line from that file and takes that line to be the name of
          the image to use.  The default is \"acl2\".  If the image
          name is not \"acl2\" and a --bin directory is set, then
          cert.pl adds a foo.cert dependency on
          <bin_dir>/<image_name>, and uses <bin_dir>/<image_name> to
          certify the book.  Otherwise, no additional dependency is
          set, and at certification time we look for the image in the
          user\'s PATH.

';

GetOptions ("help|h"               => sub { print $summary_str;
					    print $helpstr;
					    exit 0 ; },
	    "jobs|j=i"             => \$jobs,
	    "clean-certs|cc"       => \$certlib_opts{"clean_certs"},
	    "no-build|n"           => \$no_makefile,
	    "clean-all|c"          => sub {$no_makefile = 1;
					   $certlib_opts{"clean_certs"} = 1;},
	    "verbose-deps|v"       => \$certlib_opts{"print_deps"},
	    "makefile-only|m"      => \$no_build,
	    "no-boilerplate"       => \$no_boilerplate,
	    "var-prefix=s"         => \$var_prefix,
	    "o=s"                  => \$mf_name,
	    "all-deps|d"           => \$certlib_opts{"all_deps"},
	    "static-makefile|s=s"  => sub {shift;
					   $mf_name = shift;
					   $certlib_opts{"all_deps"} = 1;
					   $no_build = 1;},
	    "acl2|a=s"             => \$acl2,
	    "acl2-books|b=s"       => \$acl2_books,
	    "bin=s"                => \$bin_dir,
	    "include|i=s"          => sub {shift;
					   push(@includes, shift);},
	    "include-after|ia=s"     => sub {shift;
					     push(@include_afters,
						  shift);},
	    "relative-paths|r=s"   => sub {shift;
					   $base_path =
					       abs_canonical_path(shift);},
	    "svn-status"           => sub {push (@run_sources,
						 sub { my $target = shift;
						       print `svn status --no-ignore $target`;
						   })},
	    "tags-file=s"          => sub { shift;
					    my $tagfile = shift;
					    push (@run_sources,
						  sub { my $target = shift;
							print `etags -a -o $tagfile $target`;})},
	    "source-cmd=s"         => sub { shift;
					    my $cmd = shift;
					    push (@run_sources,
						  sub { my $target = shift;
							my $line = $cmd;
							$line =~ s/{}/$target/g;
							print `$line`;})},
	    "quiet|q"              => \$quiet,
	    "make-args=s"          => \@make_args,
            "keep-going|k"         => \$keep_going,
	    "targets|t=s"          => sub { shift;
					    read_targets(shift, \@user_targets);
					},
	    "debug"                => \$certlib_opts{"debugging"},
	    # Note: this doesn't do anything yet.
	    "cache|h=s"            => \$cache_file,
	    "accept-cache"         => \$certlib_opts{"believe_cache"},
	    "deps-of|p=s"          => sub { shift; push(@user_targets, "-p " . shift); },
	    "<>"                   => sub { push(@user_targets, shift); }
	    );

sub remove_trailing_slash {
    my $dir = shift;
    return ( substr($dir,-1) eq "/" && $dir ne "/" )
	? substr($dir,0,-1) : $dir;
}
# Remove trailing slash from bin_dir, if any
$bin_dir = $bin_dir && canonical_path(remove_trailing_slash($bin_dir));

certlib_set_opts(\%certlib_opts);

my $cache;
if ($cache_file && -e $cache_file) {
    $cache = retrieve($cache_file);
} else {
    $cache = {};
}

# If $acl2_books is still not set, then:
# - set it based on the location of acl2 in the path, if available
# - otherwise set it to the directory containing this script.

unless ($acl2) {
    $acl2 = "acl2";
}

$acl2 = which($acl2);

if ($acl2) {
    $acl2 = abs_canonical_path($acl2);
    unless($quiet || $no_build) {
	print "ACL2 executable is ${acl2}\n";
    }
    $ENV{"ACL2"} = $acl2;
} else {
    unless ($quiet || $no_build) {
	print
"ACL2 executable not found.  Please specify with --acl2 command line
flag or ACL2 environment variable.\n";
    }
}

if (! $acl2_books) {
    if ($acl2) {
	$acl2_books = rel_path(dirname($acl2), "books");
    } else {
	$acl2_books = $RealBin;
    }
}
$acl2_books = abs_canonical_path($acl2_books);
unless($quiet) {
    print "System books directory is ${acl2_books}\n";
}

certlib_add_dir("SYSTEM", $acl2_books);
# In case we're going to run Make, set the ACL2_SYSTEM_BOOKS
# and ACL2 environment variables to match our assumption.
$ENV{"ACL2_SYSTEM_BOOKS"} = $acl2_books;


my %tscache = ();

my ($targets_ref, $labels_ref) = process_labels_and_targets(\@user_targets, $cache, \%tscache);
my @targets = @$targets_ref;
my %labels = %$labels_ref;

my %depmap = ( );



unless (@targets) {
    print "\nError: No targets provided.\n";
    print $helpstr;
    exit 1;
}

my %sourcehash = ( );

foreach my $target (@targets) {
    add_deps($target, $cache, \%depmap, \%sourcehash, \%tscache, 0);
}

$cache_file && store($cache, $cache_file);

my @sources = sort(keys %sourcehash);

# Is this how we want to nest these?  Pick a command, run it on
# every source file, versus pick a source file, run every command?
# This way seems more flexible; commands can be grouped together.
foreach my $run (@run_sources) {
    foreach my $source (@sources) {
	&$run($source);
    }
}

my $mf_intro_string = '
# Cert.pl is a build system for ACL2 books.  The cert.pl executable is
# located under your ACL2_SYSTEM_BOOKS directory; run "cert.pl -h" for
# usage options.


';

unless ($no_makefile) {
    # Build the makefile and run make.
    open (my $mf, ">", $mf_name)
	or die "Failed to open output file $mf_name\n";

    print $mf "\n# This makefile was generated by running:\n# cert.pl";
    foreach my $arg (@orig_cmd_line_args) {
	print $mf " $arg";
    }
    print $mf "\n";
    print $mf $mf_intro_string;

    unless ($no_boilerplate) {
	print $mf "ACL2_SYSTEM_BOOKS ?= " . canonical_path($RealBin) . "\n";
	if ($bin_dir) {
	    print $mf "export ACL2_BIN_DIR := ${bin_dir}\n";
	}
	print $mf "include \$(ACL2_SYSTEM_BOOKS)/make_cert\n\n";
    }

    foreach my $incl (@includes) {
	print $mf "\ninclude $incl\n";
    }

    print $mf "\n.PHONY: all-cert-pl-certs\n\n";
    print $mf "# Depends on all certificate files.\n";
    print $mf "all-cert-pl-certs:\n\n";
    
    # declare $var_prefix_CERTS to be the list of certificates
    print $mf $var_prefix . "_CERTS :=";

    my @certs = keys %depmap;
    @certs = sort(@certs);

    foreach my $cert (@certs) {
	print $mf " \\\n     $cert";
	if (cert_is_two_pass($cert, \%depmap)) {
	    my $acl2xfile = cert_to_acl2x($cert);
	    print $mf " \\\n     $acl2xfile";	    
	}
    }

    print $mf "\n\n";

    print $mf "ifneq (\$(ACL2_PCERT),)\n\n";
    print $mf "${var_prefix}_CERTS := \$(${var_prefix}_CERTS)";
    foreach my $cert (@certs) {
	if ($cert =~ /\.cert$/) {
	    my $base = $cert;
	    $base =~ s/\.cert$//;
	    print $mf " \\\n     $base.pcert";
	    print $mf " \\\n     $base.acl2x";
	}
    }
    print $mf "\n\nendif\n";
	

    print $mf "all-cert-pl-certs: \$(" . $var_prefix . "_CERTS)\n\n";

    # declare $var_prefix_SOURCES to be the list of sources
    print $mf $var_prefix . "_SOURCES :=";
    foreach my $source (@sources) {
	print $mf " \\\n     $source ";
    }
    print $mf "\n\n";

    # If there are labels, write out the sources and certs for those
    foreach my $label (sort(keys %labels)) {
	my @topcerts = @{$labels{$label}};
	my @labelcerts = ();
	my @labelsources = ();
	my %visited = ();
	# print "Processing label: $label\n";
	foreach my $topcert (@topcerts) {
	    # print "Visiting $topcert\n";
	    deps_dfs($topcert, \%depmap, \%visited, \@labelsources, \@labelcerts);
	}
	@labelcerts = sort(@labelcerts);
	@labelsources = sort(@labelsources);
	print $mf "${label}_CERTS :=";
	foreach my $cert (@labelcerts) {
	    print $mf " \\\n     $cert";
	    if (cert_is_two_pass($cert, \%depmap)) {
		my $acl2x = cert_to_acl2x($cert);
		print $mf " \\\n     $acl2x";
	    }
	}
	print $mf "\n\n";
	print $mf "ifneq (\$(ACL2_PCERT),)\n\n";
	print $mf "${label}_CERTS := \$(${label}_CERTS)";
	foreach my $cert (@labelcerts) {
	    my $base = $cert;
	    $base =~ s/\.cert$//;
	    print $mf " \\\n     $base.pcert";
	    print $mf " \\\n     $base.acl2x";
	}
	print $mf "\n\nendif\n";

	print $mf "${label}_SOURCES :=";
	foreach my $source (@labelsources) {
	    print $mf " \\\n     $source";
	}
	print $mf "\n\n";
    }

    # write out the dependencies
    foreach my $cert (@certs) {
	my $certdeps = cert_deps($cert, \%depmap);
	my $srcdeps = cert_srcdeps($cert, \%depmap);
	my $image = cert_image($cert, \%depmap);
	if (cert_is_two_pass($cert, \%depmap)) {
	    my $acl2xfile = cert_to_acl2x($cert);
#     This would be a nice way to do things, but unfortunately the "private"
#     keyword for target-specific variables was introduced in GNU Make 3.82,
#     which isn't widely used yet --
#	    print $mf "$cert : private TWO_PASS := 1\n";
#     Instead, sadly, we'll individually set the TWO_PASS variable for
#     each target instead.  (Note the ELSE case below.)
	    print $mf "$cert : TWO_PASS = 1\n";
	    print $mf "$cert :";
	    print $mf " \\\n     $acl2xfile";
	    print $mf "\n\n";
	    print $mf "$acl2xfile :";
	} else {
	    print $mf "$cert : TWO_PASS = \n";
	    print $mf "$cert :";
	}
	foreach my $dep (@$certdeps, @$srcdeps) {
	    print $mf " \\\n     $dep";
	}
	if ($image && ($image ne "acl2")) {
	    if ($bin_dir) {
		$image = rel_path($bin_dir, $image);
		print $mf " \\\n     $image";
	    } else {
		print "Warning: no --bin set, so not adding image dependencies,\n";
		print " e.g.   $cert : $image\n";
	    }
	}

	print $mf "\n\n";
    }

    # Write dependencies for pcert mode.
    print $mf "ifneq (\$(ACL2_PCERT),)\n\n";
    print $mf "# Dependencies for .pcert files:\n";
    print $mf "# (each .pcert depends on its corresponding .acl2x)\n\n";
    
    foreach my $cert (@certs) {
	my $base = $cert;
	$base =~ s/\.cert$//;
	print $mf "$base.pcert : $base.acl2x\n";
    }

    print $mf "\n# Dependencies for .acl2x files:\n";
    print $mf "# (similar to those for .cert files)\n";

    foreach my $cert (@certs) {
	my $certdeps = cert_deps($cert, \%depmap);
	my $srcdeps = cert_srcdeps($cert, \%depmap);
	my $image = cert_image($cert, \%depmap);
	(my $base = $cert) =~ s/\.cert$//;
	if (cert_is_two_pass($cert, \%depmap)) {
	    print $mf "$base.acl2x : TWO_PASS = 1\n";
	} else {
	    print $mf "$base.acl2x : TWO_PASS = \n";
	}
	print $mf "$base.acl2x :";
	foreach my $dep (@$certdeps) {
	    my $acl2x = cert_to_acl2x($dep);
	    print $mf " \\\n     $acl2x";
	}
	foreach my $dep (@$srcdeps) {
	    print $mf " \\\n     $dep";
	}
	if ($image && ($image ne "acl2")) {
	    if ($bin_dir) {
		$image = rel_path($bin_dir, $image);
		print $mf " \\\n     $image";
	    } else {
		print "Warning: no --bin set, so not adding image dependencies,\n";
		print " e.g.   $cert : $image\n";
	    }
	}
	print $mf "\n\n";
    }

    print $mf "# Dependencies for converting .pcert to .cert files:\n";
    print $mf "# (Each cert file depends on its pcert.)\n";
    
    foreach my $cert (@certs) {
	my $base = $cert;
	$base =~ s/\.cert$//;
	print $mf "$cert : $base.pcert\n";
    }
    print $mf "\nendif\n\n";


    foreach my $incl (@include_afters) {
	print $mf "\ninclude $incl\n";
    }

    close($mf);
    
    unless ($no_build) {
	my $make_cmd = join(' ', (("$make -j $jobs -f $mf_name"
				   . ($keep_going ? " -k" : "")),
				  @make_args));
	if ($certlib_opts{"debugging"}) {
	    print "$make_cmd\n";
	}
	exec $make_cmd;
    }
}

# print_times_seen();


