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
use FindBin qw($RealBin);
use Getopt::Long qw(:config bundling_override);

(do "$RealBin/certlib.pl") or die ("Error loading $RealBin/certlib.pl:\n!: $!\n\@: $@\n");
(do "$RealBin/paths.pl") or die ("Error loading $RealBin/paths.pl:\n!: $!\n\@: $@\n");

my %reqparams = ("hons-only" => "HONS_ONLY",
		 "uses-glucose" => "USES_GLUCOSE",
		 "uses-quicklisp" => "USES_QUICKLISP",
		 "ansi-only" =>  "ANSI_ONLY",
		 "uses-acl2r" => "USES_ACL2R",
		 "non-acl2r" => "NON_ACL2R",
		 "ccl-only" => "CCL_ONLY",
    );

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
		     "all_deps" => 1,
                     "believe_cache" => 0 );
my $cache_file = 0;
my $bin_dir = $ENV{'CERT_PL_BIN_DIR'};
my $params_file = 0;
# Remove trailing slash from and canonicalize bin_dir
if ($bin_dir) {
    my $cbin_dir = canonical_path(remove_trailing_slash($bin_dir));
    if (! $cbin_dir) {
	die("Fatal: bad path in environment var CERT_PL_BIN_DIR=$bin_dir");
    }
    $bin_dir = $cbin_dir;
}


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

DEPENDENCY SCAN

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

 - ;; cert_param: (<paramname>[=<paramval>])
     Cert_param directives control various things about how the file
gets certified, such as whether it uses provisional certification
(pcert), acl2x expansion (acl2x), and skip-proofs during acl2x
expansion (acl2xskip).

See files make-targets and regression-targets for example uses of
cert.pl.

SPECIAL MAKEFILE VARIABLES

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

CERT_PL_EXCLUDE FILES

Cert.pl can be prevented from exploring a directory (recursively) by
creating a file called "cert_pl_exclude".  Any book found to be
under a directory containing that file will not be scanned for
dependencies and won\'t have any dependencies added for it.  However,
only certain directories are searched, depending on where the book is
relative to where cert.pl is invoked.  To illustrate:

(1) If cert.pl reaches a book whose relative path is foo/bar/baz.lisp,
then it will skip the dependency scan if any of the following exist:
  ./cert_pl_exclude
  foo/cert_pl_exclude
  foo/bar/cert_pl_exclude
but not:
  ../cert_pl_exclude.

(2) If cert.pl reaches a book whose relative path is
../../foo/bar/baz.lisp, then it will skip the dependency scan if any
of the following exist:
  ../../cert_pl_exclude
  ../../foo/cert_pl_exclude
  ../../foo/bar/cert_pl_exclude
but not:
  ./cert_pl_exclude
  ../cert_pl_exclude
  ../../../cert_pl_exclude.


COMMAND LINE OPTIONS

   --help
   -h
           Display this help and exit.

   --jobs <n>
   -j <n>
           Use n processes to build certificates in parallel.

   --all-deps
   -d
           Toggles writing out dependency information for all targets
           encountered, including ones which don\'t need updating.  This is
           done by default, so using -d or --all-deps actually means that
           only targets that need updating are written to the makefile.

   --acl2 <cmd>
   -a <cmd>
           Use <cmd> as the ACL2 executable, overriding the ACL2
           environment variable and the location of an executable
           named "acl2" in the PATH.

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
           Equivalent to -m -o <makefile-name>.  Useful for
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
               cert.pl top.lisp -n --source-cmd "echo {}; wc {}"
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
          the image to use.  The default is "acl2".  If the image
          name is not "acl2" and a --bin directory is set, then
          cert.pl adds a foo.cert dependency on
          <bin_dir>/<image_name>, and uses <bin_dir>/<image_name> to
          certify the book.  Otherwise, no additional dependency is
          set, and at certification time we look for the image in the
          user\'s PATH.

   --params <filename>
          Specifies a file that contains lines like:
             mybook.cert:  pcert = 1, acl2x = 0
          with the grammar:
             <bookname>.cert: <param> = <val> [ , <param> = <val> ]*
          The parameters specified have the same meaning as cert_param
          directives in the books themselves, and if the same parameter
          is assigned in the book and in the params file, the params
          file takes precedence.

   --cache <filename>
          Specifies a file to use as a sourcefile events cache.  Such
          a file records events such as include-book, cert-param,
          etc., that are present in each source file.  When this
          option is given, cached information is read from that file
          if it is present, and updated information is written to it
          when we are done.  Using a cache may improve performance by
          reducing the number of source files that must be scanned for
          events.  File modification times are used to determine when
          the cached information about a file must be updated.

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
	    "all-deps|d"           => sub { $certlib_opts{"all_deps"} = !$certlib_opts{"all_deps"}; },
	    "static-makefile|s=s"  => sub {shift;
					   $mf_name = shift;
					   $certlib_opts{"all_deps"} = 1;
					   $no_build = 1;},
	    "acl2|a=s"             => \$acl2,
	    "acl2-books|b=s"       => \$acl2_books,
	    "bin=s"                => sub {
		shift;
		my $arg = shift;
		$bin_dir = canonical_path(remove_trailing_slash($arg));
		if (!$bin_dir) {
		    die("Fatal: bad path in directive --bin $arg\n");
		}
	    },
	    "include|i=s"          => sub {shift;
					   push(@includes, shift);},
	    "include-after|ia=s"     => sub {shift;
					     push(@include_afters,
						  shift);},
	    "relative-paths|r=s"   => sub {
		shift;
		my $arg = shift;
		$base_path = abs_canonical_path($arg);
		if (! $base_path) {
		    die("Fatal: bad path in directive --relative-paths/-r $arg\n");
		}
	    },
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
	    "cache=s"              => \$cache_file,
	    "accept-cache"         => \$certlib_opts{"believe_cache"},
	    "deps-of|p=s"          => sub { shift; push(@user_targets, "-p " . shift); },
	    "params=s"             => \$params_file,
	    "<>"                   => sub { push(@user_targets, shift); },
	    );

sub remove_trailing_slash {
    my $dir = shift;
    return ( substr($dir,-1) eq "/" && $dir ne "/" )
	? substr($dir,0,-1) : $dir;
}

certlib_set_opts(\%certlib_opts);

my $cache = retrieve_cache($cache_file);

# If $acl2_books is still not set, then:
# - set it based on the location of acl2 in the path, if available
# - otherwise set it to the directory containing this script.

unless ($acl2) {
    $acl2 = "acl2";
}

# convert user-provided ACL2 to cygwin path, under cygwin
$acl2 = path_import($acl2);
# this is probably always /dev/null but who knows under windows
my $devnull = File::Spec->devnull;
# get the absolute path
$acl2 = `which $acl2 2>$devnull`;
chomp($acl2);  # remove trailing newline

if ($acl2) {
    # canonicalize the path
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
	# was:
	# my $tmp_acl2_books = rel_path(dirname($acl2), "books");
	my $tmp_acl2_books = File::Spec->catfile(dirname($acl2), "books");
	if (-d $tmp_acl2_books) {
	    $acl2_books = $tmp_acl2_books;
	} else {
	    $acl2_books = "$RealBin/..";
	}
    } else {
	$acl2_books = "$RealBin/..";
    }
}

$acl2_books = abs_canonical_path($acl2_books);
unless($quiet) {
    print "System books directory is ${acl2_books}\n";
}

certlib_add_dir("SYSTEM", $acl2_books);
# In case we're going to run Make, set the ACL2_SYSTEM_BOOKS
# and ACL2 environment variables to match our assumption.
# In cygwin, ACL2 reads paths like c:/foo/bar whereas we're dealing in
# paths like /cygdrive/c/foo/bar, so "export" it
my $acl2_books_env = path_export($acl2_books);
$ENV{"ACL2_SYSTEM_BOOKS"} = $acl2_books_env;

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
my %otherhash = ( );

foreach my $target (@targets) {
    add_deps($target, $cache, \%depmap, \%sourcehash, \%otherhash, \%tscache, 0);
}

if ($params_file && open (my $params, "<", $params_file)) {
    while (my $pline = <$params>) {
	my @parts = $pline =~ m/([^:]*):(.*)/;
	if (@parts) {
	    my ($certname, $paramstr) = @parts;
	    my $certpars = cert_get_params($certname, \%depmap);
	    if ($certpars) {
		my $passigns = parse_params($paramstr);
		foreach my $pair (@$passigns) {
		    $certpars->{$pair->[0]} = $pair->[1];
		}
	    }
	}
    }
    close($params);
}


store_cache($cache, $cache_file);

my @sources = sort(keys %sourcehash);

# Is this how we want to nest these?  Pick a command, run it on
# every source file, versus pick a source file, run every command?
# This way seems more flexible; commands can be grouped together.
foreach my $run (@run_sources) {
    foreach my $source (@sources) {
	&$run($source);
    }
}

my @certs = sort(keys %depmap);

# Warn about books that include relocation stubs
my %stubs = (); # maps stub files to the books that include them
foreach my $cert (@certs) {
    my $certdeps = cert_bookdeps($cert, \%depmap);
    foreach my $dep (@$certdeps) {
	if (cert_get_param($dep, \%depmap, "reloc_stub")) {
	    if (exists $stubs{$dep}) {
		push(@{$stubs{$dep}}, $cert);
	    } else {
		$stubs{$dep} = [ $cert ];
	    }
	}
    }
}
if (%stubs && ! $quiet) {
    print "Relocation warnings:\n";
    print "--------------------------\n";
    my @stubbooks = sort(keys %stubs);
    foreach my $stub (@stubbooks) {
	print "Stub file:       $stub\n";
	# note: assumes each stub file includes only one book.
	print "relocated to:    ${cert_bookdeps($stub, \%depmap)}[0]\n";
	print "is included by:\n";
	foreach my $cert (sort(@{$stubs{$stub}})) {
	    print "                 $cert\n";
	}
	print "--------------------------\n";
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
	print $mf "ACL2_SYSTEM_BOOKS ?= " . canonical_path("$RealBin/..") . "\n";
	if ($bin_dir) {
	    print $mf "export ACL2_BIN_DIR := ${bin_dir}\n";
	}
	print $mf "include \$(ACL2_SYSTEM_BOOKS)/build/make_cert\n\n";
    }

    foreach my $incl (@includes) {
	print $mf "\ninclude $incl\n";
    }

    print $mf "\n.PHONY: all-cert-pl-certs\n\n";
    print $mf "# Depends on all certificate files.\n";
    print $mf "all-cert-pl-certs:\n\n";

    # declare $var_prefix_CERTS to be the list of certificates
    print $mf $var_prefix . "_CERTS :=";

    foreach my $cert (@certs) {
	print $mf " \\\n     $cert";
	# if (cert_get_param($cert, \%depmap, "acl2x")) {
	#     my $acl2xfile = cert_to_acl2x($cert);
	#     print $mf " \\\n     $acl2xfile";
	# }
    }

    print $mf "\n\n";

    # print $mf "ifneq (\$(ACL2_PCERT),)\n\n";
    # print $mf "${var_prefix}_CERTS := \$(${var_prefix}_CERTS)";
    # foreach my $cert (@certs) {
    # 	if ($cert =~ /\.cert$/) {
    # 	    my $base = $cert;
    # 	    $base =~ s/\.cert$//;
    # 	    print $mf " \\\n     $base.pcert0";
    # 	    print $mf " \\\n     $base.pcert1";
    # 	}
    # }
    # print $mf "\n\nendif\n";

    print $mf "all-cert-pl-certs: \$(" . $var_prefix . "_CERTS)\n\n";

    # declare $var_prefix_SOURCES to be the list of sources
    print $mf $var_prefix . "_SOURCES :=";
    foreach my $source (@sources) {
	print $mf " \\\n     $source ";
    }
    print $mf "\n\n";

    # Write out the list of hons-only certs
    # Propagate the hons-only requirement:
    my %visited;
    foreach my $reqparam (keys %reqparams) {
	%visited = ();
	foreach my $cert (@certs) {
	    propagate_reqparam($cert, $reqparam, \%visited, \%depmap);
	}

	print $mf "${var_prefix}_${reqparams{$reqparam}} :=";
	foreach my $cert (@certs) {
	    if (cert_get_param($cert, \%depmap, $reqparam)) {
		print $mf " \\\n     $cert ";
	    }
	}
	print $mf "\n\n";
    }
    # If there are labels, write out the sources and certs for those
    foreach my $label (sort(keys %labels)) {
	my @topcerts = @{$labels{$label}};
	my @labelcerts = ();
	my @labelsources = ();
	%visited = ();
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
	    # if (cert_is_two_pass($cert, \%depmap)) {
	    # 	my $acl2x = cert_to_acl2x($cert);
	    # 	print $mf " \\\n     $acl2x";
	    # }
	}
	print $mf "\n\n";
	# print $mf "ifneq (\$(ACL2_PCERT),)\n\n";
	# print $mf "${label}_CERTS := \$(${label}_CERTS)";
	# foreach my $cert (@labelcerts) {
	#     my $base = $cert;
	#     $base =~ s/\.cert$//;
	#     print $mf " \\\n     $base.pcert";
	#     print $mf " \\\n     $base.acl2x";
	# }
	# print $mf "\n\nendif\n";

	print $mf "${label}_SOURCES :=";
	foreach my $source (@labelsources) {
	    print $mf " \\\n     $source";
	}
	print $mf "\n\n";
    }

    my $warned_bindir = 0;

    # write out the dependencies
    foreach my $cert (@certs) {
	my $certdeps = cert_deps($cert, \%depmap);
	my $srcdeps = cert_srcdeps($cert, \%depmap);
	my $otherdeps = cert_otherdeps($cert, \%depmap);
	my $image = cert_image($cert, \%depmap);
	my $useacl2x = cert_get_param($cert, \%depmap, "acl2x") || 0;
	# BOZO acl2x implies no pcert
	my $pcert_ok = ( ! $useacl2x && cert_get_param($cert, \%depmap, "pcert")) || 0;
	my $acl2xskip = cert_get_param($cert, \%depmap, "acl2xskip") || 0;
	print $mf "$cert : acl2x = $useacl2x\n";
	print $mf "$cert : pcert = $pcert_ok\n";
	# print $mf "#$cert params: ";
	# my $params = cert_get_params($cert, \%depmap);
	# while (my ($key, $val) = each %$params) {
	#     print $mf "$key = $val ";
	# }
	print $mf "\n";
	print $mf "$cert :";
	foreach my $dep (@$certdeps, @$srcdeps, @$otherdeps) {
	    print $mf " \\\n     $dep";
	}
	if ($image && ($image ne "acl2")) {
	    if ($bin_dir) {
		# was:
		# print $mf " \\\n     " . rel_path($bin_dir, $image);
		print $mf " \\\n     " . File::Spec->catfile($bin_dir, $image);
	    } elsif (! $warned_bindir) {
		print "Warning: no --bin set, so not adding image dependencies,\n";
		print " e.g.   $cert : $image\n";
		$warned_bindir = 1;
	    }
	}
	print $mf "\n";
	if ($useacl2x) {
	    my $acl2xfile = cert_to_acl2x($cert);
#     This would be a nice way to do things, but unfortunately the "private"
#     keyword for target-specific variables was introduced in GNU Make 3.82,
#     which isn't widely used yet --
#	    print $mf "$cert : private TWO_PASS := 1\n";
#     Instead, sadly, we'll individually set the TWO_PASS variable for
#     each target instead.  (Note the ELSE case below.)
	    print $mf "$cert : |";   # order-only prerequisite
	    print $mf " \\\n     $acl2xfile";
	    print $mf "\n\n";
	    print $mf "$acl2xfile : acl2xskip = $acl2xskip\n";
	    print $mf "$acl2xfile :";
	    foreach my $dep (@$certdeps, @$srcdeps, @$otherdeps) {
		print $mf " \\\n     $dep";
	    }
	    if ($image && ($image ne "acl2")) {
		if ($bin_dir) {
		    # was:
		    # print $mf " \\\n     " . rel_path($bin_dir, $image);
		    print $mf " \\\n     " . File::Spec->catfile($bin_dir, $image);
		} elsif (! $warned_bindir) {
		    print "Warning: no --bin set, so not adding image dependencies,\n";
		    print " e.g.   $cert : $image\n";
		    $warned_bindir = 1;
		}
	    }
	}

	print $mf "\n\n";
    }

    # Write dependencies for pcert mode.
    print $mf "ifneq (\$(ACL2_PCERT),)\n\n";

    foreach my $cert (@certs) {
	my $useacl2x = cert_get_param($cert, \%depmap, "acl2x") || 0;
	# BOZO acl2x implies no pcert
	my $pcert_ok = (! $useacl2x && cert_get_param($cert, \%depmap, "pcert")) || 0;

	my $bookdeps = cert_bookdeps($cert, \%depmap);
	my $portdeps = cert_portdeps($cert, \%depmap);
	my $srcdeps = cert_srcdeps($cert, \%depmap);
	my $otherdeps = cert_otherdeps($cert, \%depmap);
	my $image = cert_image($cert, \%depmap);
	(my $base = $cert) =~ s/\.cert$//;
	# this is either the pcert0 or pcert1 depending on pcert_ok
	my $pcert = cert_sequential_dep($cert, \%depmap);
	print $mf "$pcert : pcert = $pcert_ok\n";
	print $mf "$pcert : acl2x = $useacl2x\n";
	print $mf "$pcert :";
	foreach my $dep (@$bookdeps, @$portdeps) {
	    # this is either the pcert0 or pcert1 depending whether the dependency
	    # has pcert set
	    print $mf " \\\n     " . cert_sequential_dep($dep, \%depmap);
	}
	foreach my $dep (@$srcdeps, @$otherdeps) {
	    print $mf " \\\n     $dep";
	}
	if ($image && ($image ne "acl2")) {
	    if ($bin_dir) {
		# was:
		# print $mf " \\\n     " . rel_path($bin_dir, $image);
		print $mf " \\\n     " . File::Spec->catfile($bin_dir, $image);
	    } elsif (! $warned_bindir) {
		print "Warning: no --bin set, so not adding image dependencies,\n";
		print " e.g.   $cert : $image\n";
		$warned_bindir = 1;
	    }
	}
	print $mf "\n";
	# If we're doing prov cert, pcert1 depends on pcert0 and cert depends on pcert1
	if ($pcert_ok) {
	    # Pcert1 files depend only on the corresp. pcert0.
	    print $mf "$base.pcert1 : acl2x = $useacl2x\n";
	    print $mf "$base.pcert1 : pcert = $pcert_ok\n";
	    print $mf "$base.pcert1 : $base.pcert0\n";
	} elsif ($useacl2x) {
	    # pcert1 depends on .acl2x
	    print $mf "$base.pcert1 : $base.acl2x\n";
	}
	print $mf "$cert : $base.pcert1\n";
	print $mf "\n";
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


