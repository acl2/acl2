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
my @targets = ();
my @deps_of = ();
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
my @make_args = ();
my $acl2 = $ENV{"ACL2"};
my $acl2_books = $ENV{"ACL2_SYSTEM_BOOKS"};
my $keep_going = 0;
my $var_prefix = "CERT_PL";
my %certlib_opts = ( "debugging" => 0,
		     "clean_certs" => 0,
		     "print_deps" => 0,
		     "all_deps" => 0,
                     "believe_cache" => 0);

my $cache_file = 0;

$base_path = abs_canonical_path(".");

my $summary_str = "\ncert.pl: Automatic dependency analysis for certifying ACL2 books.\n";


my $helpstr = '
Usage:
perl cert.pl <options, targets>

where targets are filenames of ACL2 files or certificates to be built
and options are as follows:

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
	    "deps-of|p=s"          => \@deps_of,
	    "debug"                => \$certlib_opts{"debugging"},
	    # Note: this doesn't do anything yet.
	    "cache|h=s"            => \$cache_file,
	    "accept-cache"         => \$certlib_opts{"believe_cache"}
	    );

certlib_set_opts(\%certlib_opts);

my $cache = {};
if ($cache_file && -e $cache_file) {
    $cache = retrieve($cache_file);
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

push(@user_targets, @ARGV);

my %seen = ( );
my @sources = ( );

foreach my $target (@user_targets) {
    push (@targets, to_basename($target) . ".cert");
}

my %tscache = ();

foreach my $top (@deps_of) {
    (my $deps, my $two_pass) = find_deps(to_basename($top), $cache, 1, \%tscache);
    push (@targets, @{$deps});
}


unless (@targets) {
    print "\nError: No targets provided.\n";
    print $helpstr;
    exit 1;
}


foreach my $target (@targets) {
    add_deps($target, $cache, \%seen, \@sources, \%tscache);
}

$cache_file && store($cache, $cache_file);

@sources = sort(@sources);

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
	print $mf "include "
	    . canonical_path(rel_path($RealBin, "make_cert"))
	    . "\n\n";
    }

    foreach my $incl (@includes) {
	print $mf "\ninclude $incl\n";
    }

    print $mf "\n.PHONY: all-cert-pl-certs\n\n";
    print $mf "# Depends on all certificate files.\n";
    print $mf "all-cert-pl-certs:\n\n";
    
    # declare $var_preifx_CERTS to be the list of certificates
    print $mf $var_prefix . "_CERTS :=";
    my @certs = ();
    while ((my $key, my $value) = each %seen) {
	if ($value) { 
	    push (@certs, $key);
	}
    }

    @certs = sort(@certs);

    foreach my $cert (@certs) {
	print $mf " \\\n     $cert";
    }

    print $mf "\n\n";

    print $mf "all-cert-pl-certs: \$(" . $var_prefix . "_CERTS)\n\n";

    # declare $var_prefix_SOURCES to be the list of sources
    print $mf $var_prefix . "_SOURCES :=";
    foreach my $source (@sources) {
	print $mf " \\\n     $source ";
    }
    print $mf "\n\n";

    # write out the dependencies
    foreach my $cert (@certs) {
	my $val = $seen{$cert};
	if ($val) {
	    my @the_deps = @{$val};
	    print $mf "$cert :";
	    foreach my $dep (@the_deps) {
		print $mf " \\\n     $dep";
	    }
	    print $mf "\n\n";
	}
    }

    foreach my $incl (@include_afters) {
	print $mf "\ninclude $incl\n";
    }

    close($mf);
    
    unless ($no_build) {
	my $make_cmd = join(' ', (("make -j $jobs -f $mf_name"
				   . ($keep_going ? " -k" : "")),
				  @make_args));
	if ($certlib_opts{"debugging"}) {
	    print "$make_cmd\n";
	}
	exec $make_cmd;
    }
}

# print_times_seen();


