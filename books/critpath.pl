#!/usr/bin/env perl

# critpath.pl - Critical path analysis for ACL2 books
# Copyright 2008-2009 by Sol Swords 
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

use warnings;
use strict;
use Getopt::Long qw(:config bundling); 
use File::Spec;
use FindBin qw($RealBin);

# Note: Trying out FindBin::$RealBin.  If breaks, we can go back to
# the system below.

# Perl's include mechanism seems horribly broken.  FindBin doesn't understand
# what to do if the script is invoked through a symlink.  The following is
# ugly, but seems to work through symlinks, or through "perl filename", or
# through ./filename, without requiring extra modules from CPAN.

# sub fully_resolve_symlink {
#     my $path = shift;
#     while (-l $path) {
# 	$path = readlink $path;
#     }
#     return $path;
# }
	
# my $script_file = fully_resolve_symlink($0);
# my $script_dir = File::Spec->catpath( (File::Spec->splitpath($script_file))[0,1] );

(do "$RealBin/certlib.pl") or die("Error loading $RealBin/certlib.pl:\n $!");


my $HELP_MESSAGE = "

 critpath.pl [OPTIONS] <top-book>

 This program displays the longest dependency chain leading up to a certified
 book, measured in sequential certification time.  This is the amount of time
 it would take to certify your book if you had as many parallel processors as
 could be used, each running at a fixed speed.

 Steps for using this program:

 0. Ensure that you have GNU time installed and accessible by running \"env
    time\".  For example, running \"env time --version\" should print something
    like \"GNU time 1.7\".

 1. Use cert.pl to certify all the books you're interested in (from scratch)
    with the TIME_CERT environment variable set to \"yes\" and exported.

    For example,
     setenv TIME_CERT yes   # in csh, or
     export TIME_CERT=yes   # in bash
     cert.pl top.lisp -c    # clean
     cert.pl top.lisp -j 8  # recertify using 8 parallel processors

 2. Run critpath.pl [OPTIONS] <top-book>, where <top-book> is the
    .lisp or .cert file of the book of interest.

    The options are as follows:

       -h, --html   Print HTML formatted output (the default is plain text.)

       --nowarn     Suppress warnings.
       --nopath     Suppress critical path information.
       --nolist     Suppress individual-files list.

       --help       Print this help message and exit.

       --makefile=<makefile>
       -m <makefile>
                    Compute the dependency graph from the given makefile
                    instead of recomputing it by looking at all the
                    source files.  The makefile must be of the format
                    produced by cert.pl; this option uses a simple
                    regular expression parsing of the makefile to
                    produce the dependency graph.
 ";

my %OPTIONS = (
  'html'    => '',
  'help'    => '',
  'nowarn'  => '',
  'nopath'  => '',
  'nolist'  => '',
  'makefile' => ''
);

my $options_okp = GetOptions('h|html' => \$OPTIONS{'html'},
			     'help'   => \$OPTIONS{'help'},
			     'nowarn' => \$OPTIONS{'nowarn'},
			     'nopath' => \$OPTIONS{'nopath'},
			     'nolist' => \$OPTIONS{'nolist'},
			     'm|makefile=s' => \$OPTIONS{'makefile'}
			     );

my $args_okp = (@ARGV == 1);

if (!$options_okp || !$args_okp || $OPTIONS{"help"})
{
    print $HELP_MESSAGE;
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my %deps;
my $topfile = canonical_path(shift);
$topfile =~ s/\.lisp$/.cert/;

if ($OPTIONS{'makefile'}) {
    %deps = makefile_dependency_graph($OPTIONS{'makefile'});
} else {
    %deps = ();
    my %certlib_opts = ( "debugging" => 0,
			 "clean_certs" => 0,
			 "print_deps" => 0,
			 "all_deps" => 1 );

    certlib_set_opts(\%certlib_opts);

    my @sources = ();
    add_deps($topfile, \%deps, \@sources);
}

my ($costs, $warnings) = make_costs_table($topfile, \%deps);


unless ($OPTIONS{'nowarn'}) {
    print warnings_report($warnings, $OPTIONS{"html"});
}

unless ($OPTIONS{'nopath'}) {
    print critical_path_report($topfile, $costs, $OPTIONS{"html"});
}

unless ($OPTIONS{'nolist'}) {
    print individual_files_report($costs, $OPTIONS{"html"});
}
