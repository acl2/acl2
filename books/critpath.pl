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

 critpath.pl [OPTIONS] <top-book1> <top-book2> ... 

 This program displays the longest dependency chain leading up to any of the
 top-books specified, measured in sequential certification time.  This is the
 amount of time it would take to certify your book if you had as many parallel
 processors as could be used, each running at a fixed speed.  Additionally, by
 default, it then displays the complete list of dependencies, sorted by
 cumulative certification time.

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

 2. Run critpath.pl [OPTIONS] <top-book> ..., where each <top-book> is a
    .lisp or .cert file of the book of interest.

    The options are as follows:

       -h, --html   Print HTML formatted output (the default is plain text.)

       --nowarn     Suppress warnings.
       --nopath     Suppress critical path information.
       --nolist     Suppress individual-files list.

       --help       Print this help message and exit.

       -t, --targets <filename>
                    Take the list of top-books from <filename>, in addition
                    to any given on the command line.
 ";

my %OPTIONS = (
  'html'    => '',
  'help'    => '',
  'nowarn'  => '',
  'nopath'  => '',
  'nolist'  => '',
  'short'   => 1
);

my @user_targets = ();
my @targets = ();

my $options_okp = GetOptions('h|html' => \$OPTIONS{'html'},
			     'help'   => \$OPTIONS{'help'},
			     'nowarn' => \$OPTIONS{'nowarn'},
			     'nopath' => \$OPTIONS{'nopath'},
			     'nolist' => \$OPTIONS{'nolist'},
			     'short=i' =>  \$OPTIONS{'short'},
			     "targets|t=s"          
			              => sub { shift;
					       read_targets(shift, \@user_targets);
					   }
			     );

push (@user_targets, @ARGV);

if (!$options_okp || $OPTIONS{"help"})
{
    print $HELP_MESSAGE;
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my %deps = ();
my @sources = ();
my $costs = {};
my $warnings = [];

my %certlib_opts = ( "debugging" => 0,
		     "clean_certs" => 0,
		     "print_deps" => 0,
		     "all_deps" => 1 );

certlib_set_opts(\%certlib_opts);

# add :dir :system as the path to this executable
certlib_add_dir("SYSTEM", $RealBin);


foreach my $target (@user_targets) {
    push (@targets, to_basename($target) . ".cert");
}

foreach my $target (@targets) {
    add_deps($target, \%deps, \@sources);
    ($costs, $warnings) = make_costs_table($target, \%deps, $costs, $warnings, $OPTIONS{"short"});
}




unless ($OPTIONS{'nowarn'}) {
    print warnings_report($warnings, $OPTIONS{"html"});
}

unless ($OPTIONS{'nopath'}) {
    print critical_path_report($costs, $OPTIONS{"html"});
}

unless ($OPTIONS{'nolist'}) {
    print individual_files_report($costs, $OPTIONS{"html"});
}
