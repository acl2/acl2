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
use Storable;

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

 2. Run critpath.pl [OPTIONS] <target> ..., where each <target> is a
    book with or without a .lisp or .cert extension.

    The options are as follows:

       -h, --html   Print HTML formatted output (the default is plain text.)

       --nowarn     Suppress warnings.
       --nopath     Suppress critical path information.
       --nolist     Suppress individual-files list.

       --help       Print this help message and exit.

       -t, --targets <filename>
                    Add all targets listed in <filename>, in addition
                    to any given on the command line.

       -p, --deps-of <filename>
                    Add as targets all dependencies of the book <filename>.
 ";

my %OPTIONS = (
  'html'    => '',
  'help'    => '',
  'nowarn'  => '',
  'nopath'  => '',
  'nolist'  => '',
  'short'   => 1,
);

my @user_targets = ();
my @targets = ();
my @deps_of = ();

my $debug = 0;

my $cache_file = 0;

my $options_okp = GetOptions('h|html' => \$OPTIONS{'html'},
			     'help'   => \$OPTIONS{'help'},
			     'nowarn' => \$OPTIONS{'nowarn'},
			     'nopath' => \$OPTIONS{'nopath'},
			     'nolist' => \$OPTIONS{'nolist'},
			     'short=i' =>  \$OPTIONS{'short'},
			     'debug|d' => \$debug,
			     "targets|t=s"          
			              => sub { shift;
					       read_targets(shift, \@user_targets);
					   },
			     "deps-of|p=s"
			              => \@deps_of,
			     "cache|h=s"
			              => \$cache_file
			     );

my $cache = {};
if ($cache_file && -e $cache_file) {
    $cache = retrieve($cache_file);
}
my %tscache = ();

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

foreach my $top (@deps_of) {
    my $deps = find_deps(to_basename($top), $cache, 1, \%tscache);
    push (@targets, @{$deps});
}

unless (@targets) {
    print "\nError: No targets provided.\n";
    print $HELP_MESSAGE;
    exit 1;
}

foreach my $target (@targets) {
    if ($target =~ /\.cert/) {
	add_deps($target, $cache, \%deps, \@sources, \%tscache);
    }
}

$cache_file && store($cache, $cache_file);

my $basecosts = {};
read_costs(\%deps, $basecosts, $warnings);
print "done read_costs\n" if $debug;

compute_cost_paths(\%deps, $basecosts, $costs, $warnings);
print "done compute_cost_paths\n" if $debug;

print "costs: " .  $costs . "\n" if $debug;
my @keys = keys %{$costs};
(my $topbook, my $topbook_cost) = find_most_expensive(\@targets, $costs);

print "done topbook\n" if $debug;

my @critpath = ();
my $nxtbook = $topbook;
while ($nxtbook) {
    push(@critpath, $nxtbook);
    $nxtbook = $costs->{$nxtbook}->{"maxpath"};
}

my %savings = ();
foreach my $critfile (@critpath) {
    print "critfile: $critfile\n" if $debug;
    my $filebasecost = $basecosts->{$critfile};

    # Get the max savings from speeding up the book: set the file base cost to 0 and recompute crit path.
    my %tmpcosts = ();
    my @tmpwarns = ();
    $basecosts->{$critfile} = 0.0;
    compute_cost_paths(\%deps, $basecosts, \%tmpcosts, \@tmpwarns);
    (my $tmptop, my $tmptopcost) = find_most_expensive(\@targets, \%tmpcosts);
    my $speedup_savings = $topbook_cost - $tmptopcost;
    $speedup_savings = $speedup_savings || 0.000001;

    # Get the max savings from removing the book: set the file total cost to 0 and recompute crit path.
    %tmpcosts = ();
    $tmpcosts{$critfile} = 0;
    compute_cost_paths(\%deps, $basecosts, \%tmpcosts, \@tmpwarns);
    ($tmptop, $tmptopcost) = find_most_expensive(\@targets, \%tmpcosts);
    my $remove_savings = $topbook_cost - $tmptopcost;
    $remove_savings = $remove_savings || 0.000001;

    my %entry = ( "speedup" => $speedup_savings,
		  "remove" => $remove_savings );
    $savings{$critfile} = \%entry;
    $basecosts->{$critfile} = $filebasecost;
}



	# ($costs, $warnings) = make_costs_table($target, \%deps, $costs, $warnings, $OPTIONS{"short"});



unless ($OPTIONS{'nowarn'}) {
    print warnings_report($warnings, $OPTIONS{"html"});
}

unless ($OPTIONS{'nopath'}) {
    print critical_path_report($costs, $basecosts, \%savings, $topbook, $OPTIONS{"html"}, $OPTIONS{"short"});
}

unless ($OPTIONS{'nolist'}) {
    print individual_files_report($costs, $basecosts, $OPTIONS{"html"}, $OPTIONS{"short"});
}



my ($max_parallel, $max_start_time, $max_end_time, $avg_parallel, $sum_parallel)
    = parallelism_stats($costs, $basecosts);

if (! $OPTIONS{"html"}) {
    print "Maximum parallelism: $max_parallel processes, from time $max_start_time to $max_end_time\n";
    print "Average level of parallelism: $avg_parallel.\n";
    print "Total time for all files: " . human_time($sum_parallel,0) . ".\n";
}
