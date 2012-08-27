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

       -r, --real   Toggle real time versus user+system

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
  'real'    => 0,
  'pcert'   => $ENV{'ACL2_PCERT'}
);

my @user_targets = ();
my @targets = ();
my @deps_of = ();

my $debug = 0;

my $cache_file = 0;
my $params_file = 0;
my $options_okp = GetOptions('h|html' => \$OPTIONS{'html'},
			     'help'   => \$OPTIONS{'help'},
			     'nowarn' => \$OPTIONS{'nowarn'},
			     'nopath' => \$OPTIONS{'nopath'},
			     'nolist' => \$OPTIONS{'nolist'},
			     'short=i' =>  \$OPTIONS{'short'},
			     'real|r'  => \$OPTIONS{'real'},
			     'debug|d' => \$debug,
			     "targets|t=s"          
			              => sub { shift;
					       read_targets(shift, \@user_targets);
					   },
			     "deps-of|p=s"
			              => \@deps_of,
			     "cache|h=s"
			              => \$cache_file,
			     "params=s"             => \$params_file,
			     );

my $cache = {};
$cache = retrieve_cache($cache_file);

my %tscache = ();

push (@user_targets, @ARGV);

if (!$options_okp || $OPTIONS{"help"})
{
    print $HELP_MESSAGE;
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my %deps = ();
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
    my $path = canonical_path(to_cert_name($target));
    if ($path) {
	push (@targets, $path);
    } else {
	print "Warning: bad target path $target\n";
    }
}

foreach my $top (@deps_of) {
    my $path = canonical_path(to_source_name($top));
    if ($path) {
	my ($certdeps) = find_deps($path, $cache, 1, \%tscache);
	push (@targets, @{$certdeps});
    } else {
	print "Warning: bad path in --deps-of/-p $top\n";
    }
}

unless (@targets) {
    print "\nError: No targets provided.\n";
    print $HELP_MESSAGE;
    exit 1;
}

my %sourcehash = ();
my %otherhash = ();
foreach my $target (@targets) {
    if ($target =~ /\.cert/) {
	add_deps($target, $cache, \%deps, \%sourcehash, \%otherhash, \%tscache, 0);
    }
}

if ($params_file && open (my $params, "<", $params_file)) {
    while (my $pline = <$params>) {
	my @parts = $pline =~ m/([^:]*):(.*)/;
	if (@parts) {
	    my ($certname, $paramstr) = @parts;
	    my $certpars = cert_get_params($certname, \%deps);
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

my $basecosts = {};
read_costs(\%deps, $basecosts, $warnings, $OPTIONS{'real'}, $OPTIONS{'pcert'});
print "done read_costs\n" if $debug;

# foreach my $file (keys %$basecosts) {
#     if ($file =~ /\.cert$/) {
# 	$basecosts->{$file} = 0.00001;
#     }
# }


compute_cost_paths(\%deps, $basecosts, $costs, $warnings, $OPTIONS{'pcert'});
print "done compute_cost_paths\n" if $debug;

print "costs: " .  $costs . "\n" if $debug;

(my $topbook, my $topbook_cost) = find_most_expensive(\@targets, $costs);

my $savings = compute_savings($costs, $basecosts, \@targets, $debug, \%deps, $OPTIONS{'pcert'}); 


	# ($costs, $warnings) = make_costs_table($target, \%deps, $costs, $warnings, $OPTIONS{"short"});



unless ($OPTIONS{'nowarn'}) {
    print warnings_report($warnings, $OPTIONS{"html"});
}

unless ($OPTIONS{'nopath'}) {
    print critical_path_report($costs, $basecosts, $savings, $topbook, $OPTIONS{"html"}, $OPTIONS{"short"});
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

if ((! $OPTIONS{"html"}) && $OPTIONS{"pcert"}) {
    my $acl2xtime = 0.0;
    my $pcert1time = 0.0;
    my $pcert0time = 0.0;
    my $certtime = 0.0;
    foreach my $key (keys %$basecosts) {
	my $selfcost = $basecosts->{$key};
	$selfcost = ($selfcost >= 0) ? $selfcost : 0.0;
	if ($key =~ /\.cert$/) {
	    $certtime = $certtime + $selfcost;
	} elsif ($key =~ /\.acl2x$/) {
	    $acl2xtime = $acl2xtime + $selfcost;
	} elsif ($key =~ /\.pcert1$/) {
	    $pcert1time = $pcert1time + $selfcost;
	} elsif ($key =~ /\.pcert0$/) {
	    $pcert0time = $pcert0time + $selfcost;
	}
    }

    print "\n";
    print "Total acl2x build time: " . human_time($acl2xtime) . "\n";
    print "Total pcert0 build time: " . human_time($pcert0time) . "\n";
    print "Total pcert1 build time: " . human_time($pcert1time) . "\n";
    print "Total cert build time: " . human_time($certtime) . "\n";
}

# print "\n\nBasecosts:\n";
# while ((my $key, my $val) = each %$basecosts) {
#     print "$key: $val\n";
# }
