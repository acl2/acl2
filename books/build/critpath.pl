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
# Original author: Sol Swords <sswords@centtech.com>

# critpath.pl - Critical path analysis for ACL2 books

use warnings;
use strict;
use Getopt::Long qw(:config bundling);
use File::Spec;
use FindBin qw($RealBin);
use lib "$RealBin/lib";
use Storable qw(nstore retrieve);
use Certlib;
use Bookscan;

# Note: Trying out FindBin::$RealBin.  If breaks, we can go back to
# the system below.

# (do "$RealBin/certlib.pl") or die("Error loading $RealBin/certlib.pl:\n $!");


my $HELP_MESSAGE = "

 critpath.pl [OPTIONS] <top-book1> <top-book2> ...

 This program displays the longest dependency chain leading up to any of the
 top-books specified, measured in sequential certification time.  This is the
 amount of time it would take to certify your book if you had as many parallel
 processors as could be used, each running at a fixed speed.  Additionally, by
 default, it then displays the complete list of dependencies, sorted by
 cumulative certification time.

 Steps for using this program:

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
       --nodepthpath Suppress max-depth path information.
       --nolist     Suppress individual-files list.

       -r, --real   Toggle real time versus user+system

       --help       Print this help message and exit.

       -t, --targets <filename>
                    Add all targets listed in <filename>, in addition
                    to any given on the command line.

       -p, --deps-of <filename>
                    Add as targets all dependencies of the specified
                    source file.

       -m, --max-depth <N>
                    Print a maximum of N levels of directory context;
                    default 1.

       -c, --cache <filename>
                    Read/write a sourcefile events cache, which may
                    improve performance.  See 'cert.pl --help' for
                    more info.

       -w, --write-costs <filename>
                    Write the base costs for each file into <filename>
                    in perl's Storable format.

       --costs-file <filename>
                    Instead of reading the costs for each file from
                    its .cert.time file, read them all from a file (as
                    written by write_costs).  Only really works
                    correctly if all targets/dependencies are the
                    same.

       -f, --from-file <filename>
                    This option may be given multiple times.  Instead
                    of assuming that everything starts out
                    uncertified, assume that the given file(s) are the
                    only ones that have been updated, and compute
                    paths relative to them.

   --pcert-all
          Compute dependencies assuming provisional certification is used
          for all books, not just the ones with the \'pcert\' cert_param.

   --target-ext <extension>
   -e <extension>
          Normally, when targets are specified by their source filename (.lisp)
          or without an extension, rather than by their target filename (.cert,
          .acl2x, .pcert0, .pcert1), the target extension used is \'cert\'.
          This option allows you to specify this default extension as (say)
          \'pcert0\' instead.

";

my %OPTIONS = (
  'html'    => '',
  'help'    => '',
  'nowarn'  => '',
  'nopath'  => '',
  'nolist'  => '',
  'short'   => 1,
  'real'    => 0,
  'pcert'   => $ENV{'ACL2_PCERT'},
  'write_costs' => 0,
  'costs_file' => 0,
  'pcert_all' => 0,
  'target_ext' => "cert",
);

my @user_targets = ();
my @targets = ();
my @deps_of = ();
my @user_from_files = ();
my %from_files = ();

my $debug = 0;

my $cache_file = 0;
my $params_file = 0;

my %certlib_opts = ( "debugging" => 0,
		     "clean_certs" => 0,
		     "print_deps" => 0,
		     "all_deps" => 1,
                     "pcert_all" => 0,
		     "include_excludes" => 0,
    );


my $options_okp = GetOptions('h|html' => \$OPTIONS{'html'},
			     'help'   => \$OPTIONS{'help'},
			     'nowarn' => \$OPTIONS{'nowarn'},
			     'nopath' => \$OPTIONS{'nopath'},
			     'nodepthpath' => \$OPTIONS{'nodepthpath'},
			     'nolist' => \$OPTIONS{'nolist'},
			     'short=i' =>  \$OPTIONS{'short'},
			     'max-depth|m=i' =>  \$OPTIONS{'short'},
			     'real|r'  => \$OPTIONS{'real'},
			     'debug|d' => \$debug,
			     "targets|t=s"
			              => sub { shift;
					       read_targets(shift, \@user_targets);
					   },
			     "deps-of|p=s"
			              => \@deps_of,
			     "cache|c=s"
			              => \$cache_file,
			     "params=s"             => \$params_file,
			     "write-costs|w=s" => \$OPTIONS{'write_costs'},
			     "costs-file=s" => \$OPTIONS{'costs_file'},
                             "pcert-all"    => \$certlib_opts{'pcert_all'},
                             "include-excludes"  => \$certlib_opts{'include_excludes'},
                             "target-ext|e=s"    => \$OPTIONS{'target_ext'},
                             "from-file|f=s"     => \@user_from_files,
			     );

my $cache = {};
$cache = retrieve_cache($cache_file);

my $depdb = new Depdb( evcache => $cache );

push (@user_targets, @ARGV);

if (!$options_okp || $OPTIONS{"help"})
{
    print $HELP_MESSAGE;
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my $costs = {};
my $warnings = [];

certlib_set_opts(\%certlib_opts);

# add :dir :system as the path to this executable
certlib_add_dir("SYSTEM", "$RealBin/..");


foreach my $target (@user_targets) {
    my $path = canonical_path(to_cert_name($target, $OPTIONS{'target_ext'}));
    if ($path) {
	push (@targets, $path);
    } else {
	print "Warning: bad target path $target\n";
    }
}

foreach my $top (@deps_of) {
    my $path = canonical_path(to_source_name($top));
    if ($path) {
	my $certinfo = find_deps($path, $depdb, 0);
	push (@targets, @{$certinfo->bookdeps});
	push (@targets, @{$certinfo->portdeps});
    } else {
	print "Warning: bad path in --deps-of/-p $top\n";
    }
}

unless (@targets) {
    print "\nError: No targets provided.\n";
    print $HELP_MESSAGE;
    exit 1;
}

foreach my $target (@targets) {
    (my $tcert = $target) =~ s/\.(acl2x|pcert(0|1))/\.cert/;
    add_deps($tcert, $depdb, 0);
    if ($tcert =~ /\.cert/) {
	add_deps($tcert, $depdb, 0);
    }
}

foreach my $from (@user_from_files) {
    my $path = canonical_path(to_cert_name($from, $OPTIONS{'target_ext'}));
    if ($path) {
	$from_files{$path}=1;
    } else {
	print "Warning: bad from_file path $from\n";
    }

}


if ($params_file && open (my $params, "<", $params_file)) {
    while (my $pline = <$params>) {
	my @parts = $pline =~ m/([^:]*):(.*)/;
	if (@parts) {
	    my ($certname, $paramstr) = @parts;
	    my $certpars = $depdb->cert_get_params($certname);
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

my $basecosts;
if ($OPTIONS{'costs_file'}) {
    $basecosts = retrieve($OPTIONS{'costs_file'});
} else {
    $basecosts = {};
    read_costs($depdb, $basecosts, $warnings, $OPTIONS{'real'});
    print "done read_costs\n" if $debug;
}

# foreach my $file (keys %$basecosts) {
#     if ($file =~ /\.cert$/) {
# 	$basecosts->{$file} = 0.00001;
#     }
# }

if ($OPTIONS{'write_costs'}) {
    nstore($basecosts, $OPTIONS{'write_costs'});
}

my $updateds = (@user_from_files) ? \%from_files : 1;
compute_cost_paths($depdb, $basecosts, $costs, $updateds, $warnings);

print "done compute_cost_paths\n" if $debug;

print "costs: " .  $costs . "\n" if $debug;

(my $topbook, my $topbook_cost) = find_most_expensive(\@targets, $costs, $updateds);

my $savings = compute_savings($costs, $basecosts, \@targets, $updateds, $debug, $depdb);


	# ($costs, $warnings) = make_costs_table($target, $depdb, $costs, $warnings, $OPTIONS{"short"});



unless ($OPTIONS{'nowarn'}) {
    print warnings_report($warnings, $OPTIONS{"html"});
}

unless ($OPTIONS{'nopath'}) {
    print critical_path_report($costs, $basecosts, $savings, $topbook, $OPTIONS{"html"}, $OPTIONS{"short"});
}

unless ($OPTIONS{'nolist'}) {
    print individual_files_report($costs, $basecosts, $OPTIONS{"html"}, $OPTIONS{"short"});
}

unless ($OPTIONS{'nodepthpath'}) {
    print deepest_path_report($costs, $basecosts, $savings, $topbook, $OPTIONS{"html"}, $OPTIONS{"short"});
}



my ($max_parallel, $max_start_time, $max_end_time, $avg_parallel, $sum_parallel)
    = parallelism_stats($costs, $basecosts);

if (! $OPTIONS{"html"}) {
    print "Maximum parallelism: $max_parallel processes, from time $max_start_time to $max_end_time\n";
    print "Average level of parallelism: $avg_parallel.\n";
    print "Total time for all files: " . human_time($sum_parallel,0) . ".\n";
}

if (! $OPTIONS{"html"}) {
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
    if ($acl2xtime != 0.0) {
	print "Total acl2x build time: " . human_time($acl2xtime) . "\n";
    }
    if ($pcert0time != 0.0) {
	print "Total pcert0 build time: " . human_time($pcert0time) . "\n";
    }
    if ($pcert1time != 0.0) {
	print "Total pcert1 build time: " . human_time($pcert1time) . "\n";
    }
    if ($certtime != 0.0) {
	print "Total cert build time: " . human_time($certtime) . "\n";
    }
}

# print "\n\nBasecosts:\n";
# while ((my $key, my $val) = each %$basecosts) {
#     print "$key: $val\n";
# }
