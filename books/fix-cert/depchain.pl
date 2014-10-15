#!/usr/bin/env perl
use warnings;
use strict;
use Getopt::Long qw(:config bundling); 
use File::Spec;
use FindBin qw($RealBin);
use Storable;

# Note: Trying out FindBin::$RealBin.  If breaks, we can go back to
# the system below.

(do "$RealBin/../build/certlib.pl")  or die("Error loading $RealBin/../build/certlib.pl:\n $!");
my %OPTIONS = (
  'nolist'  => '',
);

my @user_targets = ();
my @targets = ();

my $debug = 0;

my $options_okp = GetOptions('nolist' => \$OPTIONS{'nolist'},
			     'debug|d' => \$debug,
                             'max-depth|m=i' =>  1000,
			     "targets|t=s"          
			              => sub { shift;
					       read_targets(shift, \@user_targets);
					   },
			     );

my $cache = {};

my $depdb = new Depdb( evcache => $cache );

push (@user_targets, @ARGV);

if (!$options_okp || $OPTIONS{"help"})
{
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my $costs = {};
my $warnings = [];

my %certlib_opts = ( "debugging" => 0,
		     "clean_certs" => 0,
		     "print_deps" => 0,
		     "all_deps" => 1 );

certlib_set_opts(\%certlib_opts);

# add :dir :system as the path to this executable
certlib_add_dir("SYSTEM", "$RealBin/..");


foreach my $target (@user_targets) {
    my $path = canonical_path(to_cert_name($target));
    if ($path) {
	push (@targets, $path);
    } else {
	print "Warning: bad target path $target\n";
    }
}


unless (@targets) {
    print "\nError: No targets provided.\n";
    exit 1;
}

foreach my $target (@targets) {
    if ($target =~ /\.cert/) {
	add_deps($target, $depdb, 0);
    }
}

my $basecosts;
 $basecosts = {};
 read_costs($depdb, $basecosts, $warnings, $OPTIONS{'real'}, $OPTIONS{'pcert'});
# print "done read_costs\n" if $debug;



compute_cost_paths($depdb, $basecosts, $costs, $warnings, $OPTIONS{'pcert'});
print "done compute_cost_paths\n" if $debug;

print "costs: " .  $costs . "\n" if $debug;


sub dep_chain_report {

# individual_files_report(costs,htmlp) returns a string describing the
# self-times of each file in the costs_table, either in either TEXT or HTML
# format, per the value of htmlp.
    my ($costs,$basecosts) = @_;

    my @sorted = sort { ($costs->{$a}->{"totaltime"} + 0.0) <=> ($costs->{$b}->{"totaltime"} + 0.0) } keys(%{$costs});
    my $ret;

    foreach my $name (@sorted)
    {
        if ($name =~ /\.cert$/) { #only concern ourselves with cert files
            $ret .= sprintf("%s\n", $name);
        }
    }
    return $ret;
}


unless ($OPTIONS{'nolist'}) {
    print dep_chain_report($costs, $basecosts);
}
