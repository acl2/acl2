#!/usr/bin/env perl

# compare.pl - compare timings on regressions or whatever
# Copyright 2013 by Centaur Technology
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

use warnings;
use strict;
# use Getopt::Long qw(:config bundling); 
# use File::Spec;
# use FindBin qw($RealBin);
use Storable;

my $usage =
'compare.pl:  Print a summary of timings for two runs of some regression.

Usage:
   compare.pl old_cost_file new_cost_file

where old_cost_file and new_cost_file are files produced using critpath.pl\'s
"-w"/"--write-costs" option (or some other method for dumping a Perl Storable
file containing a hash mapping strings to positive numbers).
';

if (@ARGV != 2) {
    print $usage;
    exit(1);
}

my $old = $ARGV[0];
my $new = $ARGV[1];

my $old_costs = retrieve($old);
my $new_costs = retrieve($new);

my %keyhash  = ();

my @old_not_new = ();
my @new_not_old = ();

foreach my $key (keys %$old_costs) {
    if ($old_costs->{$key} == -1.00) {
	delete $old_costs->{$key};
    }
}

foreach my $key (keys %$new_costs) {
    if ($new_costs->{$key} == -1.00) {
	delete $new_costs->{$key};
    }
}

foreach my $key (keys %$old_costs) {
    if (exists $new_costs->{$key}) {
	$keyhash{$key} = 1;
    } else {
	push (@old_not_new, $key);
    } 
}

foreach my $key (keys %$new_costs) {
    if (! exists $old_costs->{$key}) {
	push (@new_not_old, $key);
    }
}

if (@old_not_new) {
    print("Warning: The following files are present in $old but not $new:\n");
    foreach my $f (@old_not_new) {
	print("    $f\n");
    }
    print("\n\n");
}
if (@new_not_old) {
    print("Warning: The following files are present in $new but not $old:\n");
    foreach my $f (@new_not_old) {
	print("    $f\n");
    }
    print("\n\n");
}


my @files = keys %keyhash;

sub print_sum_costs {
    my $files = shift;
    my $old_sum = 0;
    my $new_sum = 0;
    foreach my $f (@$files) {
	$old_sum += $old_costs->{$f};
	$new_sum += $new_costs->{$f};
    }
    my $col = (length($new) > length($old) ? length($new) : length($old))+1;
    
    printf("%-${col}s %10.2f sec\n%-${col}s %10.2f sec\n", "$old:", $old_sum, "$new:", $new_sum);
}

print "Total costs of files in both tables:\n";
print_sum_costs(\@files);
print "\n";

my @filt = ();
foreach my $f (@files) {
    if ($old_costs->{$f} > 5.0 || $new_costs->{$f} > 5.0) {
	push(@filt, $f);
    }
}

print "Costs of non-trivial files in both tables:\n";
print_sum_costs(\@filt);
print "\n";

sub speedup {
    my $file = shift;
    my $oldtime = $old_costs->{$file};
    my $newtime = $new_costs->{$file};
#    print "file $file: oldtime $oldtime newtime $newtime\n";
    my $linear = $oldtime/$newtime;
    if ($linear < 0) {
	# This is total nonsense but at least it's a clear error.
	return 999999;
    }
    else {
	return log($linear)/log(2);
    }
}

sub speedup_compare {
    my ($file1, $file2) = @_;
    return speedup($file1) <=> speedup($file2);
}

my @ordered = sort { speedup_compare($a, $b) } @filt;

my $max_chars = length("Files sorted by absolute speedup:");
foreach my $f (@files) {
    if ($max_chars < length($f)) {
	$max_chars = length($f);
    }
}

my $col2 = length($old);
if ($col2 < 10) {
    $col2 = 10;
}
my $col3 = length($new);
if ($col3 < 10) {
    $col3 = 10;
}
printf("%-${max_chars}s %${col2}s   %${col3}s   %10s\n", "Files sorted by speedup ratio:", $old, $new, "Log Speedup");
foreach my $f (@ordered) {
    my $oldtime = $old_costs->{$f};
    my $newtime = $new_costs->{$f};
    my $speedup = speedup($f);
    printf("%-${max_chars}s %${col2}.2f   %${col3}.2f   %11.2f\n", $f, $oldtime, $newtime, $speedup);
}
print "\n";

sub abs_speedup {
    my $file = shift;
    my $oldtime = $old_costs->{$file};
    my $newtime = $new_costs->{$file};
    return $oldtime - $newtime;
}

sub abs_speedup_compare {
   my ($file1, $file2) = @_;
   return abs_speedup($file1) <=> abs_speedup($file2);
}

my @ordered2 = sort { abs_speedup_compare($a, $b) } @ordered;

printf("%-${max_chars}s %${col2}s   %${col3}s   %10s\n", "Files sorted by absolute speedup:", $old, $new, "Abs Speedup");
foreach my $f (@ordered2) {
    my $oldtime = $old_costs->{$f};
    my $newtime = $new_costs->{$f};
    my $speedup = abs_speedup($f);
    printf("%-${max_chars}s %${col2}.2f   %${col3}.2f   %10.2f\n", $f, $oldtime, $newtime, $speedup);
}



    # file => (old_time, new_time)



