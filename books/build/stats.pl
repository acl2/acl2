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

use strict;
use warnings;
use Getopt::Long qw(:config bundling_override);
use FindBin qw($RealBin);
use lib "$RealBin/lib";
use Certlib;
use Bookscan;


my @targets = ();

GetOptions ("targets|t=s"   => sub { shift;
				     read_targets(shift, \@targets);
	    },
	    "<>"            => sub { push @targets, shift; }
    );

my @stats = ();

foreach my $book (@targets) {

    my @warnings = ();

    my $certtime = Certlib::get_cert_time($book, \@warnings, 0);

    my $lispfile = $book;
    $lispfile =~ s/\.cert$/\.lisp/;
    $lispfile =~ s/\.pcert0$/\.lisp/;
    $lispfile =~ s/\.pcert1$/\.lisp/;
    $lispfile =~ s/\.acl2x$/\.lisp/;
    my $events = scan_src_run($lispfile);

    my $mem = 0;
    foreach my $event (@$events) {
	my $type = $event->[0];
	if ($type eq set_max_mem_event) {
	    $mem = $event->[1];
	}
    }
    if ($certtime != -1) {
	push @stats, [$book, $certtime, $mem];
    }
}

# sort by memory descending
@stats = sort { $b->[2] <=> $a->[2] } @stats;

my $over64time = 0.0;
my $over32time = 0.0;
my $over16time = 0.0;
my $over8time = 0.0;
my $under8time = 0.0;
my $under8count = 0;
my $under1sec = 0;
my $under5sec = 0;
my $under20sec = 0;
my $under1min = 0;
my $under5min = 0;
my $under20min = 0;
my $under1hour = 0;
my $under5hour = 0;
my $over5hour = 0;
foreach my $entry (@stats) {
    my $book = $entry->[0];
    my $time = $entry->[1];
    my $mem = $entry->[2];
    print "$book:         $time sec   $entry->[2] gb\n";
    if ($mem > 64) {
	$over64time = $over64time + $time;
    } elsif ($mem > 32) {
	$over32time = $over32time + $time;
    } elsif ($mem > 16) {
	$over16time = $over16time + $time;
    } elsif ($mem > 8) {
	$over8time = $over8time + $time;
    } else {
	$under8time = $under8time + $time;
	$under8count++;
    }

    if ($time < 1.0) {
	$under1sec++;
    } elsif ($time < 5.0) {
	$under5sec++;
    } elsif ($time < 20.0) {
	$under20sec++;
    } elsif ($time < 60.0) {
	$under1min++;
    } elsif ($time < 60.0*5) {
	$under5min++;
    } elsif ($time < 60.0*20) {
	$under20min++;
    } elsif ($time > 60.0*60) {
	$under1hour++;
    } elsif ($time > 60.0*60*5) {
	$under5hour++;
    } else {
	$over5hour++;
    }
}

my $totaltime = $over64time + $over32time + $over16time + $over8time + $under8time;
print "\nTotal time: $totaltime sec\n";
print "Time using >64GB:        $over64time sec\n";
print "Time using >32GB, <64GB: $over32time sec\n";
print "Time using >16GB, <32GB: $over16time sec\n";
print "Time using >8GB, <16GB:  $over8time sec\n";
print "Time using <=8GB:        $under8time sec\n";

print "Jobs < 1 sec:                  $under1sec\n";
print "Jobs < 5 sec, > 1 sec:         $under5sec\n";
print "Jobs < 20 sec, > 5 sec:        $under20sec\n";
print "Jobs < 1 min, > 20 sec:        $under1min\n";
print "Jobs < 5 min, > 1 min:         $under5min\n";
print "Jobs < 20 min, > 5 min:        $under20min\n";
print "Jobs < 1 hour, > 20 min:       $under1hour\n";
print "Jobs < 5 hours, > 1 hour:      $under5hour\n";
print "Jobs over  5 hours:            $over5hour\n";

print "Jobs using < 8GB:              $under8count\n";


