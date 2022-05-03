# cert.pl build system
# Copyright (C) 2008-2014 Centaur Technology
# Copyright (C) 2022 Intel Corporation
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
# Original author: Sol Swords <sol.swords@intel.com>

package Critpath;
use strict;
use warnings;
use File::Basename;
use File::Spec;
use Storable qw(nstore retrieve);
use Cwd 'abs_path';
use Certlib;
use base 'Exporter';

our @EXPORT = qw(
read_costs
compute_cost_paths
find_most_expensive
compute_savings
warnings_report
critical_path_report
individual_files_report
deepest_path_report
parallelism_stats
human_time
read_build_log
costs_from_start_end_times
lagtime_stats
);



sub get_cert_time {

# Given a .cert file, gets the total user + system time recorded in the
# corresponding .time file.  If not found, prints a warning and returns 0.
# Given an .acl2x file, gets the time recorded in the corresponding
# .acl2x.time file.
    my ($path, $warnings, $use_realtime) = @_;

    $path =~ s/\.cert$/\.cert\.time/;
    $path =~ s/\.pcert0$/\.pcert0\.time/;
    $path =~ s/\.pcert1$/\.pcert1\.time/;
    $path =~ s/\.acl2x$/\.acl2x\.time/;

    if (open (my $timefile, "<", $path)) {

	# The following while loop works for GNU time, but 
	# we now prefer one that works with the POSIX standard instead.
	# while (my $the_line = <$timefile>) {
	#     my $regexp = "^([0-9]*\\.[0-9]*)user ([0-9]*\\.[0-9]*)system";
	#     my @res = $the_line =~ m/$regexp/;
	#     if (@res) {
	# 	close $timefile;
	# 	return 0.0 + $res[0] + $res[1];
	#     }
	
	# Should we go by user+system or just real time?
	my $usertime;
	my $systime;
	my $realtime;
	while (my $the_line = <$timefile>) {
	    my @res = $the_line =~ m/^(\S*)\s*([0-9]*)m([0-9]*\.[0-9]*)s/;
	    if (@res) {
		# print "$res[0]_$res[1]_$res[2]\n";
		my $secs = 60*$res[1] + $res[2];
		if ($res[0] eq "user") {
		    $usertime = $secs;
		} elsif ($res[0] eq "sys") {
		    $systime = $secs;
		} elsif ($res[0] eq "real") {
		    $realtime = $secs;
		}
	    }
	}
	close $timefile;
	if (!defined($usertime) || !defined($systime)) {
	    push(@$warnings, "Corrupt timings in $path\n");
	    return -1;
	}
	if ($use_realtime) {
	    return 0.0 + $realtime;
	} else {
	    return 0.0 + $usertime + $systime;
	}
    } else {
	# carp("Could not open $path: $!\n");
	push(@$warnings, "Could not open $path: $!\n");
	return -1;
    }
}


sub read_costs {
    my ($depdb, $basecosts, $warnings, $use_realtime) = @_;

    foreach my $certfile (keys %{$depdb->certdeps}) {
	$basecosts->{$certfile} = get_cert_time($certfile, $warnings, $use_realtime);
	if ($depdb->cert_get_param($certfile, "acl2x")) {
	    my $acl2xfile = cert_to_acl2x($certfile);
	    $basecosts->{$acl2xfile} = get_cert_time($acl2xfile, $warnings, $use_realtime);
	} elsif ($depdb->cert_get_param($certfile, "pcert") || $Certlib::pcert_all) {
	    my $pcert1file = cert_to_pcert1($certfile);
	    $basecosts->{$pcert1file} = get_cert_time($pcert1file, $warnings, $use_realtime);
	    my $pcert0file = cert_to_pcert0($certfile);
	    $basecosts->{$pcert0file} = get_cert_time($pcert0file, $warnings, $use_realtime);
	}
    }
}


sub get_end_time {
    my ($target, $start_end_times) = @_;
    my $start_end = $start_end_times->{$target};
    if (! $start_end) {
	# print("no start_end target $target\n");
	# print("database:\n");
	# foreach my $fname (keys %$start_end_times) {
	#     print("$fname start " . $start_end_times->{$fname}->[0] . " finish " . $start_end_times->{$fname}->[1] . "\n");
	# }
	
	return 0;
    }
    # print("endtime " . $start_end->[1] . " target $target\n");
    return $start_end->[1];
}

sub get_end_time_bounded {
   my ($target, $minimum, $start_end_times) = @_;
   my $endtime1 = get_end_time($target, $start_end_times);
   if ((! $endtime1) || ($endtime1 < $minimum)) {
       # print("endtime minimum " . $minimum . " target $target\n");
       return $minimum;
   }
   # print("endtime bounded " . $endtime1 . " target $target\n");
   return $endtime1;
}

sub max_dep_endtime {
    my ($target, $depdb, $begin_time, $start_end_times) = @_;

    my $deps = cert_target_deps($depdb, $target);
    my $starttime = $begin_time;
    foreach my $dep (@$deps) {
	# print("$target -> $dep\n");
	$starttime = get_end_time_bounded($dep, $starttime, $start_end_times);
    }
    # print("max dep endtime " . $starttime . " target $target\n");
    return $starttime;
}

sub target_time_from_start_end_times {
    my ($target, $depdb, $begin_time, $start_end_times) = @_;
    my $endtime = get_end_time($target, $start_end_times);
    if ($endtime) {
	# To find starttime, get max endtime from dependencies.
	my $starttime = max_dep_endtime($target, $depdb, $begin_time, $start_end_times);
	# print("time " . ($endtime - $starttime) . " target $target\n");
	return $endtime - $starttime;
    } else {
	return -1;
    }
}

sub costs_from_start_end_times {
    my ($depdb, $begin_time, $start_end_times, $basecosts) = @_;

    foreach my $target (keys %{$depdb->certdeps}) {
	$basecosts->{$target} = target_time_from_start_end_times($target, $depdb, $begin_time, $start_end_times);
	if ($depdb->cert_get_param($target, "acl2x")) {
	    my $acl2xfile = cert_to_acl2x($target);
	    $basecosts->{$acl2xfile} = target_time_from_start_end_times($acl2xfile, $depdb, $begin_time, $start_end_times);
	} elsif ($depdb->cert_get_param($target, "pcert") || $Certlib::pcert_all) {
	    my $pcert1file = cert_to_pcert1($target);
	    my $pcert0file = cert_to_pcert0($target);	
	    $basecosts->{$pcert1file} = target_time_from_start_end_times($pcert1file, $depdb, $begin_time, $start_end_times);
	    $basecosts->{$pcert0file} = target_time_from_start_end_times($pcert0file, $depdb, $begin_time, $start_end_times);
	}
    }
    return $basecosts;
}


# Relevant lines of the build log are:
# Beginning build at 03-Mar-2022 08:15:02.244386355 [1646324102.244386355]
# Making /path/to/acl2/books/std/portcullis.cert on 03-Mar-2022 08:15:02.282 [1646324102.282]
# Built /path/to/acl2/books/std/portcullis.cert (0.244s) at 03-Mar-2022 08:15:02.537 [1646324102.537] 
# This takes a substring such as [1646324102.282] or [1646324102.244386355] and just returns
# the value up to milliseconds.
# Note: fails on negative timestamps -- no dates before 1970, please!
sub parse_build_log_timestamp {
    my ($stamp) = @_;
    # print("parse $stamp\n");
    my ($int, $dec) = $stamp =~ m{\[([0-9]*)\.([0-9]{3})[0-9]*\]};
    return int($int) + ($dec/1000.0);
}

sub read_build_log {
    my ($logpath) = @_;

    my %filetimes = ();
    my $begin_time = 0;
    
    if (open (my $log, "<", $logpath)) {
	while (my $the_line = <$log>) {
	    # Remove ANSI color sequences first -- magic regex
	    $the_line =~ s/\e\[\d+(?>(;\d+)*)m//g;
	    my @match;
	    if (@match = $the_line =~
		m{^Making \s
		(\S*) # note no whitespace allowed in filenames
		\s on \s [^[]* # skip til square bracket for timestamp
		(\[[0-9]+\.[0-9]+\])
		}x)
	    {
		my ($full_fname, $tstamp) = @match;
	        # print("Making line: " . $full_fname . $tstamp . "\n");
		my $fname = canonical_path($full_fname);
		my $time = parse_build_log_timestamp($tstamp);
		# print ("Making $fname $time\n");
		if (exists $filetimes{$fname}) {
		    $filetimes{$fname}->[0] = $time;
		} else {
		    $filetimes{$fname} = [ $time, 0 ];
		}
	    } elsif (@match = $the_line =~
		       m{^Built \s
		       (\S*)       # filename, no spaces
		       \s \( [^[]* # skip til square bracket for timestamp
		       (\[[0-9]+\.[0-9]+\])
		       }x)
	    {
		my ($full_fname, $tstamp) = @match;
		my $fname = canonical_path($full_fname);
		my $time = parse_build_log_timestamp($tstamp);
		# print ("Built $fname $time\n");
		if (exists $filetimes{$fname}) {
		    $filetimes{$fname}->[1] = $time;
		} else {
		    $filetimes{$fname} = [ 0, $time ];
		}
	    } elsif (@match = $the_line =~
		       m{^Beginning \s build \s at \s [^[]* # skip to open bracket
		       (\[[0-9]+\.[0-9]+\])
		       }x)
	    {
		my ($tstamp) = @match;
		$begin_time = parse_build_log_timestamp($tstamp);
		# print ("Beginning $begin_time\n");
	    }
	}
    } else {
	die("Couldn't open $logpath\n");
    }
    # foreach my $fname (keys %filetimes) {
    # 	print("$fname start " . $filetimes{$fname}->[0] . " finish " . $filetimes{$fname}->[1] . "\n");
    # }
    return ( $begin_time, \%filetimes );
}




sub find_most_expensive {
    # horrible: updateds is either 1 or a reference to a hash holding the names of updated targets.
    my ($files, $costs, $updateds) = @_;

    my $most_expensive_file_total = 0;
    my $most_expensive_file = 0;

    foreach my $file (@{$files}) {
	if ($file =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
	    if (($updateds==1) || $updateds->{$file}) {
		my $file_costs = $costs->{$file};
		if ($file_costs) {
		    my $this_file_total = $file_costs->{"totaltime"};
		    if ($this_file_total > $most_expensive_file_total) {
			$most_expensive_file = $file;
			$most_expensive_file_total = $this_file_total;
		    }
		}
	    }
	}
    }

    return ($most_expensive_file, $most_expensive_file_total);
}

sub find_max_depth {
    # horrible: updateds is either 1 or a reference to a hash holding the names of updated targets.
    my ($files, $costs, $updateds) = @_;

    my $deepest_file_total = 0;
    my $deepest_file = 0;

    foreach my $file (@{$files}) {
	if ($file =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
	    if (($updateds==1) || $updateds->{$file}) {
		my $file_costs = $costs->{$file};
		if ($file_costs) {
		    my $this_file_depth = $file_costs->{"depth"};
		    if ($this_file_depth > $deepest_file_total) {
			$deepest_file = $file;
			$deepest_file_total = $this_file_depth;
		    }
		}
	    }
	}
    }

    return ($deepest_file, $deepest_file_total);
}

sub compute_cost_paths_aux {
    # horrible: updateds is either 1 or a reference to a hash holding the names of updated targets.
    my ($target,$depdb,$basecosts,$costs,$updateds,$warnings) = @_;

    if (exists $costs->{$target} || ! ($target =~ /\.(cert|acl2x|pcert0|pcert1)$/)) {
	return $costs->{$target};
    }

    # put something in $costs->{$target} so that we don't loop
    $costs->{$target} = 0;
    # print("DFS starting for $target\n");

    my $certtime = $basecosts->{$target};
    if (! defined $certtime) {
	# Probably the .lisp file doesn't exist
	my %entry = ( "totaltime" => 0.0,
		      "maxpath" => "ERROR",
	              "depth" => 0,
                      "maxdepthpath" => "ERROR");
	$costs->{$target} = \%entry;
	return $costs->{$target};
    }
    
    my $targetdeps;
    $targetdeps = [];
    if ($target =~ /\.pcert0$/) {
	## The dependencies are the dependencies of the cert file, but
	## with each .cert replaced with the corresponding sequential_dep.
	(my $certfile = $target) =~ s/\.pcert0$/\.cert/;
	my $certdeps = $depdb->cert_deps($certfile);
	foreach my $dep (@$certdeps) {
	    my $deppcert = $depdb->cert_sequential_dep($dep);
	    push(@$targetdeps, $deppcert);
	}
    } elsif ($target =~ /\.pcert1$/) {
	(my $certfile = $target) =~ s/\.pcert1$/\.cert/;
	(my $pcert0 = $target) =~ s/\.pcert1$/\.pcert0/;
	push (@$targetdeps, $pcert0);
    } elsif ($target =~ /\.acl2x$/) {
	## The dependencies are the dependencies of the cert file.
	(my $certfile = $target) =~ s/\.acl2x$/\.cert/;
	my $certdeps = $depdb->cert_deps($certfile);
	push(@$targetdeps, @$certdeps);
    } else {
	# $target =~ /\.cert$/
	# Depends.
	if ($depdb->cert_get_param($target, "acl2x")) {
	    # If it's using the acl2x/two-pass, then depend only on the acl2x file.
	    (my $acl2xfile = $target) =~ s/\.cert$/\.acl2x/;
	    push (@$targetdeps, $acl2xfile);
	} else {
	    # otherwise, depend on its subbooks' certificates and the pcert1, if applicable.
	    push (@$targetdeps, @{$depdb->cert_deps($target)});
	    if ($depdb->cert_get_param($target, "pcert") || $Certlib::pcert_all) {
		(my $pcert1 = $target) =~ s/\.cert$/\.pcert1/;
		push (@$targetdeps, $pcert1);
	    }
	}
    }

    my $most_expensive_dep = 0;
    my $most_expensive_dep_total = 0;
    my $updated = ($updateds==1) || $updateds->{$target} || 0;

#    print "$target depends on @$targetdeps\n";
    if (@$targetdeps) {
	foreach my $dep (@$targetdeps) {
	    if ($dep =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
		my $this_dep_costs = compute_cost_paths_aux($dep, $depdb, $basecosts, $costs, $updateds, $warnings);
		if (($updateds == 1) || $updateds->{$dep}) {
		    if (! $this_dep_costs) {
			if ($dep eq $target) {
			    push(@{$warnings}, "Self-dependency in $dep");
			} else {
			    push(@{$warnings}, "Dependency loop involving $dep and $target");
			}
		    }
		    $updated = 1;
		}
	    }
	}
    }
    # if (! defined $most_expensive_dep_total) {
    # 	carp("Most_expensive_dep undefined for $target\n");
    # } elsif (! defined $certtime) {
    # 	carp("Certtime undefined for $target\n");
    # }
    # print("DFS ending for $target -- updated $updated\n");

    if ($updated) {
	($most_expensive_dep, $most_expensive_dep_total) = find_most_expensive($targetdeps, $costs, $updateds);
	(my $deepest_dep, my $dep_depth) = find_max_depth($targetdeps, $costs, $updateds);
	my %entry = ( "totaltime" => $most_expensive_dep_total + $certtime, 
		      "maxpath" => $most_expensive_dep,
                      "depth" => $dep_depth + 1,
	              "maxdepthpath" => $deepest_dep );
	$costs->{$target} = \%entry;
	if ($updateds != 1) {
	    $updateds->{$target} = 1;
	}
	return $costs->{$target};
    }
}

sub compute_cost_paths {
    my ($depdb,$basecosts,$costs,$updateds,$warnings) = @_;
    foreach my $certfile (keys %{$depdb->certdeps}) {
	compute_cost_paths_aux($certfile, $depdb, $basecosts, $costs, $updateds, $warnings);
    }
    foreach my $certfile (keys %{$costs}) {
	if ($costs->{$certfile} == 0) {
	    delete $costs->{$certfile};
	}
    }
}



sub warnings_report {

# warnings_report(warnings, htmlp) returns a string describing any warnings
# which were encountered during the generation of the costs table, such as for
# missing .time files.
    my ($warnings,$htmlp) = @_;

    unless (@$warnings) {
	return "";
    }

    my $ret;

    if ($htmlp) {
	$ret = "<dl class=\"critpath_warnings\">\n"
	     . "<dt>Warnings</dt>\n";
	foreach (@$warnings) {
	    chomp($_);
	    $ret .= "<dd>$_</dd>\n";
	}
	$ret .= "</dl>\n\n";
    }

    else  {
	$ret = "Warnings:\n\n";
	foreach (@$warnings) {
	    chomp($_);
	    $ret .= "$_\n";
	}
	$ret .= "\n\n";
    }

    return $ret;
}



sub human_time {

# human_time(secs,shortp) returns a string describing the time taken in a
# human-friendly format, e.g., 5.6 minutes, 10.3 hours, etc.  If shortp is
# given, then we use, e.g., "min" instead of "minutes."

    my $secs = shift;
    my $shortp = shift;

    if (! defined($secs) || $secs < 0.0) {
	return "[Error]";
    }

    if ($secs < 60) {
	return sprintf("%.1f %s", $secs, $shortp ? "sec" : "seconds");
    }

    if ($secs < 60 * 60) {
	return sprintf("%.1f %s", ($secs / 60.0), $shortp ? "min" : "minutes");
    }

    return sprintf("%.2f %s", ($secs / (60 * 60)), $shortp ? "hr" : "hours");
}


sub short_cert_name {

# Given a path to some ACL2 book, e.g., foo/bar/baz/blah.cert, we produce 
# a shortened version of the name, e.g., "baz/blah.cert".  Usually this is 
# enough to identify the book, and keeps the noise of the path down to a 
# minimum.

    my $certfile = shift;
    my $short = shift;

    if ($short == -1) {
	return $certfile;
    }
    
    my $pos = length($certfile)+1;

    while ($short > -1) {
	$pos = rindex($certfile, "/", $pos-1);
	if ($pos == -1) {
	    return $certfile;
	}
	$short = $short-1;
    }
    return substr($certfile, $pos+1);

}

sub linepairs_to_str {
    # input is a list of pairs [ linestart, linerest ]
    # calculates the max linestart length and formats each line with
    # linestart left-justified in a field of that length.
    my ($linepairs) = @_;
    my $ret = "";
    my $maxwidth = 0;
    foreach my $pair (@$linepairs) {
	my $len = length($pair->[0]);
	$maxwidth = ($maxwidth < $len) ? $len : $maxwidth;
    }
    my $filewidth = $maxwidth+1;
    my $fmt = "%-${maxwidth}s%s";
    foreach my $pair (@$linepairs) {
	$ret .= sprintf($fmt, $pair->[0], $pair->[1]);
    }
    return $ret;
}


sub critical_path_report {

# critical_path_report(costs,htmlp) returns a string describing the
# critical path for file according to the costs_table, either in TEXT or HTML
# format per the value of htmlp.
    my ($costs,$basecosts,$start_end_times,$savings,$topfile,$htmlp,$short) = @_;


    my $ret;
    my $linepairs;
    my $have_starttimes = scalar keys %$start_end_times;
    
    if ($htmlp) {
	$ret = "<table class=\"critpath_table\">\n"
	     . "<tr class=\"critpath_head\">"
	     . "<th>Critical Path</th>" 
	     . "<th>Time</th>"
	     . "<th>Cumulative</th>"
	     . "</tr>\n";
    } else {
	$ret = "Critical Path\n\n";
	if ($have_starttimes) {
	    $linepairs = [["File", sprintf("%10s %10s %10s %10s %10s\n", "Cumulative", "Time", "Speedup", "Remove", "Lag")]];
	} else {
	    $linepairs = [["File", sprintf("%10s %10s %10s %10s\n", "Cumulative", "Time", "Speedup", "Remove")]];
	}
    }

    my $file = $topfile;
    my $lagtime_total = 0.0;
    my $count = 0;
    while ($file) 
    {
	my $filecosts = $costs->{$file};
	my $shortcert = short_cert_name($file, $short);
	my $selftime = $basecosts->{$file};
	my $cumtime = $filecosts->{"totaltime"};
	my $filesavings = $savings->{$file};
	my $sp_savings = $filesavings->{"speedup"};
	my $rem_savings = $filesavings->{"remove"};

	my $selftime_pr = human_time($selftime, 1);
	my $cumtime_pr = human_time($cumtime, 1);
	my $spsav_pr = human_time($sp_savings, 1);
	my $remsav_pr = human_time($rem_savings, 1);

	if ($htmlp) {
	    $ret .= "<tr class=\"critpath_row\">"
	 	 . "<td class=\"critpath_name\">$shortcert</td>"
		 . "<td class=\"critpath_self\">$selftime_pr</td>"
		 . "<td class=\"critpath_total\">$cumtime_pr</td>"
		 . "</tr>\n";
	}
	else {
	    my $vals;
	    if ($have_starttimes) {
		# Selftime stores the difference between our end time
		# and the latest end time of a dependency.
		# Comparing that to the difference between our end
		# time and start time can indicate various
		# inefficiencies in the build system.
		my $lagtime_pr = "[Error]";
		if (exists $start_end_times->{$file}) {
		    ( my $start, my $end ) = @{$start_end_times->{$file}};
		    my $lagtime = $selftime - ($end - $start);
		    $lagtime_total += $lagtime;
		    $lagtime_pr = human_time($lagtime, 1);
		}
		$vals = sprintf("%10s %10s %10s %10s %10s\n", $cumtime_pr, $selftime_pr, $spsav_pr, $remsav_pr, $lagtime_pr);
	    } else {
		$vals = sprintf("%10s %10s %10s %10s\n", $cumtime_pr, $selftime_pr, $spsav_pr, $remsav_pr);
	    }
	    push(@$linepairs, [$shortcert, $vals]);
	}
	$count += 1;
	$file = $filecosts->{"maxpath"};
    }
    if ($htmlp) {
	$ret .= "</table>\n\n";
    }
    else {
	# compute the width
	$ret .= linepairs_to_str($linepairs);
	if ($have_starttimes) {
	    $ret .= "\n";
	    $ret .= sprintf("Critical path total lagtime: %s\n", human_time($lagtime_total));
	    $ret .= sprintf("Critical path average lagtime: %s\n", human_time($lagtime_total/$count));
	}
	$ret .= "\n\n";
    }

    return $ret;
}

sub deepest_path_report {

# deepest_path_report(costs,htmlp) returns a string describing the
# deepest path for file according to the costs_table, either in TEXT or HTML
# format per the value of htmlp.
    my ($costs,$basecosts,$savings,$topfile,$htmlp,$short) = @_;


    my $ret;
    my $linepairs;
    if ($htmlp) {
	$ret = "<table class=\"critpath_table\">\n"
	     . "<tr class=\"critpath_head\">"
	     . "<th>Deepest Path</th>" 
	     . "<th>Time</th>"
	     . "<th>Cumulative</th>"
	     . "</tr>\n";
    }
    else {
	$ret = "Deepest Path\n\n";
	$linepairs = [["File", sprintf("%10s %10s %10s %10s\n", "Cumulative", "Time", "Speedup", "Remove")]];
    }

    my $file = $topfile;
    while ($file) 
    {
	my $filecosts = $costs->{$file};
	my $shortcert = short_cert_name($file, $short);
	my $selftime = $basecosts->{$file};
	my $cumtime = $filecosts->{"totaltime"};
	my $filesavings = $savings->{$file};
	my $sp_savings = $filesavings->{"speedup"};
	my $rem_savings = $filesavings->{"remove"};

	my $selftime_pr = human_time($selftime, 1);
	my $cumtime_pr = human_time($cumtime, 1);
	my $spsav_pr = human_time($sp_savings, 1);
	my $remsav_pr = human_time($rem_savings, 1);

	if ($htmlp) {
	    $ret .= "<tr class=\"critpath_row\">"
	 	 . "<td class=\"critpath_name\">$shortcert</td>"
		 . "<td class=\"critpath_self\">$selftime_pr</td>"
		 . "<td class=\"critpath_total\">$cumtime_pr</td>"
		 . "</tr>\n";
	}
	else {
	    push(@$linepairs,
		 [$shortcert, sprintf("%10s %10s %10s %10s\n", $cumtime_pr, $selftime_pr, $spsav_pr, $remsav_pr)]);
	}

	$file = $filecosts->{"maxdepthpath"};
    }

    if ($htmlp) {
	$ret .= "</table>\n\n";
    }
    else {
	$ret .= linepairs_to_str($linepairs);
	$ret .= "\n\n";
    }

    return $ret;
}

	
sub classify_book_time {
    
# classify_book_time(secs) returns "low", "med", or "high".

    my $time = shift;

    return "err" if !$time;
    return "low" if ($time < 30);
    return "med" if ($time < 120);
    return "high";
}


sub individual_files_report {

# individual_files_report(costs,htmlp) returns a string describing the
# self-times of each file in the costs_table, either in either TEXT or HTML
# format, per the value of htmlp.
    my ($costs,$basecosts,$start_end_times,$htmlp,$short) = @_;

    my @sorted = reverse sort { ($costs->{$a}->{"totaltime"} + 0.0) <=> ($costs->{$b}->{"totaltime"} + 0.0) } keys(%{$costs});
    my $ret;
    my $linepairs;
    my $have_starttimes = scalar keys %$start_end_times;
    
    if ($htmlp) 
    {
	$ret = "<table class=\"indiv_table\">\n"
	     . "<tr class=\"indiv_head\"><th>All Files</th> <th>Cumulative</th> <th>Self</th></tr>\n";
    } else {
	$ret = "Individual File Times\n\n";
	if ($have_starttimes) {
	    $linepairs = [["File", sprintf("%10s %10s %10s --->  %-50s\n", "Cumulative", "Time", "Lag", "Dependency")]];
	} else {
	    $linepairs = [["File", sprintf("%10s %10s  --->  %-50s\n", "Cumulative", "Time", "Dependency")]];
	}
    }


    foreach my $name (@sorted)
    {
	my $entry = $costs->{$name};
	my $shortname = short_cert_name($name, $short);
	my $cumul = human_time($entry->{"totaltime"}, 1);
	my $time = human_time($basecosts->{$name}, 1);
	my $depname = $entry->{"maxpath"} ? short_cert_name($entry->{"maxpath"}, $short) : "[None]";
	my $timeclass = classify_book_time($basecosts->{$name});

	if ($htmlp)
	{
	    $ret .= "<tr class=\"indiv_row\">";
	    $ret .= "<td class=\"indiv_file\">";
	    $ret .= "  <span class=\"indiv_file_name\">$shortname</span><br/>";
	    $ret .= "  <span class=\"indiv_crit_dep\">--> $depname</span>";
	    $ret .= "</td>";
	    $ret .= "<td class=\"indiv_cumul\">$cumul</td>";
	    $ret .= "<td class=\"indiv_time_$timeclass\">$time</td>";
	    $ret .= "</tr>\n";
	} else {
	    my $vals;
	    if ($have_starttimes) {
		# See comment about lagtime in critical_path_report
		my $lagtime = "[Error]";
		if (exists $start_end_times->{$name}) {
		    ( my $start, my $end ) = @{$start_end_times->{$name}};
		    $lagtime = human_time($basecosts->{$name} - ($end - $start), 1);
		}
		$vals = sprintf("%10s %10s %10s --->  %-50s\n", $cumul, $time, $lagtime, $depname);
	    } else {
		$vals = sprintf("%10s %10s  --->  %-50s\n", $cumul, $time, $depname);
	    }
	    push(@$linepairs, [$shortname, $vals]);
	}
    }
    
    if ($htmlp)
    {
	$ret .= "</table>\n\n";
    } else {
	$ret .= linepairs_to_str($linepairs);
	$ret .= "\n\n";
    }

    return $ret;
}   


my $start = "start";
my $end = "end";

sub parallelism_stats {
    my ($costs, $basecosts) = @_;

    # costs: table mapping filename to totaltime, maxpath
    # basecosts: table mapping filename to immediate cost

    # collect up a list of key/val pairs (time, start_or_finish)
    my @starts_ends = ();
    my $running_total = 0;
    foreach my $key (keys %$basecosts) {
	my $selfcost = (exists $basecosts->{$key}) ? $basecosts->{$key} : 0.0 ;
	$selfcost = ($selfcost >= 0) ? $selfcost : 0.0;
	$running_total = $running_total + $selfcost;
	my $totalcost = (exists $costs->{$key}) ? $costs->{$key}->{"totaltime"} : 0.0;
	push (@starts_ends, [$totalcost-$selfcost, $start]);
	push (@starts_ends, [$totalcost, $end]);
    }

    @starts_ends = sort { ( $a->[0] <=> $b->[0] ) || 
			      (($a->[1] eq $start) ?
			       (($b->[1] eq $start) ? 0 : 1) :
			       (($b->[1] eq $start) ? -1 : 0)) } @starts_ends;



    my $max_parallel = 0;
    my $max_start_time = 0.0;
    my $max_end_time = 0.0;
    my $curr_parallel = 0;
    my $lasttime = 0.0;
    foreach my $entry (@starts_ends) {
	(my $time, my $event) = @$entry;

	if ($event eq $start) {
	    $curr_parallel = $curr_parallel + 1;
	} else {
	    if ($curr_parallel > $max_parallel) {
		$max_parallel = $curr_parallel;
		$max_start_time = $lasttime;
		$max_end_time = $time;
	    }
	    $curr_parallel = $curr_parallel - 1;
	}
	$lasttime = $time;
    }
    if ($curr_parallel != 0) {
	print STDERR "Error: Ended with jobs still running??\n"
    }
    my $avg_parallel = ($lasttime != 0) ? $running_total / $lasttime : "???";

    return ($max_parallel, $max_start_time, $max_end_time, $avg_parallel, $running_total);
}


sub compute_savings
{
    my ($costs,$basecosts,$targets,$updateds,$debug,$depdb) = @_;

    (my $topbook, my $topbook_cost) = find_most_expensive($targets, $costs, $updateds);

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

	# Get the max savings from speeding up the book:
	# set the file base cost to 0 and recompute crit path.
	my %tmpcosts = ();
	my @tmpwarns = ();
	$basecosts->{$critfile} = 0.0;
	compute_cost_paths($depdb, $basecosts, \%tmpcosts, $updateds, \@tmpwarns);
	(my $tmptop, my $tmptopcost) = find_most_expensive($targets, \%tmpcosts, $updateds);
	my $speedup_savings = $topbook_cost - $tmptopcost;
	$speedup_savings = $speedup_savings || 0.000001;

	# Get the max savings from removing the book:
	# set the file total cost to 0 and recompute crit path.
	%tmpcosts = ();
	$tmpcosts{$critfile} = 0;
	compute_cost_paths($depdb, $basecosts, \%tmpcosts, $updateds, \@tmpwarns);
	($tmptop, $tmptopcost) = find_most_expensive($targets, \%tmpcosts, $updateds);
	my $remove_savings = $topbook_cost - $tmptopcost;
	$remove_savings = $remove_savings || 0.000001;

	my %entry = ( "speedup" => $speedup_savings,
		      "remove" => $remove_savings );
	$savings{$critfile} = \%entry;
	$basecosts->{$critfile} = $filebasecost;
    }

    return \%savings;
}

sub lagtime_stats {
    my ($basecosts, $start_end_times) = @_;
    my $total_lag = 0.0;
    my $count = 0;
    foreach my $target (keys %$basecosts) {
	my $selftime = $basecosts->{$target};
	if (exists $start_end_times->{$target}) {
	    ( my $start, my $end ) = @{$start_end_times->{$target}};
	    my $lagtime = $selftime - ($end - $start);
	    $total_lag += $lagtime;
	    $count += 1;
	}
    }
    if ($count == 0) {
	return [ 0, 0 ];
    }
    return [ $total_lag, $total_lag / $count ];
}
