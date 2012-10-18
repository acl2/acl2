# certlib.pl - Library routines for cert.pl, critpath.pl, etc.
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


use strict;
use warnings;
use File::Basename;
use File::Spec;
use Storable;
# use Cwd;
use Cwd 'abs_path';

my $cache_version_code = 3;

# Note: for debugging you can enable this use and then print an error message
# using
#       carp "Description of the error\n";
# and you get a backtrace as well.
use Carp;

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




sub rel_path {
# Composes two paths together.  Basically just builds "$base/$path"
# but handles the special cases where $base is empty or $path is
# absolute.
    my $base = shift;
    my $path = shift;
    if (substr($path,0,1) eq "/" || !$base) {
	return $path;
    } else {
	return "$base/$path";
    }
}

sub rec_readlink {
    my $path = shift;
    while (-l $path) {
	$path = readlink $path;
    }
    return $path;
}


sub abs_canonical_path {
    my $path = shift;
    my $abspath = File::Spec->rel2abs(rec_readlink($path));
    my ($vol, $dir, $file) = File::Spec->splitpath($abspath);
    if (! -d $dir) {
	print "Oops, trying to go into $dir\n";
	return 0;
    }
    my $absdir = Cwd::fast_abs_path($dir);
    if ($absdir) {
	return File::Spec->catpath($vol, $absdir, $file);
    } else {
	print "Warning: canonical_path: Directory not found: " . $dir . "\n";
	return 0;
    }
}

my $BASE_PATH = abs_canonical_path(".");

my %canonical_path_memo = ();

sub canonical_path {
    my $fname = shift;
    my $entry = $canonical_path_memo{$fname};
    if ($entry) {
	return $entry;
    } else {
	my $res;
	my $abs_path = abs_canonical_path($fname);
	if ($BASE_PATH && $abs_path) {
	    my $relpath =  File::Spec->abs2rel($abs_path, $BASE_PATH);
	    $res = $relpath ? $relpath : ".";
	} else {
	    $res = $abs_path;
	}
	$canonical_path_memo{$fname} = $res;
	return $res;
    }
}

sub which {
    my $name = shift;
    # test to see if this is just a filename with no directory -- is this correct?
    if (basename($name) eq $name) {
	foreach my $dir (split(":", $ENV{"PATH"})) {
	    my $file = rel_path($dir, $name);
	    if ((! -d $file) && -x $file) {
		return abs_canonical_path($file);
	    }
	}
    } elsif ((! -d $name) && -x $name) {
	return abs_canonical_path($name);
    }
    return 0;
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


sub get_cert_time {

# Given a .cert file, gets the total user + system time recorded in the
# corresponding .time file.  If not found, prints a warning and returns 0.
# Given an .acl2x file, gets the time recorded in the corresponding
# .acl2x.time file.
    my ($path, $warnings, $use_realtime, $pcert) = @_;

    if ($pcert) {
	$path =~ s/\.cert$/\.cert\.time/;
	$path =~ s/\.pcert0$/\.pcert0\.time/;
	$path =~ s/\.pcert1$/\.pcert1\.time/;
	$path =~ s/\.acl2x$/\.acl2x\.time/;
    } else {
	$path =~ s/\.cert$/\.cert\.time/;
	$path =~ s/\.acl2x$/\.acl2x\.time/;
    }

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

sub cert_to_acl2x {
    my $cert = shift;
    (my $acl2x = $cert) =~ s/\.cert$/\.acl2x/;
    return $acl2x;
}

sub cert_to_pcert0 {
    my $cert = shift;
    (my $pcert = $cert) =~ s/\.cert$/\.pcert0/;
    return $pcert;
}

sub cert_to_pcert1 {
    my $cert = shift;
    (my $pcert = $cert) =~ s/\.cert$/\.pcert1/;
    return $pcert;
}

sub cert_bookdeps {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry ? $entry->[0] ? $entry->[0] : [] : [];
}

sub cert_portdeps {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry ? $entry->[1] ? $entry->[1] : [] : [];
}

sub cert_deps {
    my ($cert, $depmap) = @_;
    my $bookdeps = cert_bookdeps($cert, $depmap);
    my $portdeps = cert_portdeps($cert, $depmap);
    return [ @$bookdeps, @$portdeps ];
}

sub cert_srcdeps {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[2];
}

sub cert_otherdeps {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[3];
}

sub cert_image {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[4];
}

sub cert_get_params {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[5];
}

sub cert_get_param {
    my ($cert, $depmap, $param) = @_;
    my $params = cert_get_params($cert, $depmap);
    return $params && $params->{$param};
}

sub cert_is_two_pass {
    my ($certfile, $deps) = @_;
    return cert_get_param($certfile, $deps, "two_pass");
}

sub cert_sequential_dep {
    my ($certfile, $deps) = @_;
    my $res;
    if (cert_get_param($certfile, $deps, "acl2x")
	|| cert_get_param($certfile, $deps, "no_pcert")) {
	($res = $certfile) =~ s/\.cert$/\.pcert1/;
    } else {
	($res = $certfile) =~ s/\.cert$/\.pcert0/;
    }
    return $res;
}


sub read_costs {
    my ($deps, $basecosts, $warnings, $use_realtime, $pcert) = @_;

    foreach my $certfile (keys %{$deps}) {
	if ($pcert) {
	    my $pcert1file = cert_to_pcert1($certfile);
	    $basecosts->{$certfile} = get_cert_time($certfile, $warnings, $use_realtime, $pcert);
	    $basecosts->{$pcert1file} = get_cert_time($pcert1file, $warnings, $use_realtime, $pcert);
	    if (! cert_get_param($certfile, $deps, "no_pcert")
		&& ! cert_get_param($certfile, $deps, "acl2x")) {
		# print "file: $certfile no_pcert: " . cert_get_param($certfile, $deps, "no_pcert") . "\n";
		my $pcert0file = cert_to_pcert0($certfile);
		$basecosts->{$pcert0file} = get_cert_time($pcert0file, $warnings, $use_realtime, $pcert);
	    }
	} else {
	    $basecosts->{$certfile} = get_cert_time($certfile, $warnings, $use_realtime, $pcert);
	    if (cert_get_param($certfile, $deps, "acl2x")) {
		my $acl2xfile = cert_to_acl2x($certfile);
		$basecosts->{$acl2xfile} = get_cert_time($acl2xfile, $warnings, $use_realtime, $pcert);
	    }
	}
    }
}

sub find_most_expensive {
    my ($files, $costs) = @_;

    my $most_expensive_file_total = 0;
    my $most_expensive_file = 0;

    foreach my $file (@{$files}) {
	if ($file =~ /\.(cert|acl2x|pcert0|pcert1)$/) {

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

    return ($most_expensive_file, $most_expensive_file_total);
}

sub compute_cost_paths_aux {
    my ($target,$deps,$basecosts,$costs,$warnings,$pcert) = @_;

    if (exists $costs->{$target} || ! ($target =~ /\.(cert|acl2x|pcert0|pcert1)$/)) {
	return $costs->{$target};
    }

    # put something in $costs->{$target} so that we don't loop
    $costs->{$target} = 0;

    my $certtime = $basecosts->{$target};
    if (! defined $certtime) {
	# Probably the .lisp file doesn't exist
	my %entry = ( "totaltime" => 0.0,
		      "maxpath" => "ERROR" );
	$costs->{$target} = \%entry;
	return $costs->{$target};
    }
    
    my $targetdeps;
    if ($pcert) {

	$targetdeps = [];
	if ($target =~ /\.pcert0$/) {
	    ## The dependencies are the dependencies of the cert file, but
	    ## with each .cert replaced with the corresponding .pcert0.
	    (my $certfile = $target) =~ s/\.pcert0$/\.cert/;
	    my $certdeps = cert_deps($certfile, $deps);
	    foreach my $dep (@$certdeps) {
		my $deppcert = cert_sequential_dep($dep, $deps);
		push(@$targetdeps, $deppcert);
	    }
	} elsif ($target =~ /\.pcert1$/) {
	    (my $certfile = $target) =~ s/\.pcert1$/\.cert/;
	    if (cert_get_param($certfile, $deps, "no_pcert") ||
		cert_get_param($certfile, $deps, "acl2x")) {
		## Depends on the sequential deps of the other certs
		my $certdeps = cert_deps($certfile, $deps);
		foreach my $dep (@$certdeps) {
		    my $deppcert = cert_sequential_dep($dep, $deps);
		    push(@$targetdeps, $deppcert);
		}
	    } else {
		## For true pcert, the only dependency is the corresponding .pcert0.
		(my $pcert0 = $target) =~ s/\.pcert1$/\.pcert0/;
		push (@$targetdeps, $pcert0);
	    }
	} elsif ($target =~ /\.acl2x$/) {
	    ## The dependencies are the dependencies of the cert file.
	    (my $certfile = $target) =~ s/\.acl2x$/\.cert/;
	    my $certdeps = cert_deps($certfile, $deps);
	    push(@$targetdeps, @$certdeps);
	} else { # $target =~ /\.cert$/
	    # Depends.
	    if (cert_get_param($target, $deps, "acl2x")) {
		# If it's using the acl2x/two-pass, then depend only on the acl2x file.
		(my $acl2xfile = $target) =~ s/\.cert$/\.acl2x/;
		push (@$targetdeps, $acl2xfile);
	    } else {
		# otherwise, depend on its subbooks' certificates and the pcert1.
		push (@$targetdeps, @{cert_deps($target, $deps)});
		(my $pcert1 = $target) =~ s/\.cert$/\.pcert1/;
		push (@$targetdeps, $pcert1);
	    }
	}
    } else {
	if ($target =~ /\.acl2x$/) {
	    (my $certfile = $target) =~ s/\.acl2x$/\.cert/;
	    $targetdeps = cert_deps($certfile, $deps);
	} elsif ($target =~ /\.cert$/) {
	    if (cert_is_two_pass($target, $deps)) {
		my $acl2xfile = cert_to_acl2x($target);
		$targetdeps = [ $acl2xfile ];
	    } else {
		$targetdeps = cert_deps($target, $deps);
	    }
	} else {
	    print "Warning: pcert file out of pcert context: $target\n";
	    $targetdeps = [];
	}
    }

    my $most_expensive_dep = 0;
    my $most_expensive_dep_total = 0;


#    print "$target depends on @$targetdeps\n";
    if (@$targetdeps) {
	foreach my $dep (@$targetdeps) {
	    if ($dep =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
		my $this_dep_costs = compute_cost_paths_aux($dep, $deps, $basecosts, $costs, $warnings, $pcert);
		if (! $this_dep_costs) {
		    if ($dep eq $target) {
			push(@{$warnings}, "Self-dependency in $dep");
		    } else {
			push(@{$warnings}, "Dependency loop involving $dep and $target");
		    }
		}
	    }
	}

	($most_expensive_dep, $most_expensive_dep_total) = find_most_expensive($targetdeps, $costs);
    }
    # if (! defined $most_expensive_dep_total) {
    # 	carp("Most_expensive_dep undefined for $target\n");
    # } elsif (! defined $certtime) {
    # 	carp("Certtime undefined for $target\n");
    # }
    my %entry = ( "totaltime" => $most_expensive_dep_total + $certtime, 
		  "maxpath" => $most_expensive_dep );
    $costs->{$target} = \%entry;
    return $costs->{$target};
}

sub compute_cost_paths {
    my ($deps,$basecosts,$costs,$warnings,$pcert) = @_;
    
    foreach my $certfile (keys %{$deps}) {
	compute_cost_paths_aux($certfile, $deps, $basecosts, $costs, $warnings,$pcert);
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



sub critical_path_report {

# critical_path_report(costs,htmlp) returns a string describing the
# critical path for file according to the costs_table, either in TEXT or HTML
# format per the value of htmlp.
    my ($costs,$basecosts,$savings,$topfile,$htmlp,$short) = @_;


    my $ret;

    if ($htmlp) {
	$ret = "<table class=\"critpath_table\">\n"
	     . "<tr class=\"critpath_head\">"
	     . "<th>Critical Path</th>" 
	     . "<th>Time</th>"
	     . "<th>Cumulative</th>"
	     . "</tr>\n";
    }
    else {
	$ret = "Critical Path\n\n"
	     . sprintf("%-50s %10s %10s %10s %10s\n", "File", "Cumulative", "Time", "Speedup", "Remove");
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
	    $ret .= sprintf("%-50s %10s %10s %10s %10s\n", $shortcert, $cumtime_pr, $selftime_pr, $spsav_pr, $remsav_pr);
	}

	$file = $filecosts->{"maxpath"};
    }

    if ($htmlp) {
	$ret .= "</table>\n\n";
    }
    else {
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
    my ($costs,$basecosts,$htmlp,$short) = @_;

    my @sorted = reverse sort { ($costs->{$a}->{"totaltime"} + 0.0) <=> ($costs->{$b}->{"totaltime"} + 0.0) } keys(%{$costs});
    my $ret;
    if ($htmlp) 
    {
	$ret = "<table class=\"indiv_table\">\n"
	     . "<tr class=\"indiv_head\"><th>All Files</th> <th>Cumulative</th> <th>Self</th></tr>\n";
    } else {
	$ret = "Individual File Times\n\n";

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
	    $ret .= sprintf("%-50s %10s %10s  --->  %-50s\n",
			    $shortname, $cumul, $time, $depname);
	}
    }
    
    if ($htmlp)
    {
	$ret .= "</table>\n\n";
    } else {
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
	print "Error: Ended with jobs still running??\n"
    }
    my $avg_parallel = $running_total / $lasttime;

    return ($max_parallel, $max_start_time, $max_end_time, $avg_parallel, $running_total);
}






sub to_basename {
    my $name = shift;
    $name = canonical_path($name);
    $name =~ s/\.(lisp|cert)$//;
    return $name;
}





my $debugging = 0;
my $clean_certs = 0;
my $print_deps = 0;
my $believe_cache = 0;

#  However, now it makes sense to do it in two
# passes:
# - update the dependency-info cache, including the cert and source
# tables mentioned above
# - create the make-style dependency graph using that cache,
# afterward.

# A complication is that add-include-book-dir directives can affect
# what dependencies are stored, but this should only affect ones that
# come after.  To deal with this, for each file we'll create a log of
# what relevant lines are in it, in order.

my %dirs = ( );

sub certlib_add_dir {
    my ($name,$dir) = @_;
    $dirs{$name} = $dir;
}

sub certlib_set_opts {
    my $opts = shift;
    $debugging = $opts->{"debugging"};
    $clean_certs = $opts->{"clean_certs"};
    $print_deps = $opts->{"print_deps"};
    $believe_cache = $opts->{"believe_cache"};
}

sub certlib_set_base_path {
    my $dir = shift;
    $dir = $dir || ".";
    $BASE_PATH = abs_canonical_path($dir);
    %canonical_path_memo = ();
}


# Event types:
my $add_dir_event = 'add-include-book-dir';
my $include_book_event = 'include-book';
my $depends_on_event = 'depends-on';
my $loads_event = 'loads';
my $cert_param_event = 'cert_param';
my $ld_event = 'ld';


sub get_add_dir {
    my ($base,$the_line,$events) = @_;

    # Check for ADD-INCLUDE-BOOK-DIR commands
    my $regexp = "^[^;]*\\(add-include-book-dir[\\s]+:([^\\s]*)[\\s]*\"([^\"]*[^\"/])/?\"";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	my $name = uc($res[0]);
	print "$base: add_dir $name $res[1]\n" if $debugging;
	push (@$events, [$add_dir_event, $name, $res[1]]);
	return 1;
    }
    return 0;
}


sub lookup_colon_dir {
    my $name = uc(shift);
    my $local_dirs = shift;

    my $dirpath;
    if ($local_dirs && exists $local_dirs->{$name}) {
	$dirpath = $local_dirs->{$name};
    } else {
	$dirpath = $dirs{$name} ;
    }
    return $dirpath;
}

sub print_scanevent {
    my ($fname,$cmd,$args) = @_;    
    print "$fname: $cmd ";
    foreach my $arg (@$args) {
	$arg && print " $arg";
    }
    print "\n";
}
sub debug_print_event {
    my ($fname,$cmd,$args) = @_;
    if ($debugging) {
	print_scanevent($fname, $cmd, $args);
    }
}

sub get_include_book {
    my ($base,$the_line,$events) = @_;

    my $regexp = "^[^;]*\\(include-book[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "include_book", \@res);
	push(@$events, [$include_book_event, $res[0], $res[1]]);
	return 1;
    }
    return 0;
}

sub get_depends_on {
    my ($base,$the_line,$events) = @_;

    my $regexp = "\\(depends-on[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "depends_on", \@res);
	push(@$events, [$depends_on_event, $res[0], $res[1]]);
	return 1;
    }
    return 0;
}

sub get_loads {
    my ($base,$the_line,$events) = @_;

    my $regexp = "\\(loads[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "loads", \@res);
	push(@$events, [$loads_event, $res[0], $res[1]]);
	return 1;
    }
    return 0;
}

my $two_pass_warning_printed = 0;

sub parse_params {
    my $param_str = shift;
    my @params = split(/,/, $param_str);
    my @pairs = ();
    foreach my $param (@params) {
	my @assign = $param =~ m/[\s]*([^\s=]*)[\s]*=[\s]*([^\s=]*)[\s]*/;
	if (@assign) {
	    push(@pairs, [$assign[0], $assign[1]]);
	} else {
	    push(@pairs, [$param, 1]);
	}
    }
    return \@pairs;
}



sub get_cert_param {
    my ($base,$the_line,$events) = @_;

    my $regexp = "cert_param:[\\s]*\\(?([^)]*)\\)?";
    my @match = $the_line =~ m/$regexp/;
    if (@match) {
	debug_print_event($base, "cert_param", \@match);
	my $pairs = parse_params($match[0]);
	foreach my $pair (@$pairs) {
	    (my $param, my $val) = @$pair;
	    push(@$events, [$cert_param_event, $param, $val]);
	}
	return 1;
    }
    $regexp = ";; two-pass certification";
    if ($the_line =~ m/$regexp/) {
	if ($two_pass_warning_printed) {
	    print "$base has two-pass certification directive\n";
	} else {
	    $two_pass_warning_printed = 1;
	    print "\nin $base:\n";
	    print "Note: Though we still recognize the \";; two-pass certification\"\n";
	    print "directive, it is deprecated in favor of:\n";
	    print ";; cert_param: (acl2x)\n\n";
	}
	push (@$events, [$cert_param_event, "acl2x", 1]);
	return 1;
    }
    return 0;
}





# Possible more general way of recognizing a Lisp symbol:
# ((?:[^\\s\\\\|]|\\\\.|(?:\\|[^|]*\\|))*)
# - repeatedly matches either: a non-pipe, non-backslash, non-whitespace character,
#                              a backslash and subsequently any character, or
#                              a pair of pipes with a series of intervening non-pipe characters.
# For now, stick with a dumber, less error-prone method.


sub get_ld {
    my ($base,$the_line,$events) = @_;

    # Check for LD commands
    my $regexp = "^[^;]*\\(ld[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "ld", \@res);
	push(@$events, [$ld_event, $res[0], $res[1]]);
	return 1;
    }
    return 0;
}

sub ftimestamp {
    my $file = shift;
    return (stat($file))[9];
}

sub newer_than {
    my ($file1,$file2) = @_;
    return ftimestamp($file1) > ftimestamp($file2);
}

sub excludep {
    my $prev = shift;
    my $dirname = dirname($prev);
    while ($dirname ne $prev) {
	if (-e rel_path($dirname, "cert_pl_exclude")) {
	    return 1;
	}
	$prev = $dirname;
	$dirname = dirname($dirname);
    }
    return 0;
}



sub print_dirs {
    my $local_dirs = shift;
    print "dirs:\n";
    while ( (my $k, my $v) = each (%{$local_dirs})) {
	print "$k -> $v\n";
    }
}

# Scans a source file line by line to get the list of
# dependency-affecting events.
sub scan_src {
    my $fname = shift;
    my @events = ();

    if (open(my $file, "<", $fname)) {
	while (my $the_line = <$file>) {
	    my $done = 0;
	    $done = get_include_book($fname, $the_line, \@events);
	    $done = $done || get_ld($fname, $the_line, \@events);
	    $done = $done || get_depends_on($fname, $the_line, \@events);
	    $done = $done || get_loads($fname, $the_line, \@events);
	    $done = $done || get_add_dir($fname, $the_line, \@events);
	    $done = $done || get_cert_param($fname, $the_line, \@events);
	}
	close($file);
    }
    my $timestamp = ftimestamp($fname);

    return (\@events, $timestamp);
}

# Gets the list of dependency-affecting events that are present in a
# source file.  These may be either already in the cache, or else they
# are read in using scan_src.
sub src_events {
    my ($fname,$evcache,$checked,$parent) = @_;

    my $entry = $evcache->{$fname};
    my $entry_ok = 0;

    if (-e $fname) {
	if ($entry) {
	    if ($believe_cache || $checked->{$entry}) {
		print "cached events for $fname\n" if $debugging;
	    $entry_ok = 1;
	    } elsif (ftimestamp($fname) && (ftimestamp($fname) <= $entry->[1])) {
		$checked->{$entry} = 1;
		$entry_ok = 1;
	    }
	}
	if ($entry_ok) {
	    print "cached events for $fname\n" if $debugging;
	    return $entry->[0];
	} else {
	    print "reading events for $fname\n" if $debugging;
	    (my $events, my $timestamp) = scan_src($fname);
	    my $cache_entry = [$events, $timestamp];
	    print "caching events for $fname\n" if $debugging;
	    $evcache->{$fname} = $cache_entry;
	    $checked->{$fname} = 1;
	    return $events;
	}
    } else {
	print "Warning: missing file $fname in src_events\n";
	if ($parent) {
	    print "(Required by $parent)\n";
	}
	return [];
    }
}

sub expand_dirname_cmd {
    my ($relname,$basename,$dirname,$local_dirs,$cmd,$ext) = @_;
    my $fullname;
    if ($dirname) {
	my $dirpath = lookup_colon_dir($dirname, $local_dirs);
	unless ($dirpath) {
	    print "Warning: Unknown :dir entry in ($cmd \"$relname\" :dir $dirname) for $basename\n";
	    print_dirs($local_dirs) if $debugging;
	    return 0;
	}
	print "expand $dirname -> $dirpath\n" if $debugging;
	$fullname = canonical_path(rel_path($dirpath, $relname . $ext));
	if (! $fullname) {
	    print ":dir entry in ($cmd \"$relname\" :dir $dirname) produced bad path\n";
	}
    } else {
	my $dir = dirname($basename);
	$fullname = canonical_path(rel_path($dir, $relname . $ext));
	if (! $fullname) {
	    print "bad path in ($cmd \"$relname\")\n";
	}
    }
    return $fullname;
}

sub print_event {
    my $event = shift;
    print $event->[0];
    my $i = 1;
    while ($i < @$event) {
	$event->[$i] && print " $event->[$i]";
	$i = $i+1;
    }
}

sub print_events {
    my $events = shift;
    foreach my $event (@$events) {
	print "\n"; print_event($event);
    }
    print "\n";
}
    
my %times_seen = ();

sub print_times_seen {
    foreach my $key (sort(keys(%times_seen))) {
	print "$key -> $times_seen{$key}\n";
    }
}

my $src_deps_depth = -1;
# Gets the (recursive) dependencies of fname, and returns whether it
# requires two-pass certification.  Calls src_events to get the
# dependency-affecting events that are present in the file
# (include-books, lds, etc.)
sub src_deps {
    my ($fname,             # file to scan for dependencies
	$cache,             # file event cache
	$local_dirs,        # :dir name table
	$certdeps,          # certificate dependency list (accumulator)
	$srcdeps,           # source file dependency list (accumulator)
	$otherdeps,         # other file dependency list (accumulator)
	$certparams,        # cert param hash (accumulator)
	$tscache,           # timestamp cache
	$ld_ok,             # Allow following LD commands
	$seen,              # seen table for detecting circular dependencies
	$parent)            # file that required this one
	= @_;

    if ($seen->{$fname}) {
	print "Circular dependency found in src_deps of $fname\n";
	return 0;
    }
    
    $seen->{$fname} = 1;

    $times_seen{$fname} = ($times_seen{$fname} || 0) + 1;

    $src_deps_depth = $src_deps_depth + 1;
    print "$src_deps_depth src_deps $fname\n"  if $debugging;
    my $events = src_events($fname, $cache, $tscache, $parent);
    if ($debugging) {
	print "events: $fname";
	print_events($events);
    }

    foreach my $event (@$events) {
	my $type = $event->[0];
	if ($type eq $add_dir_event) {
	    my $name = $event->[1];
	    my $dir = $event->[2];
	    my $basedir = dirname($fname);
	    my $newdir = canonical_path(rel_path($basedir, $dir));
	    if (! $newdir) {
		print "Bad path processing (add-include-book-dir :$name \"$dir\") in $fname\n";
	    }
	    $local_dirs->{$name} = $newdir;
	    print "src_deps: add_dir $name $local_dirs->{$name}\n" if
		$debugging;
	} elsif ($type eq $include_book_event) {
	    my $bookname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($bookname, $fname, $dir,
					      $local_dirs,
					      "include-book",
					      ".cert");
	    if (! $fullname) {
		print "Bad path in (include-book \"$bookname\""
                      . ($dir ? " :dir $dir)" : ")") . " in $fname\n";
	    }
	    print "include-book fullname: $fullname\n" if $debugging;
	    $fullname && push(@$certdeps, $fullname);
	} elsif ($type eq $depends_on_event) {
	    my $depname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($depname, $fname, $dir,
					      $local_dirs,
					      "depends-on", "");
	    if (! $fullname) {
		print "Bad path in (depends-on \"$depname\""
                      . ($dir ? " :dir $dir)" : ")") . " in $fname\n";
	    }
	    $fullname && push(@$otherdeps, $fullname);
	} elsif ($type eq $depends_on_event) {
	    # skip it
	} elsif ($type eq $loads_event) {
	    my $srcname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
					      $local_dirs, "loads", "");
	    if ($fullname) {
		push(@$srcdeps, $fullname);
		src_deps($fullname, $cache,
			 $local_dirs,
			 $certdeps,
			 $srcdeps,
			 $otherdeps,
			 $certparams,
			 $tscache,
			 $ld_ok,
			 $seen,
			 $fname);
	    } else {
		print "Bad path in (loads \"$srcname\""
		    . ($dir ? " :dir $dir)" : ")") . " in $fname\n";
	    }
	} elsif ($type eq $cert_param_event) {
	    # print "cert_param: $fname, " . $event->[1] . " = " . $event->[2] . "\n";
	    $certparams->{$event->[1]} = $event->[2];
	} elsif ($type eq $ld_event) {
	    if ($ld_ok) {
		my $srcname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
						  $local_dirs, "ld", "");
		if ($fullname) {
		    push(@$srcdeps, $fullname);
		    src_deps($fullname, $cache,
			     $local_dirs,
			     $certdeps,
			     $srcdeps,
			     $otherdeps,
			     $certparams,
			     $tscache,
			     $ld_ok,
			     $seen,
			     $fname);
		} else {
		    print "Bad path in (ld \"$srcname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		}
	    } else {
		print "Warning: LD event in book context in $fname:\n";
		print_event($event);
		print "\n";
	    }
	} else {
	    print "unknown event type: $type\n";
	}
    }

    $seen->{$fname} = 0;

    print "$src_deps_depth done src_deps $fname\n" if $debugging;
    $src_deps_depth = $src_deps_depth - 1;
}

sub print_lst {
    my $lst = shift;
    foreach my $val (@$lst) {
	$val && print " $val";
    }
    print "\n";
}

sub remove_dups {
    my $lst = shift;
    my @newlst = ();
    my @sortlst = sort(@$lst);
    my $lastentry = $sortlst[0];
    push (@newlst, $lastentry);
    foreach my $val (@sortlst) {
	push(@newlst, $val) unless ($val eq $lastentry);
	$lastentry = $val;
    }
    return \@newlst;
}


# Find dependencies of a lisp file.  If it has a .lisp extension, we
# assume it's supposed to be a certifiable book, so we look for .acl2
# and image files as well.  Calls src_deps to get the dependencies.
sub find_deps {
    my ($lispfile,$cache,$tscache,$parent) = @_;

    my $bookdeps = [];
    my $portdeps = [];
    my $srcdeps = [ $lispfile ];
    my $otherdeps = [];
    my $local_dirs = {};

    # If this source file has a .lisp extension, we assume it's a
    # certifiable book and look for an .acl2 file.
    my $certifiable = $lispfile =~ /\.lisp$/;

    my $base;
    my $certparams = {};
    if ($certifiable) {
	# If a corresponding .acl2 file exists or otherwise if a
	# cert.acl2 file exists in the directory, we need to scan that for dependencies as well.
	( $base = $lispfile ) =~ s/\.lisp$//;
	my $acl2file = $base . ".acl2";
	if (! -e $acl2file) {
	    $acl2file = rel_path(dirname($base), "cert.acl2");
	    if (! -e $acl2file) {
		$acl2file = 0;
	    }
	}

	# Scan the .acl2 file first so that we get the add-include-book-dir
	# commands before the include-book commands.
	if ($acl2file) {
	    push(@$srcdeps, $acl2file);
	    src_deps($acl2file, $cache,
		     $local_dirs, 
		     $portdeps,
		     $srcdeps,
		     $otherdeps,
		     $certparams,
		     $tscache,
		     1,
		     {}, $lispfile);
	}
    }

    # Scan the lisp file for include-books.
    src_deps($lispfile, $cache, $local_dirs,
	     $bookdeps, $srcdeps, $otherdeps, $certparams,
	     $tscache, !$certifiable, {}, $parent);

    if ($debugging) {
	print "find_deps $lispfile: bookdeps:\n";
	print_lst($bookdeps);
	print "portdeps:\n";
	print_lst($portdeps);
	print "sources:\n";
	print_lst($srcdeps);
	print "others:\n";
	print_lst($otherdeps);
    }
    
    my $image;

    if ($certifiable) {
	# If there is an .image file corresponding to this file or a
	# cert.image in this file's directory, add a dependency on the
	# ACL2 image specified in that file and the .image file itself.
	my $imagefile = $base . ".image";
	if (! -e $imagefile) {
	    $imagefile = rel_path(dirname($base), "cert.image");
	    if (! -e $imagefile) {
		$imagefile = 0;
	    }
	}

	if ($imagefile) {
	    my $imfilepath = canonical_path($imagefile);
	    # Won't check the result of canonical_path because we're
	    # already in the right directory.
	    push(@{$otherdeps}, $imfilepath);
	    my $line;
	    if (open(my $im, "<", $imagefile)) {
		$line = <$im>;
		close $im;
		chomp $line;
	    } else {
		print "Warning: find_deps: Could not open image file $imagefile: $!\n";
	    }
	    $image = $line;
	}
    }

    return ($bookdeps, $portdeps, $srcdeps, $otherdeps, $image, $certparams);

}



# Given that the dependency map $depmap is already built, this collects
# the full set of sources and targets needed for a given file.
sub deps_dfs {
    my ($target, $depmap, $visited, $sources, $certs, $others) = @_;

    if ($visited->{$target}) {
	return;
    }

    $visited->{$target} = 1;

    push (@$certs, $target);
    my $certdeps = cert_deps($target, $depmap);
    my $srcdeps = cert_srcdeps($target, $depmap);
    my $otherdeps = cert_otherdeps($target, $depmap);

    foreach my $dep (@$srcdeps) {
	if (! $visited->{$dep}) {
	    push(@$sources, $dep);
	    $visited->{$dep} = 1;
	}
    }

    foreach my $dep (@$otherdeps) {
	if (! $visited->{$dep}) {
	    push(@$others, $dep);
	    $visited->{$dep} = 1;
	}
    }


    foreach my $dep (@$certdeps) {
	deps_dfs($dep, $depmap, $visited, $sources, $certs, $others);
    }
}

    

# During a dependency search, this is run with $target set to each
# cert and source file in the dependencies of the top-level targets.
# If the target has been seen before, then it returns immediately.
# Otherwise, this calls on find_deps to get those dependencies.
sub add_deps {
    my ($target,$cache,$depmap,$sources,$others,$tscache,$parent) = @_;

    print "add_deps (check) $target\n" if $debugging;

    if ($target !~ /\.cert$/) {
	print "not cert\n" if $debugging;
	return;
    }

    if (exists $depmap->{$target}) {
	# We've already calculated this file's dependencies.
	print "depmap entry exists\n" if $debugging;
	return;
    }

    if (excludep($target)) {
    	# $depmap->{$target} = [];
	print "excludep\n" if $debugging;
    	return;
    }

    print "add_deps $target\n" if $debugging;

    my $local_dirs = {};
    (my $base = $target) =~ s/\.cert$//;
    my $lispfile = $base . ".lisp";

    # Clean the cert and out files if we're cleaning.
    if ($clean_certs) {
	my $outfile = $target . ".out";
	my $timefile = $target . ".time";
	my $compfile = $base . ".lx64fsl";
	my $acl2xfile = $base . ".acl2x";
	unlink($target) if (-e $target);
	unlink($outfile) if (-e $outfile);
	unlink($timefile) if (-e $timefile);
	unlink($compfile) if (-e $compfile);
	unlink($acl2xfile) if (-e $acl2xfile);
    }

    # First check that the corresponding .lisp file exists.
    if (! -e $lispfile) {
	print "Error: Need $lispfile to build $target"
               . ($parent ? " (parent: $parent)" : "")
	       . ".\n";
	return;
    }

    my ($bookdeps, $portdeps, $srcdeps, $otherdeps, $image, $certparams)
	= find_deps($lispfile, $cache, $tscache, $parent);


    $depmap->{$target} = [ $bookdeps, $portdeps, $srcdeps, $otherdeps, $image, $certparams ] ;

    if ($print_deps) {
	print "Dependencies for $target:\n";
	print "book:\n";
	foreach my $dep (@$bookdeps) {
	    print "$dep\n";
	}
	print "port:\n";
	foreach my $dep (@$portdeps) {
	    print "$dep\n";
	}
	print "src:\n";
	foreach my $dep (@{$srcdeps}) {
	    print "$dep\n";
	}
	print "other:\n";
	foreach my $dep (@{$otherdeps}) {
	    print "$dep\n";
	}
	print "image: $image\n" if $image;
	if ($certparams) {
	    print "certparams: ";
	    while (my ($key, $value) = each %$certparams) {
		print "$key = $value";
	    }
	    print "\n";
	}
	print "\n";
    }

    # Accumulate the set of sources.
    foreach my $dep (@$srcdeps) {
	$sources->{$dep} = 1;
    }

    # Accumulate the set of non-source/cert deps..
    foreach my $dep (@$otherdeps) {
	$others->{$dep} = 1;
    }


    # Run the recursive add_deps on each dependency.
    foreach my $dep  (@$bookdeps, @$portdeps) {
	add_deps($dep, $cache, $depmap, $sources, $others, $tscache, $target);
    }

}

sub read_targets {
    my ($fname,$targets) = @_;
    if (open (my $tfile, $fname)) {
	while (my $the_line = <$tfile>) {
	    chomp($the_line);
	    $the_line =~ m/^\s*([^\#]*[^\#\s])?/;
	    my $fname = $1;
	    if ($fname && (length($fname) > 0)) {
		push (@{$targets}, $fname);
	    }
	}
	close $tfile;
    } else {
	print "Warning: Could not open $fname: $!\n";
    }
}

# Heuristically take some user-input filename and produce the source
# file we actually want to read.  For now, if it doesn't have a dot,
# tack a .lisp onto it; if it has a .cert/.pcert/.acl2x extension
# change it to .lisp, and otherwise leave it alone.
# examples:
# foo.lisp  -> foo.lisp
# foo       -> foo.lisp
# foo.cert  -> foo.lisp
# foo.acl2x -> foo.lisp
# foo.pcert -> foo.lisp
# foo.lsp   -> foo.lsp
# foo.acl2  -> foo.acl2
sub to_source_name {
    my $fname = shift;
    if ($fname =~ /\./) {
	$fname =~ s/\.(cert|acl2x|pcert0|pcert1)$/\.lisp/;
	return $fname;
    } else {
	return "$fname.lisp";
    }
}

# Heuristically take some user-input filename and produce the cert
# file we want to target.  For now, if it has a .lisp extension change
# it to .cert, if it has a .acl2x/.pcert/.cert extension leave it
# alone, and otherwise tack on a .cert.  NOTE: This heuristic doesn't
# at all match the one in to_source_name; they're used for different
# purposes.
# foo.lisp  -> foo.cert
# foo       -> foo.cert
# foo.cert  -> foo.cert
# foo.acl2x -> foo.acl2x
# foo.pcert -> foo.pcert
# foo.lsp   -> foo.lsp.cert
# foo.acl2  -> foo.acl2.cert
sub to_cert_name {
    my $fname = shift;
    $fname =~ s/\.lisp$/\.cert/;
    if ($fname =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
	return $fname;
    } else {
	return "$fname.cert";
    }
}


# Takes a list of inputs containing some filenames and some labels
# and some entries of the form "-p filename".
# (ending with a colon.)  Sorts out the filenames into a list of
# targets (changing them to .cert extensions if necessary) and returns
# the list of targets and a hash associating each label with its list
# of targets.
sub process_labels_and_targets {
    my ($input, $cache, $tscache) = @_;
    my %labels = ();
    my @targets = ();
    my $label_started = 0;
    my $label_targets;
    foreach my $str (@$input) {
	if (substr($str, 0, 3) eq '-p ') {
	    # Deps-of.
	    my $name = canonical_path(to_source_name(substr($str,3)));
	    if ($name) {
		my ($deps) = find_deps($name, $cache, $tscache, 0);
		push (@targets, @$deps);
		push (@$label_targets, @$deps) if $label_started;
	    } else {
		print "Bad path for target: $str\n";
	    }
	} elsif (substr($str, -1, 1) eq ':') {
	    # label.
	    my $label = substr($str,0,-1); # everything but the :
	    $label_started = 1;
	    if (! exists($labels{$label})) {
		$label_targets = [];
		$labels{$label} = $label_targets;
	    } else {
		$label_targets = $labels{$label};
	    }
	} else {
	    # filename.
	    my $target = canonical_path(to_cert_name($str));
	    if ($target) {
		push(@targets, $target);
		push(@$label_targets, $target) if $label_started;
	    } else {
		print "Bad path for target: $str\n";
	    }
	}
    }
    # print "Labels:\n";
    # while ((my $key, my $value) = each %labels) {
    # 	print "${key}:\n";
    # 	foreach my $target (@$value) {
    # 	    print "$target\n";
    # 	}
    # }

    return (\@targets, \%labels);
}



sub compute_savings
{
    my ($costs,$basecosts,$targets,$debug,$deps, $pcert) = @_;

    (my $topbook, my $topbook_cost) = find_most_expensive($targets, $costs);

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
	compute_cost_paths($deps, $basecosts, \%tmpcosts, \@tmpwarns, $pcert);
	(my $tmptop, my $tmptopcost) = find_most_expensive($targets, \%tmpcosts);
	my $speedup_savings = $topbook_cost - $tmptopcost;
	$speedup_savings = $speedup_savings || 0.000001;

	# Get the max savings from removing the book:
	# set the file total cost to 0 and recompute crit path.
	%tmpcosts = ();
	$tmpcosts{$critfile} = 0;
	compute_cost_paths($deps, $basecosts, \%tmpcosts, \@tmpwarns, $pcert);
	($tmptop, $tmptopcost) = find_most_expensive($targets, \%tmpcosts);
	my $remove_savings = $topbook_cost - $tmptopcost;
	$remove_savings = $remove_savings || 0.000001;

	my %entry = ( "speedup" => $speedup_savings,
		      "remove" => $remove_savings );
	$savings{$critfile} = \%entry;
	$basecosts->{$critfile} = $filebasecost;
    }

    return \%savings;
}

sub store_cache {
    my ($cache, $fname) = @_;
    if ($fname) {
	store([$cache_version_code, $cache], $fname);
    }
}

sub retrieve_cache {
    my $fname = shift;
    if (! $fname || ! -e $fname) {
	return {};
    }

    my $pair = retrieve($fname);
    if (! (ref($pair) eq 'ARRAY')) {
	print "Invalid cache format; starting from empty cache\n";
	return {};
    } elsif ( $pair->[0] != $cache_version_code ) {
	print "Wrong cache version code; starting from empty cache\n";
	return {};
    } elsif (! (ref($pair->[1]) eq 'HASH')) {
	print "Right cache version code, but badly formatted! Starting from empty\n";
	return {};
    } else {
	return $pair->[1];
    }
}



# The following "1" is here so that loading this file with "do" or "require" will succeed:
1;
