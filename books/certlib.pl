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
# use Cwd;
use Cwd 'abs_path';


sub human_time {

# human_time(secs,shortp) returns a string describing the time taken in a
# human-friendly format, e.g., 5.6 minutes, 10.3 hours, etc.  If shortp is
# given, then we use, e.g., "min" instead of "minutes."

    my $secs = shift;
    my $shortp = shift;

    if (!$secs) {
	return "???";
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
	if ($BASE_PATH) {
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

    my $path = shift;
    my $warnings = shift;

    $path =~ s/\.cert$/\.time/;
    $path =~ s/\.acl2x$/\.acl2x\.time/;
    
    if (open (my $timefile, "<", $path)) {
	while (my $the_line = <$timefile>) {
	    my $regexp = "^([0-9]*\\.[0-9]*)user ([0-9]*\\.[0-9]*)system";
	    my @res = $the_line =~ m/$regexp/;
	    if (@res) {
		close $timefile;
		return 0.0 + $res[0] + $res[1];
	    }
	}
	push(@$warnings, "Corrupt timings in $path\n");
	close $timefile;
	return 0;
    } else {
	push(@$warnings, "Could not open $path: $!\n");
	return 0;
    }
}


sub read_costs {
    my $deps = shift;
    my $basecosts = shift;
    my $warnings = shift;

    foreach my $certfile (keys %{$deps}) {
	if ($certfile =~ /\.(cert|acl2x)$/) {
	    my $cost = get_cert_time($certfile, $warnings);
	    $basecosts->{$certfile} = $cost;
	}
    }
}

sub find_most_expensive {
    my $files = shift;
    my $costs = shift;

    my $most_expensive_file_total = 0;
    my $most_expensive_file = 0;

    foreach my $file (@{$files}) {
	if ($file =~ /\.(cert|acl2x)$/) {

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
    my $certfile = shift;
    my $deps = shift;
    my $basecosts = shift;
    my $costs = shift;
    my $warnings = shift;

    if (exists $costs->{$certfile} || ! ($certfile =~ /\.(cert|acl2x)$/)) {
	return $costs->{$certfile};
    }

    # put something in $costs->{$certfile} so that we don't loop
    $costs->{$certfile} = 0;

    my $certtime = $basecosts->{$certfile};
    my $certdeps = $deps->{$certfile};

    my $most_expensive_dep = 0;
    my $most_expensive_dep_total = 0;

    if ($certdeps) {
	foreach my $dep (@{$certdeps}) {
	    if ($dep =~ /\.(cert|acl2x)$/) {
		my $this_dep_costs = compute_cost_paths_aux($dep, $deps, $basecosts, $costs, $warnings);
		if (! $this_dep_costs) {
		    if ($dep eq $certfile) {
			push(@{$warnings}, "Self-dependency in $dep");
		    } else {
			push(@{$warnings}, "Dependency loop involving $dep and $certfile");
		    }
		}
	    }
	}

	($most_expensive_dep, $most_expensive_dep_total) = find_most_expensive($certdeps, $costs);
    }
    my %entry = ( "totaltime" => $most_expensive_dep_total + $certtime, 
		  "maxpath" => $most_expensive_dep );

    $costs->{$certfile} = \%entry;
    return $costs->{$certfile};
}

sub compute_cost_paths {
    my $deps = shift;
    my $basecosts = shift;
    my $costs = shift;
    my $warnings = shift;
    
    foreach my $certfile (keys %{$deps}) {
	compute_cost_paths_aux($certfile, $deps, $basecosts, $costs, $warnings);
    }
}



sub warnings_report {

# warnings_report(warnings, htmlp) returns a string describing any warnings
# which were encountered during the generation of the costs table, such as for
# missing .time files.

    my $warnings = shift;
    my $htmlp = shift;

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

    my $costs = shift;
    my $basecosts = shift;
    my $savings = shift;
    my $topfile = shift;
    my $htmlp = shift;
    my $short = shift;


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

	my $selftime_pr = $selftime ? human_time($selftime, 1) : "[Error]";
	my $cumtime_pr = $cumtime ? human_time($cumtime, 1) : "[Error]";
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

    my $costs = shift;
    my $basecosts = shift;
    my $htmlp = shift;
    my $short = shift;

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
	my $cumul = $entry->{"totaltime"} ? human_time($entry->{"totaltime"}, 1) : "[Error]";
	my $time = $basecosts->{$name} ? human_time($basecosts->{$name}, 1) : "[Error]";
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
	my $selfcost = $basecosts->{$key};
	$running_total = $running_total + $selfcost;
	my $totalcost = $costs->{$key}->{"totaltime"};
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
my $all_deps = 0;
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
    my $name = shift;
    my $dir = shift;
    $dirs{$name} = $dir;
}

sub certlib_set_opts {
    my $opts = shift;
    $debugging = $opts->{"debugging"};
    $clean_certs = $opts->{"clean_certs"};
    $print_deps = $opts->{"print_deps"};
    $all_deps = $opts->{"all_deps"};
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
my $two_pass_event = 'two-pass certification';
my $ld_event = 'ld';


sub get_add_dir {
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

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
    $local_dirs && ($dirpath = $local_dirs->{$name});
    if (! defined($dirpath)) {
	$dirpath = $dirs{$name} ;
    }
    return $dirpath;
}

sub debug_print_event {
    my $fname = shift;
    my $cmd = shift;
    my $args = shift;
    if ($debugging) {
	print "$fname: $cmd ";
	foreach my $arg (@$args) {
	    $arg && print " $arg";
	}
	print "\n";
    }
}

sub get_include_book {
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

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
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

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
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

    my $regexp = "\\(loads[\\s]*\"([^\"]*)\"(?:.*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "loads", \@res);
	push(@$events, [$loads_event, $res[0], $res[1]]);
	return 1;
    }
    return 0;
}


sub get_two_pass {
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

    my $regexp = ";; two-pass certification";
    my $match = $the_line =~ m/$regexp/;
    if ($match) {
	debug_print_event($base, "two_pass", []);
	push(@$events, [$two_pass_event]);
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
    my $base = shift;
    my $the_line = shift;
    my $events = shift;

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
    my $file1 = shift;
    my $file2 = shift;
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
	    $done = $done || get_two_pass($fname, $the_line, \@events);
	}
    }
    my $timestamp = ftimestamp($fname);

    return (\@events, $timestamp);
}

# Gets the list of dependency-affecting events that are present in a
# source file.  These may be either already in the cache, or else they
# are read in using scan_src.
sub src_events {
    my $fname = shift;
    my $evcache = shift;
    my $checked = shift;
    my $parent = shift;
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
    my $relname = shift;
    my $basename = shift;
    my $dirname = shift;
    my $local_dirs = shift;
    my $cmd = shift;
    my $ext = shift;
    my $fullname;
    if ($dirname) {
	my $dirpath = lookup_colon_dir($dirname, $local_dirs);
	unless (defined($dirpath)) {
	    print "Warning: Unknown :dir entry in ($cmd \"$relname\" :dir $dirname) for $basename\n";
	    print_dirs($local_dirs) if $debugging;
	    return 0;
	}
	$fullname = canonical_path(rel_path($dirpath, $relname . $ext));
    } else {
	my $dir = dirname($basename);
	$fullname = canonical_path(rel_path($dir, $relname . $ext));
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
	$deps,              # file dependency list (accumulator)
	$book_only,         # Only record include-book dependencies
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
    print "$src_deps_depth src_deps $fname, $book_only\n"  if $debugging;
    my $events = src_events($fname, $cache, $tscache, $parent);
    if ($debugging) {
	print "events: $fname";
	print_events($events);
    }
    my $two_pass = 0;

    foreach my $event (@$events) {
	my $type = $event->[0];
	if ($type eq $add_dir_event) {
	    my $name = $event->[1];
	    my $dir = $event->[2];
	    my $basedir = dirname($fname);
	    $local_dirs->{$name} = canonical_path(rel_path($basedir,
							   $dir));
	    print "src_deps: add_dir $name $local_dirs->{$name}\n" if
		$debugging;
	} elsif ($type eq $include_book_event) {
	    my $bookname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($bookname, $fname, $dir,
					      $local_dirs,
					      "include-book",
					      ".cert");
	    print "include-book fullname: $fullname\n" if $debugging;
	    $fullname && push(@$deps, $fullname);
	} elsif ($type eq $depends_on_event && !$book_only) {
	    my $depname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($depname, $fname, $dir,
					      $local_dirs,
					      "depends-on", "");
	    $fullname && push(@$deps, $fullname);
	} elsif ($type eq $loads_event) {
	    my $srcname = $event->[1];
	    my $dir = $event->[2];
	    my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
					      $local_dirs, "loads", "");
	    if ($fullname) {
		push(@$deps, $fullname) unless $book_only;
		my $local_two_pass = src_deps($fullname, $cache,
					      $local_dirs, $deps,
					      $book_only,
					      $tscache,
					      $ld_ok,
					      $seen,
		                              $fname);
		$two_pass = $two_pass || $local_two_pass;
	    }
	} elsif ($type eq $two_pass_event) {
	    $two_pass = 1;
	} elsif ($type eq $ld_event) {
	    if ($ld_ok) {
		my $srcname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
						  $local_dirs, "ld", "");
		if ($fullname) {
		    push(@$deps, $fullname) unless $book_only;
		    my $local_two_pass = src_deps($fullname, $cache,
						  $local_dirs, $deps,
						  $book_only,
						  $tscache,
						  $ld_ok,
						  $seen,
			                          $fname);
		    $two_pass = $two_pass || $local_two_pass;
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
    return $two_pass;
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


# Find dependencies of a cert file, here passed in without extension.
# Calls src_deps to get the dependencies of the .acl2 and book files.
sub find_deps {
    my $base = shift;
    my $cache = shift;
    my $book_only = shift;
    my $tscache = shift;
    my $parent = shift;

    my $lispfile = $base . ".lisp";

    my $deps = $book_only ? [] : [ $lispfile ];
    my $local_dirs = {};
    my $book_two_pass = 0;
    my $acl2_two_pass = 0;
    # If a corresponding .acl2 file exists or otherwise if a
    # cert.acl2 file exists in the directory, we need to scan that for dependencies as well.
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
	push(@$deps, $acl2file) unless $book_only;
	$acl2_two_pass = src_deps($acl2file, $cache,
				  $local_dirs, 
				  $deps, 
				  $book_only, 
				  $tscache,
				  1,
				  {}, $lispfile);
    }
    
    # Scan the lisp file for include-books.
    $book_two_pass = src_deps($lispfile, $cache, $local_dirs, $deps,
			      $book_only, $tscache, 0, {}, $parent);

    if ($debugging) {
	print "find_deps $lispfile: \n";
	print_lst($deps);
    }
    
    if (!$book_only) {
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
	    push(@{$deps}, canonical_path($imagefile));
	    if (open(my $im, "<", $imagefile)) {
		my $line = <$im>;
		chomp $line;
		if ($line && ($line ne "acl2")) {
		    my $image = canonical_path(rel_path(dirname($base), $line));
		    if (! -e $image) {
			$image = which($line);
		    }
		    if (-e $image) {
			push(@{$deps}, canonical_path($image));
		    }
		}
		close $im;
	    } else {
		print "Warning: find_deps: Could not open image file $imagefile: $!\n";
	    }
	}
    }

    return ($deps, $acl2_two_pass || $book_two_pass);

}



# During a dependency search, this is run with $target set to each
# cert and source file in the dependencies of the top-level targets.
# If the target has been seen before, then it returns immediately.
# Otherwise, this calls on find_deps to get those dependencies.
sub add_deps {
    my $target = shift;
    my $cache = shift;
    my $seen = shift;
    my $sources = shift;
    my $tscache = shift;
    my $parent = shift;

    if (exists $seen->{$target}) {
	# We've already calculated this file's dependencies.
	return;
    }

    if ($target !~ /\.cert$/) {
	push(@{$sources}, $target);
	$seen->{$target} = 0;
	return;
    }

    if (excludep($target)) {
    	$seen->{$target} = 0;
    	return;
    }

    print "add_deps $target\n" if $debugging;

    my $local_dirs = {};
    my $base = $target;
    $base =~ s/\.cert$//;
    my $lispfile = $base . ".lisp";

    # Clean the cert and out files if we're cleaning.
    if ($clean_certs) {
	my $outfile = $base . ".out";
	my $timefile = $base . ".time";
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

    my ($deps, $two_pass) = find_deps($base, $cache, 0, $tscache, $parent);


    my $acl2xfile = $base . ".acl2x";
    if ($two_pass) {
	$seen->{$target} = [ $acl2xfile ];
	$seen->{$acl2xfile} = $deps;
    } else {
	$seen->{$target} = $deps;
    }

    if ($print_deps) {
	print "Dependencies for $target:\n";
	foreach my $dep (@{$deps}) {
	    print "$dep\n";
	}
	print "\n";
    }

    # Run the recursive add_deps on each dependency.
    foreach my $dep  (@{$deps}) {
	add_deps($dep, $cache, $seen, $sources, $tscache, $target);
    }
    

    # If this target needs an update or we're in all_deps mode, we're
    # done, otherwise we'll delete its entry in the dependency table.
    unless ($all_deps) {
	# To fix this for two-pass files, 
	my $update_target = $two_pass ? $acl2xfile : $target;
	my $needs_update = (! -e $update_target);
	if (! $needs_update) {
	    foreach my $dep (@{$deps}) {
		if ($seen->{$dep} || (! -e $dep) || newer_than($dep, $update_target)) {
		    $needs_update = 1;
		    last;
		}
	    }
	}
	if (! $needs_update) {
	    $seen->{$update_target} = 0;
	}
	if ($two_pass &&
	    (! $seen->{$acl2xfile}) &&
	    (-e $target) &&
	    (! newer_than($acl2xfile, $target))) {
	    $seen->{$target} = 0;
	}
    }

}

sub read_targets {
    my $fname=shift;
    my $targets=shift;
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



sub compute_savings
{
    my $costs = shift;
    my $basecosts = shift;
    my $targets_ref = shift;
    my $debug = shift;
    my $deps_ref = shift;

    my @targets = @$targets_ref;
    my %deps = %$deps_ref;

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

	# Get the max savings from speeding up the book:
	# set the file base cost to 0 and recompute crit path.
	my %tmpcosts = ();
	my @tmpwarns = ();
	$basecosts->{$critfile} = 0.0;
	compute_cost_paths(\%deps, $basecosts, \%tmpcosts, \@tmpwarns);
	(my $tmptop, my $tmptopcost) = find_most_expensive(\@targets, \%tmpcosts);
	my $speedup_savings = $topbook_cost - $tmptopcost;
	$speedup_savings = $speedup_savings || 0.000001;

	# Get the max savings from removing the book:
	# set the file total cost to 0 and recompute crit path.
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

    return \%savings;
}


# The following "1" is here so that loading this file with "do" or "require" will succeed:
1;
