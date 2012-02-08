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
    if (! -d $dir) {
	print "Oops, trying to go into $dir\n";
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
    my ($path, $warnings, $use_realtime, $pcert) = @_;

    if ($pcert) {
	$path =~ s/\.cert$/\.convert\.time/;
	$path =~ s/\.pcert$/\.pcert\.time/;
	$path =~ s/\.acl2x$/\.acl2x\.time/;
    } else {
	$path =~ s/\.cert$/\.time/;
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
	    return 0;
	}
	if ($use_realtime) {
	    return 0.0 + $realtime;
	} else {
	    return 0.0 + $usertime + $systime;
	}
    } else {
	push(@$warnings, "Could not open $path: $!\n");
	return 0;
    }
}

sub cert_to_acl2x {
    my $cert = shift;
    (my $acl2x = $cert) =~ s/\.cert$/\.acl2x/;
    return $acl2x;
}

sub cert_to_pcert {
    my $cert = shift;
    (my $pcert = $cert) =~ s/\.cert$/\.pcert/;
    return $pcert;
}

sub cert_is_two_pass {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[1];
}

sub cert_deps {
    my ($cert, $depmap) = @_;
    my $entry = $depmap->{$cert};
    return $entry && $entry->[0];
}


sub read_costs {
    my ($deps, $basecosts, $warnings, $use_realtime, $pcert) = @_;

    foreach my $certfile (keys %{$deps}) {
	if ($pcert) {
	    my $pcertfile = cert_to_pcert($certfile);
	    my $acl2xfile = cert_to_acl2x($certfile);
	    $basecosts->{$certfile} = get_cert_time($certfile, $warnings, $use_realtime, $pcert);
	    $basecosts->{$pcertfile} = get_cert_time($pcertfile, $warnings, $use_realtime, $pcert);
	    $basecosts->{$acl2xfile} = get_cert_time($acl2xfile, $warnings, $use_realtime, $pcert);
	} else {
	    $basecosts->{$certfile} = get_cert_time($certfile, $warnings, $use_realtime, $pcert);
	    if (cert_is_two_pass($certfile, $deps)) {
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
	if ($file =~ /\.(cert|acl2x|pcert)$/) {

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

    if (exists $costs->{$target} || ! ($target =~ /\.(cert|acl2x|pcert)$/)) {
	return $costs->{$target};
    }

    # put something in $costs->{$target} so that we don't loop
    $costs->{$target} = 0;

    my $certtime = $basecosts->{$target};
    
    my $targetdeps;
    if ($pcert) {
	$targetdeps = [];
	if ($target =~ /\.pcert$/) {
	    ## The only dependency is the corresponding .acl2x.
	    (my $acl2xfile = $target) =~ s/\.pcert$/\.acl2x/;
	    push (@$targetdeps, $acl2xfile);
	} elsif ($target =~ /\.acl2x$/) {
	    ## The dependencies are the dependencies of the cert file, but
	    ## with each .cert replaced with the corresponding .acl2x.
	    (my $certfile = $target) =~ s/\.acl2x$/\.cert/;
	    my $certdeps = cert_deps($certfile, $deps);
	    foreach my $dep (@$certdeps) {
		my $depacl2x = cert_to_acl2x($dep);
		push(@$targetdeps, $depacl2x);
	    }
	} else { # $target =~ /\.cert$/
	    # The dependencies are the ones saved in $deps, plus the corresponding pcert.
	    my $certdeps = cert_deps($target, $deps);
	    push (@$targetdeps, @$certdeps);
	    my $pcertfile = cert_to_pcert($target);
	    push (@$targetdeps, $pcertfile);
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
	    if ($dep =~ /\.(cert|acl2x|pcert)$/) {
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
my $believe_cache = 0;
my $bin_dir = "";

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
    $bin_dir = $opts->{"bin_dir"};
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
    $local_dirs && ($dirpath = $local_dirs->{$name});
    if (! defined($dirpath)) {
	$dirpath = $dirs{$name} ;
    }
    return $dirpath;
}

sub debug_print_event {
    my ($fname,$cmd,$args) = @_;
    if ($debugging) {
	print "$fname: $cmd ";
	foreach my $arg (@$args) {
	    $arg && print " $arg";
	}
	print "\n";
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


sub get_two_pass {
    my ($base,$the_line,$events) = @_;

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
    my ($base,$cache,$book_only,$tscache,$parent) = @_;

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
	    my $line;
	    if (open(my $im, "<", $imagefile)) {
		$line = <$im>;
		close $im;
		chomp $line;
	    } else {
		print "Warning: find_deps: Could not open image file $imagefile: $!\n";
	    }
	    if ($line && ($line ne "acl2")) {
		if ($bin_dir) {
		    my $image = canonical_path(rel_path($bin_dir, $line));
		    push(@{$deps}, $image);
		} else {
		    print "Warning: no --bin set, so not adding image dependencies,\n";
		    print " e.g.   $base.cert : $line\n";
		}
	    }
	}
    }

    return ($deps, $acl2_two_pass || $book_two_pass);

}



# Given that the dependency map $depmap is already built, this collects
# the full set of sources and targets needed for a given file.
sub deps_dfs {
    my ($target, $depmap, $visited, $sources, $certs) = @_;

    if ($visited->{$target}) {
	return;
    }

    $visited->{$target} = 1;

    if ($target !~ /\.(cert|acl2x|pcert)$/) {
	push(@{$sources}, $target);
	return;
    }

    push (@$certs, $target);
    my $deps = cert_deps($target, $depmap);

    foreach my $dep (@$deps) {
	deps_dfs($dep, $depmap, $visited, $sources, $certs);
    }
}

    

# During a dependency search, this is run with $target set to each
# cert and source file in the dependencies of the top-level targets.
# If the target has been seen before, then it returns immediately.
# Otherwise, this calls on find_deps to get those dependencies.
sub add_deps {
    my ($target,$cache,$depmap,$sources,$tscache,$parent) = @_;

    if ($target !~ /\.cert$/) {
	$sources->{$target} = 1;
	return;
    }

    if (exists $depmap->{$target}) {
	# We've already calculated this file's dependencies.
	return;
    }

    if (excludep($target)) {
    	$depmap->{$target} = [];
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


    $depmap->{$target} = [ $deps, $two_pass ] ;

    if ($print_deps) {
	print "Dependencies for $target:\n";
	foreach my $dep (@{$deps}) {
	    print "$dep\n";
	}
	print "\n";
    }

    # Run the recursive add_deps on each dependency.
    foreach my $dep  (@{$deps}) {
	add_deps($dep, $cache, $depmap, $sources, $tscache, $target);
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

# Takes a list of inputs containing some filenames and some labels
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
	    my $name = to_basename(substr($str,3));
	    (my $deps, my $two_pass) = find_deps($name, $cache, 1, $tscache, 0);
	    push (@targets, @$deps);
	    push (@$label_targets, @$deps) if $label_started;
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
	    my $target = to_basename($str) . ".cert";
	    push(@targets, $target);
	    push(@$label_targets, $target) if $label_started;
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


# The following "1" is here so that loading this file with "do" or "require" will succeed:
1;
