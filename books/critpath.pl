#!/usr/bin/env perl

######################################################################
## NOTE.  This file is not part of the standard ACL2 books build
## process; it is part of an experimental build system that is not yet
## intended, for example, to be capable of running the whole
## regression.  The ACL2 developers do not maintain this file.
##
## Please contact Sol Swords <sswords@cs.utexas.edu> with any
## questions/comments.
######################################################################

# Copyright 2008 by Sol Swords.



#; This program is free software; you can redistribute it and/or modify
#; it under the terms of the GNU General Public License as published by
#; the Free Software Foundation; either version 2 of the License, or
#; (at your option) any later version.

#; This program is distributed in the hope that it will be useful,
#; but WITHOUT ANY WARRANTY; without even the implied warranty of
#; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#; GNU General Public License for more details.

#; You should have received a copy of the GNU General Public License
#; along with this program; if not, write to the Free Software
#; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


# This program displays the longest dependency chain leading up to a
# certified book, measured in sequential certification time.  This is
# the amount of time it would take to certify your book if you had as
# many parallel processors as could be used, each running at a fixed
# speed.

# Steps for using this program:

# 0. Ensure that you have GNU time installed and accessible by running
# "env time".   For example, running "env time --version" should print
# something like "GNU time 1.7".

# 1. Use cert.pl to certify all the books you're interested in (from
# scratch) with the TIME_CERT environment variable set to "yes" and
# exported.
# For example,
#  setenv TIME_CERT yes   # in csh, or
#  export TIME_CERT=yes   # in bash
#  cert.pl top.lisp -c    # clean
#  cert.pl top.lisp -j 8  # recertify using 8 parallel processors

# 2. Run this program as follows:
# critpath.pl <makefile> <top-book>
# Here the <makefile> should be the Makefile-tmp produced by cert.pl
# in step 1.  However, if this gets deleted, you can recreate it using
# cert.pl -s <makefile> <top-book>
# <top-book> should be the .lisp or .cert file of the book of
# interest.



use strict;
use warnings;
use File::Basename;
use File::Spec;
use Cwd;
use Cwd 'abs_path';

sub rm_dotdots {
    my $path = shift;
    while ($path =~ s/( |\/)[^\/\.]+\/\.\.\//$1/g) {}
    return $path;
}

sub rel_path {
    my $base = shift;
    my $path = shift;
    if (substr($path,0,1) eq "/") {
	return $path;
    } else {
	return "$base/$path";
    }
}

sub rec_readlink {
    my $file = shift;
    my $last = $file;
    my $dest;
    while ($dest = readlink $last) {
	$last = rel_path(dirname($last),$dest);
    }
    return $last;
}

sub abs_canonical_path {
    my $path = shift;
    my $abspath = File::Spec->rel2abs(rec_readlink($path));
    my ($vol, $dir, $file) = File::Spec->splitpath($abspath);
    my $absdir = abs_path($dir);
    if ($absdir) {
	return File::Spec->catpath($vol, $absdir, $file);
    } else {
	print "Warning: canonical_path: Directory not found: " . $dir . "\n";
	return 0;
    }
}

my $base_path = abs_canonical_path(".");

sub canonical_path {
    my $abs_path = abs_canonical_path(shift);
    if ($base_path) {
	return File::Spec->abs2rel($abs_path, $base_path);
    } else {
	return $abs_path;
    }
}



# Given a .cert file, gets the total user + system time recorded in
# the corresponding .time file.  If not found, prints a warning and
# returns 0.
sub get_cert_time {
    my $path = shift;
    $path =~ s/\.cert$/\.time/;
    if (open (my $timefile, "<", $path)) {
	while (my $the_line = <$timefile>) {
	    my $regexp = "^([0-9]*\\.[0-9]*)user ([0-9]*\\.[0-9]*)system";
	    my @res = $the_line =~ m/$regexp/;
	    if (@res) {
		return 0.0 + $res[0] + $res[1];
	    }
	}
	print "Failed to read runtimes from file $path\n";
	return 0;
    } else {
	print "Failed to open time file $path\n";
	return 0;
    }
}


# Records a dependency graph between cert files by looking through the
# Makefile and adding an entry for each line matching *.cert : *.cert.

my %deps = ( );

sub mk_dep_graph {
    my $mkpath = shift;
    open (my $mkfile, "<", $mkpath)
	or die "Failed to open makefile $mkpath\n";
    my $regexp = "^(.*\\.cert)[\\s]*:[\\s]*(.*\\.cert)";
    while (my $teh_line = <$mkfile>) {
	my @res = $teh_line =~ m/$regexp/;
	if (@res) {
	    push(@{$deps{$res[0]}}, $res[1]);
	}
    }
}


# For each cert file in the dependency graph, records a maximum-cost
# path, the path's cost, and the cert's own cost.

my %costs = ( );

sub get_max_cost_path {
    my $certfile = shift;
    if ($costs{$certfile}) {
	return $costs{$certfile};
    }

    my $certtime = get_cert_time($certfile);
    my $certdeps = $deps{$certfile};
    my $maxcost = 0;
    my $maxpath = 0;
    foreach my $dep (@{$certdeps}) {
	my $depcosts = get_max_cost_path($dep);
	my $depcost = $ {$depcosts}[1];
	if ($depcost > $maxcost) {
	    $maxcost = $depcost;
	    $maxpath = $dep;
	}
    }

    $costs{$certfile} = [ $certtime, $maxcost + $certtime,
			  $maxpath ];
    return $costs{$certfile};
}


sub print_path {
    my $certfile = shift;

    my $costs = $costs{$certfile};
    my @shortcert = $certfile =~ m/^.*\/([^\/]*\/[^\/]*)$/;

    formline (<<'END', $shortcert[0] || $certfile, $ {$costs}[0], $ {$costs}[1]);
@<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< @######.## @###########.##
END
    
    print $^A;
    $^A = "";

    if ($ {$costs}[2]) {
	print_path ($ {$costs}[2]);
    }
}


# Jared added this to report the individual times.
sub report_individual_files 
{
    print "\n\nIndividual times for all files (sorted by name; not just the critical path):\n\n";

    my %lines = ();

    foreach my $filename (keys %deps) 
    {
         my @shortcert = $filename =~ m/^.*\/([^\/]*\/[^\/]*)$/;
         my $shortname = $shortcert[0] || $filename;
         my $indiv_time = get_cert_time $filename;
         $lines{$shortname} = $indiv_time;
    }

    foreach my $name ( sort(keys %lines) )
    {
        my $time = $lines{$name};
        formline (<<'END', $name, $time);
@<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< @######.##
END
        print $^A;
        $^A = "";
    }
}
    

my $mkfile = canonical_path(shift);
my $topfile = canonical_path(shift);
$topfile =~ s/\.lisp$/.cert/;



mk_dep_graph $mkfile;
get_max_cost_path $topfile;


print "\nCritical path:\n\n";
formline (<<'END', "File", "Time", "Cumulative");
@<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< @>>>>>>>>> @>>>>>>>>>>>>>>
END
print $^A;
$^A = "";

print_path ($topfile);

report_individual_files;
