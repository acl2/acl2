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

package Bookscan;
use strict;
use warnings;

# Functions to scan files for various forms

use base 'Exporter';

our @EXPORT = qw(
add_dir_event
include_book_event
depends_on_event
depends_rec_event
loads_event
cert_param_event
ld_event
ifdef_event
endif_event
ifdef_define_event
set_max_mem_event
set_max_time_event
pbs_event
scan_src
scan_src_run
parse_params
);

my $debugging = 0;

sub set_debugging () {
    $debugging = shift;
}

# "Event" types:
sub add_dir_event () { return 'add-include-book-dir'; }
sub include_book_event () { return 'include-book'; }
sub depends_on_event () { return 'depends-on'; }
sub depends_rec_event () { return 'depends-rec'; }
sub loads_event () { return 'loads'; }
sub cert_param_event () { return 'cert_param'; }
sub ld_event () { return 'ld'; }
sub ifdef_event () { return 'ifdef'; }
sub endif_event () { return 'endif'; }
sub ifdef_define_event () { return 'ifdef-define'; }
sub set_max_mem_event () { return 'set-max-mem'; }
sub set_max_time_event () { return 'set-max-time'; }
sub pbs_event () { return 'pbs'; }

sub print_scanevent {
    my ($fname,$args) = @_;    
    print "$fname: ";
    foreach my $arg (@$args) {
	$arg && print " $arg";
    }
    print "\n";
}


sub debug_print_event {
    my ($fname,$args) = @_;
    if ($debugging) {
	print_scanevent($fname, $args);
    }
}


sub scan_ifdef {
    my ($base,$the_line) = @_;

    my @res = $the_line =~ m/^[^;]* # not commented
                             \(\s*
                             (?:[^\s():]*::)? # package prefix
                             if(?<negate>n?)def \s+
                             "(?<var>\w*)"
                             /xi;
    if (@res) {
	return [ifdef_event, $+{negate} ? 1 : 0, $+{var}];
    }
    return 0;
}

sub scan_endif {
    my ($base,$the_line) = @_;

    my @res = $the_line =~ m/^[^;]* # not commented
                             :endif \s* \)
                             /xi;
    if (@res) {
	return [endif_event];
    }
    return 0;
}

sub scan_ifdef_define {
    my ($base,$the_line) = @_;

    my @res = $the_line =~ m/^[^;]* # not commented
                             \(\s*
                             (?:[^\s():]*::)? # package prefix
                             ifdef-(?<negate>un)?define(?<nonloc>!?) \s+
                             "(?<var>\w*)"
                             /xi;
    if (@res) {
	my $ans = [ifdef_define_event, $+{negate} ? 1 : 0, $+{var}, ($+{nonloc} eq "!") ? 0 : 1 ];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}


sub scan_add_dir {
    my ($base,$the_line) = @_;

    # Check for ADD-INCLUDE-BOOK-DIR commands
    # my $regexp = "^[^;]*\\([\\s]*add-include-book-dir!?[\\s]+:([^\\s]*)[\\s]*\"([^\"]*[^\"/])/?\"";
    my $res = $the_line =~
	m/^[^;]* # not commented
          \(\s*
            (?:[^\s():]*::)?   # package prefix
            add-include-book-dir
            (?<nonloc>!?)
            \s+
            :(?<name>[^\s]*)
            \s+
            "(?<dir>[^"]*[^"\/])  # dir string except for possible trailing slash
            \/?"
         /xi;
    if ($res) {
	my $ans = [add_dir_event, uc($+{name}), $+{dir}, ($+{nonloc} eq "!") ? 0 : 1 ];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}


sub scan_include_book {
    my ($base,$the_line, $islocal) = @_;

    my @res = $the_line =~
	m/^[^;]*?   # not commented. Minimal match so we don't miss the optional local.
          (?<local>
               \(\s*
               (?:[^\s():]*::)? # package prefix
               local
               \s*)?  # optional local prefix
          \(\s*
           (?:[^\s():]*::)? # package prefix
           include-book
           \s*
           "(?<book>[^"]*)"
           (?:          # optional :dir argument
              [^;]* :dir \s*
              :(?<dirname>[^\s()]*))?
           (?: .*;.*
            (?<noport>no[_-]port))? # optional no-port comment
       /xi;
    if (@res) {
	$islocal = $islocal || ($+{local} ? 1 : 0);
	my $ans = [include_book_event, $+{book}, uc($+{dirname} || ""), $+{noport} ? 1 : 0, $islocal ];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}


sub scan_depends_on {
    my ($base,$the_line) = @_;

    my $regexp = "\\([\\s]*depends-on[\\s]*\"([^\"]*)\"(?:[^;]*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	debug_print_event($base, "depends_on", \@res);
	# Disallow depends-on of a certificate, for now.
	if ($res[0] =~ m/\.cert$/) {
	    STDERR->print("**************************** WARNING **************************************\n");
	    STDERR->print("$base has a \'depends-on\' dependency on a certificate, $res[0].\n");
	    STDERR->print("It is better to use \'include-book\' (in a multiline comment, if necessary)\n");
	    STDERR->print("to specify dependencies on books, because \'depends-on\' doesn't trigger\n");
	    STDERR->print("a scan of the target's dependencies.\n");
	    STDERR->print("***************************************************************************\n");
	}
	my $ans = [depends_on_event, $res[0], uc($res[1] || "")];
	debug_print_event($base, $ans);
	return $ans;
    }
}

sub scan_depends_rec {
    my ($base,$the_line) = @_;

    my $regexp = "\\([\\s]*depends-rec[\\s]*\"([^\"]*)\"(?:[^;]*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	my $ans = [depends_rec_event, $res[0], uc($res[1] || "")];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}

sub scan_loads {
    my ($base,$the_line) = @_;

    my $regexp = "\\([\\s]*loads[\\s]*\"([^\"]*)\"(?:[^;]*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	my $ans = [loads_event, $res[0], uc($res[1] || "")];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}


# Cert_param lines are currently of the form:
# cert_param: ( foo = bar , baz = 1 , bla )
# (the whitespace is optional.)
# An entry without an = is just set to 1.
sub parse_params {
    my $param_str = shift;
    my @params = split(/,/, $param_str);
    my @pairs = ();
    foreach my $param (@params) {
	$param =~ s/^\s+//;
	$param =~ s/\s+$//; #remove leading/trailing whitespace
	my @assign = $param =~ m/([^\s=]*)[\s]*=[\s]*([^\s=]*)/;
	if (@assign) {
	    push(@pairs, [$assign[0], $assign[1]]);
	} else {
	    push(@pairs, [$param, 1]);
	}
    }
    return \@pairs;
}



my $two_pass_warning_printed = 0;

sub scan_cert_param {
    my ($base,$the_line) = @_;

    my $regexp = "cert[-_]param[\\s]*:?[\\s]*\\(?([^)]*)\\)?";
    my @match = $the_line =~ m/$regexp/;
    if (@match) {
	debug_print_event($base, "cert_param", \@match);
	my $pairs = parse_params($match[0]);
	return [cert_param_event, $pairs];
    }
    $regexp = ";; two-pass certification";
    if ($the_line =~ m/$regexp/) {
	if ($two_pass_warning_printed) {
	    print STDERR "$base has two-pass certification directive\n";
	} else {
	    $two_pass_warning_printed = 1;
	    print STDERR "\nin $base:\n";
	    print STDERR "Note: Though we still recognize the \";; two-pass certification\"\n";
	    print STDERR "directive, it is deprecated in favor of:\n";
	    print STDERR ";; cert_param: (acl2x)\n\n";
	}
	return [cert_param_event, [["acl2x", 1]]];
    }
    $regexp = "\\([\\s]*check-hons-enabled[\\s]+\\(:book";
    if ($the_line =~ m/$regexp/) {
	return [cert_param_event, [["hons-only", 1]]];
    }
    return 0;
}


sub scan_ld {
    my ($base,$the_line) = @_;

    # Check for LD commands
    my $regexp = "^[^;]*\\([\\s]*ld[\\s]*\"([^\"]*)\"(?:[^;]*:dir[\\s]*:([^\\s)]*))?";
    my @res = $the_line =~ m/$regexp/i;
    if (@res) {
	my $ans = [ld_event, $res[0], $res[1]];
	debug_print_event($base, $ans);
	return $ans;
    }
    return 0;
}


sub parse_max_mem_arg
{
    # Try to parse the "..." part of (set-max-mem ...), return #GB needed
    my $filename = shift;
    my $arg = shift;
    my $ret = 0;

    if ($arg =~ m/\(\* ([0-9]+) \(expt 2 30\)\)/) {
	# (* n (expt 2 30)) is n gigabytes
	$ret = $1;
    }
    elsif ($arg =~ m/\(\* \(expt 2 30\) ([0-9]+)\)/) {
	# (* (expt 2 30) n) is n gigabytes
	$ret = $1;
    }
    elsif ($arg =~ m/^\(expt 2 ([0-9]+)\)*$/) {       # Example: arg is (expt 2 36))
	my $expt  = $1;                               # 36
	my $rexpt = ($expt > 30) ? ($expt - 30) : 0;  # 6  (but at least 0 in general)
	$ret      = 2 ** $rexpt;                      # 64 (e.g., 2^6)
    }
    else {
	print STDERR "Warning in $filename: skipping unsupported set-max-mem line: $arg\n";
	print STDERR "Currently supported forms:\n";
	print STDERR "  - (set-max-mem (expt 2 k))\n";
	print STDERR "  - (set-max-mem (* n (expt 2 30)))\n";
	print STDERR "  - (set-max-mem (* (expt 2 30) n))\n";
    }
    return $ret;
}

sub scan_max_mem {
    my ($base, $the_line) = @_;
    if ($the_line =~ m/^[^;]*\((?:acl2::)?set-max-mem (.*)\)/) {
	my $max_mem = parse_max_mem_arg($base, $1);
	if ($max_mem) {
	    return [ set_max_mem_event, $max_mem ];
	}
	return 0;
    }
    return 0;

}

sub scan_max_time {
    my ($base, $the_line) = @_;
    if ($the_line =~ m/^[^;]*\((?:acl2::)?set-max-time ([0-9]*)\)/) {
	return [ set_max_time_event, $1 ];
    }
    return 0;
}

sub scan_pbs {
   my ($base, $the_line) = @_;
   if ($the_line =~ m/^;PBS (.*)$/) {
       return [ pbs_event, $1 ];
   }
   return 0;
}

sub scan_local {
    # If the line ends with "(local" (with possible whitespace,
    # package prefix, and/or trailing comment), return 1.
    my ($base, $the_line) = @_;
    if ($the_line =~ m/^[^;]*           # disallow comment but allow other leading trash
                      \( \s*
                      (?:[^\s():]*::)?  # package prefix
                      local
                      \s*               # allow only whitespace or comment after local
                      (?:;.*)?
                      $/xi) {
	return 1;
    }
    return 0;
}

sub scan_acl2devel {
    my ($base, $the_line) = @_;
    if ($the_line =~ m/^[^;]*           # disallow comment but allow other leading trash
                      \#\+acl2-devel
                      \s*               # allow only whitespace or comment after #+acl2-devel
                      (?:;.*)?
                      $/xi) {
	return 1;
    }
    return 0;


}

sub start_acl2devel_event {

    return [ifdef_event, 0, "ACL2_DEVEL"];

}

sub end_acl2devel_event {
    return [endif_event]
}

# Scans a source file line by line to get the list of
# dependency-affecting events.
sub scan_src {
    my $fname = shift;
    my @events = ();
    if (open(my $file, "<", $fname)) {
	my $islocal = 0;
	my $acl2devel = 0;
	while (my $the_line = <$file>) {
	    if ($the_line =~ m/^\s*$/) {
		# just whitespace so skip, in particular don't remove $islocal or $acl2devel
	    } else {
		my $event = scan_include_book($fname, $the_line, $islocal)
		    || scan_cert_param($fname, $the_line)
		    || scan_depends_on($fname, $the_line)
		    || scan_depends_rec($fname, $the_line)
		    || scan_ifdef($fname, $the_line)
		    || scan_endif($fname, $the_line)
		    || scan_ifdef_define($fname, $the_line)
		    || scan_loads($fname, $the_line)
		    || scan_ld($fname, $the_line)
		    || scan_add_dir($fname, $the_line)
		    || scan_max_mem($fname, $the_line)
		    || scan_max_time($fname, $the_line)
		    || scan_pbs ($fname, $the_line);
		if ($event) {
		    push @events, $event;
		}
		if ($acl2devel) {
		    push @events, end_acl2devel_event();
		    $acl2devel = 0;
		}
		$islocal = scan_local($fname, $the_line);
		$acl2devel = scan_acl2devel($fname, $the_line);
		if ($acl2devel) {
		    push @events, start_acl2devel_event();
		}
	    }
	}
	close($file);
    }

    return \@events;
}

# Scans a source file for runtime information.  Not trying to get
# dependencies, just max-mem, max-time, and .port file stuff.
sub scan_src_run {
    my $fname = shift;
    my @events = ();
    if (open(my $file, "<", $fname)) {
	while (my $the_line = <$file>) {
	    my $event = scan_include_book($fname, $the_line)
		|| scan_max_mem($fname, $the_line)
		|| scan_max_time($fname, $the_line)
		|| scan_ifdef($fname, $the_line)
		|| scan_endif($fname, $the_line)
		|| scan_ifdef_define($fname, $the_line)
		|| scan_pbs($fname, $the_line);
	    if ($event) {
		push @events, $event;
	    }
	}
	close($file);
    }
    return \@events;
}

1;
