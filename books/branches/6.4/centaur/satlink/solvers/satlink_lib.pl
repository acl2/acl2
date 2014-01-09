# SATLINK - Link from ACL2 to SAT Solvers
# Copyright (C) 2013 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later
# version.  This program is distributed in the hope that it will be useful but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.  You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
#
# Original author: Jared Davis <jared@centtech.com>

use warnings;
use strict;
require File::Temp;
use File::Copy "cp";

# SCRIPT is the compact name of the script being run, e.g., "glucose-cert", for
# use in debugging and error messages.

my $SCRIPT = $0;
if ($SCRIPT =~ m|\/([^/]*)$|) {
    $SCRIPT = $1;
}

sub debug
{
    my $msg = shift;
    print "c $SCRIPT: $msg\n";
}


# Stupid little mechanism for cleaning up temporary files.  The normal way of
# immediate unlinking them won't work, because we have to tell the sub-programs
# what files to use, etc.

my @satlink_rm_files = ();

sub satlink_temp_file
{
    my $fd = File::Temp->new( TEMPLATE => 'TMP-satlink-$PID.XXXXXX', UNLINK => 0 );
    my $filename = $fd->filename;
    push(@satlink_rm_files, $filename);
    return $filename;
}

sub satlink_cleanup
{
    unlink(@satlink_rm_files);
}

sub fatal
{
    my $msg = shift;
    print "c $SCRIPT: Fatal error: $msg\n";
    satlink_cleanup();
    exit(1);
}

sub satlink_interrupt_handler
{
    fatal("Interrupted");
}

$SIG{'INT'} = 'satlink_interrupt_handler';

sub run_sat_solver
{
    # We run a SAT solver on some arguments, echoing all output EXCEPT for
    # solution lines.  We return "SATISFIABLE" or "UNSATISFIABLE" per the SAT
    # solver's output, or call fatal() if the output doesn't make sense.

    my ($solver_cmd, $solver_args) = @_;
    my @args = @$solver_args;

    debug("Solver command: $solver_cmd @args");

    my $solution = "";
    my $sat_start = time();

    open(my $fd, "-|", $solver_cmd, @args)
	or fatal("can't run $solver_cmd: $!");

    while(my $line = <$fd>)
    {
	if ($line =~ /^s (.+)$/) {
	    debug("Intercepted solution line ($1).");
	    fatal("multiple solution lines!") if ($solution);
	    $solution = $1;
	}
	else {
	    print $line;
	}
    }

    close($fd)
	or debug($! ? "Error closing $solver_cmd pipe: $!"
       	            : "Exit status " . ($? >> 8) . " from $solver_cmd.");

    debug("Sat solving took " . (time() - $sat_start) . " seconds.");

    if ($solution ne "SATISFIABLE" && $solution ne "UNSATISFIABLE") {
	fatal("unrecognized solution $solution");
    }

    return $solution;
}

sub check_unsat_proof
{
    # Call drup-trim to check an UNSAT proof.  On any failure we abort by
    # calling fatal().  That is, if this function returns, then the UNSAT proof
    # was verified successfully.

    my ($infile, $proof_file) = @_;
    my @args = ($infile, $proof_file);

    # I'll just hard-code this in for now.
    my $cmd = "drup-trim";

    debug("Checker command: $cmd @args\n");

    my $status = "";
    my $start_time = time();

    open(my $fd, "-|", $cmd, @args)
	or fatal("can't run $cmd: $!");

    while(my $line = <$fd>)
    {
	if ($line =~ /^s (.+)$/) {
	    debug("Intercepted status line ($1).");
	    fatal("multiple status lines!") if ($status);
	    $status = $1;
	}
	else {
	    print $line;
	}
    }

    close($fd)
	or debug($! ? "Error closing $cmd pipe: $!"
       	            : "Exit status " . ($? >> 8) . " from $cmd.");

    debug("Checking took " . (time() - $start_time) . " seconds.");

    if ($status eq "VERIFIED" || $status eq "TRIVIAL UNSAT") {
	# Seems good.
	return;
    }

    debug("Woah -- Proof rejected!");
    debug("Copying offending files so you can debug this.");
    cp($infile,     "satlink-rejected.in");
    cp($proof_file, "satlink-rejected.proof");
    debug("Input file: satlink-rejected.in");
    debug("Proof file: satlink-rejected.proof");
    fatal("Invalid proof!");
}


sub run_sat_and_check
{
    # Top level function for running SAT and checking unsat proofs.

    my ($solver, $args, $infile, $proof_file) = @_;

    my $solution = run_sat_solver($solver, $args);

    if ($solution eq "SATISFIABLE") {
	debug("Solver says SAT, so not checking an UNSAT proof.");
	print "s SATISFIABLE\n";
	return;
    }

    if ($solution ne "UNSATISFIABLE") {
	fatal("Programming error: this can never happen.");
    }

    if ($ENV{"SATLINK_TRUST_SOLVER"}) {
	debug("Not checking the proof since SATLINK_TRUST_SOLVER=1");
	print "s UNSATISFIABLE\n";
	return;
    }

    debug("Verifying the UNSAT proof.\n");
    check_unsat_proof($infile, $proof_file);
    print "s UNSATISFIABLE";
}


1;
