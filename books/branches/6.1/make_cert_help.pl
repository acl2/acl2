#!/usr/bin/env perl

# cert.pl build system
# Copyright (C) 2008-2011 Centaur Technology
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
# Original authors: Sol Swords <sswords@centtech.com>
#                   Jared Davis <jared@centtech.com>
#
# NOTE: This file is not part of the standard ACL2 books build process; it is
# part of an experimental build system.  The ACL2 developers do not maintain
# this file.


# make_cert_help.pl -- this is a companion file that is used by "make_cert".
# It is the core script responsible for certifying a single ACL2 book.

# The code here is largely similar to the %.cert: %.lisp rule from
# Makefile-generic, but with several extensions.  For instance,
#
#   - We try to gracefully NFS lag, and
#   - We can certify certain books with other save-images, using .image files
#   - We support .acl2x files and two-pass certification,
#   - We support adding #PBS directives to limit memory and wall time
#   - We support running ACL2 via an external queuing mechanism.
#
# We only expect to invoke this through make_cert, so it is not especially
# user-friendly.  We rely on several environment variables that are given to us
# by make_cert.  See make_cert for the defaults and meanings of ACL2,
# COMPILE_FLG, and other variables used in this script.

# Usage: make_cert_help.pl TARGET STEP
#   - TARGET is like "foo" for "foo.lisp"
#   - STEP is "cert", "acl2x", "acl2xskip", "acl2xcert", "pcert", or "convert"

# The meaning of the steps is as follows:
# "cert"      -- conventional single-pass certification
# "acl2x"     -- first pass of a two-pass certification, not skipping proofs
# "acl2xskip" -- first pass of a two-pass or provisional certification, skipping proofs
# "pcert"     -- second pass of a provisional certification
# "convert"   -- third pass of a provisional certification


use warnings;
use strict;
use File::Spec;
# problematic to get this from cpan on msys
# use File::Which qw(which);
use FindBin qw($RealBin);
use POSIX qw(strftime);
use Cwd;

(do "$RealBin/paths.pl") or die ("Error loading $RealBin/paths.pl:\n!: $!\n\@: $@\n");

sub trim
{
	my $str = shift;
	$str =~ s/^\s+//;
	$str =~ s/\s+$//;
	return $str;
}

sub read_whole_file
{
    my $filename = shift;
    open (my $fh, "<", $filename) or die("Can't open $filename: $!\n");
    local $/ = undef;
    my $ret = <$fh>;
    close($fh);
    return $ret;
}

sub read_whole_file_if_exists
{
    my $filename = shift;
    return "" if (! -f $filename);
    return read_whole_file($filename);
}


# Takes a string, a nesting depth, and a starting index.  Scans the
# string for parens and keeps track of the depth.  Stops when the
# depth reaches 0.  If it reaches the end of the string, returns the
# current depth.  Returns three results: a flag which is 1 if it
# reached the end before depth 0 and 0 otherwise, the nesting depth at
# the end (only valid if it reached the end), and the index after the
# closing paren.  BOZO doesn't care about string quotes etc.
sub find_matching_parens {
    my ($str, $depth, $pos) = @_;
    while (1) {
	my $next_open = index($str, "(", $pos);
	my $next_close = index($str, ")", $pos);
	my $open_next = ($next_open != -1)
	    && (($next_close == -1) || $next_open < $next_close);
	my $close_next = ($next_close != -1)
	    && (($next_open == -1) || $next_close < $next_open);
	if ($open_next) {
	    $pos = $next_open+1;
	    $depth = $depth+1;
	} elsif ($close_next) {
	    $pos = $next_close+1;
	    $depth = $depth-1;
	    if ($depth == 0) {
		return (0, -1, $pos);
	    }
	} else {
	    # reached end of string with no more parens
	    return (1, $depth, -1);
	}
    }
}

   
sub skip_certify_books {
    my $str = shift;
    my $pos = 0;
    my @strs = ();
    my @match;
    while ($str =~ m/(\((?:acl2::)?certify-book)/gi) {
	my $beg = pos($str) - length($1);
	my $end = pos($str);
	push (@strs, substr($str,$pos,$beg-$pos));
	my ($done, $depth, $newpos) = find_matching_parens($str, 1, $end);
	if ($done) {
	    return join("", @strs);
	}
	$pos = $newpos;
	pos($str) = $pos;
    }
    push (@strs, substr($str, $pos));
    return join("", @strs);
}


sub read_file_except_certify {
    my $filename = shift;
    my $str = read_whole_file($filename);
    return skip_certify_books($str);
    # my @lines = ();
    # open (my $fh, "<", $filename) or die("Can't open $filename: $!\n");
    # my $line;
    # my $parens_deep = -1;
    # while (my $line = <$fh>) {
    # 	chomp($line);
    # 	if ($parens_deep == -1) {
    # 	    my $start = index($line, "(certify-book"
    # 			      $line =~ s/\(certify-book [^)]*\)//;
    # 	push (@lines, $line);
    # }
    # my $ret = join("\n", @lines);
    # return $ret;
}

sub remove_file_if_exists
{
    my $filename = shift;
    if (-f $filename) {
	unlink($filename) or die("Can't remove $filename: $!\n");
    }
}

sub nfs_file_exists
{
    # In theory, this is just -f $filename.  In practice, NFS client caching
    # may mean that -f $filename does not mean what you think it does.
    #
    # Jared's notes.  I originally tried to just use a -f $filename when
    # waiting for NFS files to come into existence.  But it appears that, at
    # least under some configurations of NFS, the NFS client (not perl or
    # something) can cache whether a file exists or not.
    #
    # This caching can last for a long time, at least several minutes, perhaps
    # indefinitely.  (I literally went down the hall and got a lesson on NFS
    # from the sysamin, and when we came back to my office my "ls" loop was
    # still running and not seeing the file.)
    #
    # For our particular network setup, the file in question was not visible
    # from fv-hpc, but was visible from the compute nodes.  We used "df" to
    # investigate which NFS servers the compute nodes and fv-hpc were connected
    # to for that particular drive, and found that some nodes using the same
    # server could see the file.  Hence, we concluded it was not a server-side
    # issue.
    #
    # We then did an "ls" in the directory, and suddenly the client got a
    # refreshed view of the directory and could see the file.  So, it seems
    # that the client was caching the individual file, but not the directory
    # list.
    #
    # So, to really try to test whether the NFS file exists, we first do an
    # "ls" which apparently seems to be sufficient to clear the NFS cache for
    # that directory, and then ask if the file exists.  This seems to be good
    # enough for our setup.  If it doesn't work for somebody else's setup,
    # maybe they can figure out a better solution.

    my $filename = shift;
    my $blah = `ls`; # hit the directory again, to try to get NFS to not cache things
    return -f $filename;

#    my $output = `test -f '$filename'`;
#    my $status = $? >> 8;
#    return $status == 0;
}

sub wait_for_nfs
{
    my $filename = shift;
    my $max_lag = shift;
    for(my $i = 0; $i < $max_lag; $i++)
    {
	print "NFS Lag?  Waited $i seconds for $filename...\n";
	sleep(1);

	return 1 if nfs_file_exists($filename);
    }
    return 0;
}

sub write_whole_file
{
    my $filename = shift;
    my $contents = shift;

    open(my $fd, ">", $filename) or die("Can't open $filename: $!\n");
    print $fd $contents;
    close($fd);
}

sub parse_max_mem_arg
{
    # Try to parse the "..." part of (set-max-mem ...), return #GB needed
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
	print "Warning: skipping unsupported set-max-mem line: $arg\n";
	print "Currently supported forms:\n";
	print "  - (set-max-mem (expt 2 k))\n";
	print "  - (set-max-mem (* n (expt 2 30)))\n";
	print "  - (set-max-mem (* (expt 2 30) n))\n";
    }
    return $ret;
}

sub scan_for_set_max_mem
{
    my $filename = shift;

    open(my $fd, "<", $filename) or die("Can't open $filename: $!\n");
    while(<$fd>) {
	my $line = $_;
	chomp($line);
	if ($line =~ m/^[^;]*\((acl2::)?set-max-mem (.*)\)/)
	{
	    my $gb = parse_max_mem_arg($2);
	    return $gb;
	}
    }

    return 0;
}

sub scan_for_set_max_time
{
    my $filename = shift;

    open(my $fd, "<", $filename) or die("Can't open $filename: $!\n");
    while(<$fd>) {
	my $line = $_;
	chomp($line);
	if ($line =~ m/^[^;]*\((acl2::)?set-max-time ([0-9]*)\)/)
	{
	    my $minutes = $2;
	    return $minutes;
	}
    }
    return 0;
}

sub collect_ls_dirs {
# Hi.  This is a horrible hack to compensate for NFS lag.  In our
# setup, it seems to help to run "ls" on the directories containing
# our dependencies (otherwise they often are not there yet when we try
# to load them.)  To minimize the impact of this atrocity, we collect
# the full set of these directories and uniqify them so that our
# remote job doesn't do lots of redundant work.
    my ($prereqs, $startdir) = @_;
    my %dirs = ();

    foreach my $prereq (@$prereqs) {
	(my $vol, my $dir, my $file) = File::Spec->splitpath("$startdir/$prereq");
	my $fulldir = File::Spec->canonpath(File::Spec->catpath($vol, $dir, ""));

	$dirs{$fulldir} = 1;
    }

    my @dirnames = keys %dirs;

    return \@dirnames;
}

my $TARGET = shift;
my $STEP = shift;      # certify, acl2x, acl2xskip, pcertify, pcertifyplus, convert, or complete
my $ACL2X = shift;     # "yes" or otherwise no. use ACL2X file in certify/pcertify/pcertifyplus/convert steps
my $PREREQS = \@ARGV;

# print "Prereqs for $TARGET $STEP: \n";
# foreach my $prereq (@$PREREQS) {
#     print "$prereq\n";
# }

my $startdir = getcwd;
# my $prereq_dirs = collect_ls_dirs($PREREQS, $startdir);

my $TARGETEXT;
if ($STEP eq "complete" || $STEP eq "certify") {
    $TARGETEXT = "cert";
} elsif ($STEP eq "convert" || $STEP eq "pcertifyplus") {
    $TARGETEXT = "pcert1";
} elsif ($STEP eq "pcertify") {
    $TARGETEXT = "pcert0";
} elsif ($STEP eq "acl2x" || $STEP eq "acl2xskip") {
    $TARGETEXT = "acl2x";
} else {
    die("Unrecognized step type: $STEP");
}

# normalize acl2x flag to Boolean
$ACL2X = ($ACL2X eq "yes") ? ":acl2x t" : "";

my $INHIBIT     = $ENV{"INHIBIT"} || "";
my $HEADER      = $ENV{"OUTFILE_HEADER"} || "";
my $MAX_NFS_LAG = $ENV{"MAX_NFS_LAG"} || 100;
my $DEBUG       = $ENV{"ACL2_BOOKS_DEBUG"} ? 1 : 0;
my $FLAGS       = $ENV{"COMPILE_FLG"};
my $TIME_CERT   = $ENV{"TIME_CERT"} ? 1 : 0;
my $STARTJOB    = $ENV{"STARTJOB"} || "";
my $ON_FAILURE_CMD = $ENV{"ON_FAILURE_CMD"} || "";
my $ACL2           = $ENV{"ACL2"} || "acl2";
# Figure out what ACL2 points to before we switch directories.

if ($ENV{"ACL2_BIN_DIR"}) {
    (my $vol, my $dir, my $file) = File::Spec->splitpath($ENV{"ACL2_BIN_DIR"});
    my $canon_bin_dir = File::Spec->canonpath(File::Spec->catpath($vol, $dir, $file));
    print "canonical bin dir: $canon_bin_dir\n" if $DEBUG;
    $ENV{"PATH"} = $ENV{"PATH"} ? "$canon_bin_dir:$ENV{'PATH'}" : $canon_bin_dir;
}
# fix up the acl2 path as in cert.pl
my $devnull = File::Spec->devnull;
$ACL2 = path_import($ACL2);
my $default_acl2 = `which $ACL2 2>$devnull`;
if (($? >> 8) != 0) {
    print "Error: failed to find \$ACL2 ($ACL2) in the PATH.\n";
    exit(1);
}
chomp($default_acl2);

my $PCERT = "";
if ($STEP eq "pcertify") {
    $PCERT = ":pcert :create";
} elsif ($STEP eq "convert") {
    $PCERT = ":pcert :convert";
} elsif ($STEP eq "pcertifyplus") {
    $PCERT = ":pcert t";
} elsif ($STEP eq "complete") {
    $PCERT = ":pcert :complete";
}


if ($DEBUG)
{
    print "-- Starting up make_cert_help.pl in debug mode.\n";
    print "-- TARGET       = $TARGET\n";
    print "-- STEP         = $STEP\n";
    print "-- TARGETEXT    = $TARGETEXT\n";
    print "-- INHIBIT      = $INHIBIT\n";
    print "-- MAX_NFS_LAG  = $MAX_NFS_LAG\n";
    print "-- FLAGS        = $FLAGS\n";
    print "-- PCERT        = $PCERT\n";
    print "-- ACL2X        = $ACL2X\n";
    print "-- HEADER       = $HEADER\n";
    print "-- Default ACL2 = $default_acl2\n" if $DEBUG;
}

my $full_file = File::Spec->rel2abs($TARGET);
(my $vol, my $dir, my $file) = File::Spec->splitpath($full_file);
my $goal = "$file.$TARGETEXT";
my $printgoal = path_export($full_file);

print "Making $printgoal on " . strftime('%d-%b-%Y %H:%M:%S',localtime) . "\n";

my $fulldir = File::Spec->canonpath(File::Spec->catpath($vol, $dir, ""));
print "-- Entering directory $fulldir\n" if $DEBUG;
chdir($fulldir) || die("Error switching to $fulldir: $!\n");

my $status;
my $timefile = "$file.$TARGETEXT.time";
my $outfile = "$file.$TARGETEXT.out";

print "-- Removing files to be generated.\n" if $DEBUG;

remove_file_if_exists($goal);
remove_file_if_exists($timefile);
remove_file_if_exists($outfile);

write_whole_file($outfile, $HEADER);

## Consider just using "mv"/"touch" for the complete step.
if ($STEP eq "complete") {
    ## BOZO this is horrible and only works for CCL/linux and probably the file time thing
    ## is also wrong.
    my $cmd = "(time ((cp $file.pcert1 $file.cert; if [[ $file.lx64fsl -nt $file.pcert1 ]]; then touch $file.lx64fsl; fi) >> $outfile)) 2> $timefile";
    if (system($cmd) != 0) {
	die("Failed to move $file.pcert1 to $file.cert\n");
    }
    $status = 43;
} else {

# Override ACL2 per the image file, as appropriate.
    my $acl2 = read_whole_file_if_exists("$file.image");
    $acl2 = read_whole_file_if_exists("cert.image") if !$acl2;
    $acl2 = $default_acl2 if !$acl2;
    $acl2 = trim($acl2);
    $ENV{"ACL2"} = $acl2;
    print "-- Image to use = $acl2\n" if $DEBUG;
    die("Can't determine which ACL2 to use.") if !$acl2;

# ------------ TEMPORARY LISP FILE FOR ACL2 INSTRUCTIONS ----------------------

    my $rnd = int(rand(2**30));
    my $tmpbase = "workxxx.$goal.$rnd";
# upper-case .LISP so if it doesn't get deleted, we won't try to certify it
    my $lisptmp = "$tmpbase.LISP";
    print "-- Temporary lisp file: $lisptmp\n" if $DEBUG;

    my $instrs = "";

# I think this strange :q/lp dance is needed for lispworks or something?
    $instrs .= "(acl2::value :q)\n";
    $instrs .= "(in-package \"ACL2\")\n";
    $instrs .= "#+acl2-hons (profile-fn 'prove)\n";
    $instrs .= "#+acl2-hons (profile-fn 'certify-book-fn)\n";
    $instrs .= "(acl2::lp)\n\n";
#    $instrs .= "(set-debugger-enable :bt)\n";
    $instrs .= "(set-write-acl2x t state)\n" if ($STEP eq "acl2x");
    $instrs .= "(set-write-acl2x '(t) state)\n" if ($STEP eq "acl2xskip");
    $instrs .= "$INHIBIT\n" if ($INHIBIT);

    $instrs .= "\n";


    my $cert_cmd = "#!ACL2 (er-progn (time\$ (certify-book \"$file\" ? $FLAGS $PCERT $ACL2X))
                                 (value (prog2\$ #+acl2-hons (memsum)
                                                 #-acl2-hons nil
                                                 (exit 43))))";

# Get the certification instructions from foo.acl2 or cert.acl2, if either
# exists, or make a generic certify-book command.
    if (-f "$file.acl2") {
	$instrs .= "; instructions from $file.acl2\n";
	$instrs .= "; (omitting any certify-book line):\n";    
	$instrs .= read_file_except_certify("$file.acl2");
	$instrs .= "\n; certify-book command added automatically:\n";
	$instrs .= "$cert_cmd\n\n";
    }
    elsif (-f "cert.acl2") {
	$instrs .= "; instructions from cert.acl2:\n";
	$instrs .= read_whole_file("cert.acl2");
	$instrs .= "\n; certify-book command added automatically:\n";
	$instrs .= "$cert_cmd\n\n";
    }
    else {
	$instrs .= "; certify-book generated automatically:\n";
	$instrs .= "$cert_cmd\n\n";
    }

    if ($DEBUG) {
	print "-- ACL2 Instructions: $lisptmp --\n";
	print "$instrs\n";
	print "-------------------------------------------------------\n\n";
    }

    write_whole_file($lisptmp, $instrs);



# ------------ TEMPORARY SHELL SCRIPT FOR RUNNING ACL2 ------------------------

# upper-case .SH to agree with upper-case .LISP
    my $shtmp = "$tmpbase.SH";
    my $shinsts = "#!/bin/sh\n\n";

# If we find a set-max-mem line, add 3 gigs of padding for the stacks and to
# allow the lisp to have some room to go over.  Default to 6 gigs.
    my $max_mem = scan_for_set_max_mem("$file.lisp");
    $max_mem = $max_mem ? ($max_mem + 3) : 6;

# If we find a set-max-time line, honor it directly; otherwise default to
# 240 minutes.
    my $max_time = scan_for_set_max_time("$file.lisp") || 240;

    print "-- Resource limits: $max_mem gigabytes, $max_time minutes.\n\n" if $DEBUG;

    $shinsts .= "#PBS -l pmem=${max_mem}gb\n";
    $shinsts .= "#PBS -l walltime=${max_time}:00\n\n";

    $shinsts .= "pwd >> $outfile\n";
# $shinsts .= "echo List directories of prereqs >> $outfile\n";
# $shinsts .= "time ( ls @$prereq_dirs > /dev/null ) 2> $outfile\n";
# foreach my $prereq (@$PREREQS) {
#     $shinsts .= "echo prereq: $prereq >> $outfile\n";
#     $shinsts .= "ls -l $startdir/$prereq >> $outfile 2>&1 \n";
# }
    $shinsts .= "echo >> $outfile\n";
    $shinsts .= "hostname >> $outfile\n";
    $shinsts .= "echo >> $outfile\n";

    $shinsts .= "echo Temp lisp file: >> $outfile\n";
    $shinsts .= "cat $lisptmp >> $outfile\n";
    $shinsts .= "echo >> $outfile\n";

    $shinsts .= "echo TARGET: $TARGET >> $outfile\n";
    $shinsts .= "echo STEP: $STEP >> $outfile\n";
    $shinsts .= "echo Start of output: >> $outfile\n";
    $shinsts .= "echo >> $outfile\n";

    $shinsts .= "echo ACL2_SYSTEM_BOOKS: \${ACL2_SYSTEM_BOOKS} >> $outfile\n";

    if ($TIME_CERT) {
	$shinsts .= "(time (($acl2 < $lisptmp 2>&1) >> $outfile)) 2> $timefile\n";
    }
    else {
	$shinsts .= "($acl2 < $lisptmp 2>&1) >> $outfile\n";
    }

    $shinsts .= "EXITCODE=\$?\n";
    $shinsts .= "ls -l $goal >> $outfile || echo $goal seems to be missing >> $outfile\n";
    $shinsts .= "exit \$EXITCODE\n";


    if ($DEBUG) {
	print "-- Wrapper Script: $shtmp --\n";
	print "$shinsts\n";
	print "-------------------------------------------------------\n\n";
    }

    write_whole_file($shtmp, $shinsts);


# Run it!  ------------------------------------------------

    system("$STARTJOB $shtmp");
    $status = $? >> 8;

    unlink($lisptmp) if !$DEBUG;
    unlink($shtmp) if !$DEBUG;

}

# Success or Failure Detection -------------------------------

# We should know immediately whether we've succeeded or failed,
# because we should exit 43 if we succeeded and not if we don't.
# But we still want to wait for the target file to show up.
my $success = 0;

if ($status == 43) {
    if (-f $goal) {
	$success = 1;
	print "-- Immediate success detected\n" if $DEBUG;
    } else {
# if ($STEP eq "cert" && $status == 43) {
    # The exit code indicates that the file certified successfully, so why
    # doesn't it exist?  Maybe there's NFS lag.  Let's try waiting to see if
    # the file will show up.
	$success = wait_for_nfs($goal, $MAX_NFS_LAG);
	print "-- After waiting for NFS, success is $success\n" if $DEBUG;
    }
}

if ($success) {
    print "Successfully built $printgoal\n";
} else {
    my $taskname = ($STEP eq "acl2x" || $STEP eq "acl2xskip") ? "ACL2X GENERATION" :
	($STEP eq "certify")  ? "CERTIFICATION" :
	($STEP eq "pcertify") ? "PROVISIONAL CERTIFICATION" :
	($STEP eq "pcertifyplus") ? "PROVISIONAL CERTIFICATION+" :
	($STEP eq "convert")  ? "PCERT0->PCERT1 CONVERSION" :
	($STEP eq "complete") ? "PCERT1->CERT COMLETION" : "UNKNOWN";
    print "**$taskname FAILED** for $dir$file.lisp\n\n";
    system("tail -300 $outfile | sed 's/^/   | /'") if $outfile;
    print "\n\n";

    if ($ON_FAILURE_CMD) {
	system($ON_FAILURE_CMD);
    }

    print "**$taskname FAILED** for $dir$file.lisp\n\n";
    exit(1);
}

print "-- Final result appears to be success.\n" if $DEBUG;

# Else, we made it!
system("ls -l $goal");
exit(0);

