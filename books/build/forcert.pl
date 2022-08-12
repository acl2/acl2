#!/usr/bin/env perl

# forcert.pl
# Forward Certification
#
#  Copyright (C) 2022 Kestrel Institute
#
#  License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
#  Author: Eric McCarthy (mccarthy@kestrel.edu)

use strict;
use warnings;
use File::Basename;
use File::Spec;

use FindBin qw($RealBin);
use Getopt::Long qw(:config bundling_override);
# Note, cert.pl uses bundling_override instead.

use lib "$RealBin/lib";
use Certlib;
use Bookscan;
use Cygwin_paths;

use Cwd;
use File::Temp qw/ tempfile /;

################################################################################

# SYNOPSIS
#     forcert.pl [-h|--help] [-j <cores>] [--agg] <targets>...
#
# DESCRIPTION
#     "forcert" stands for "forward certification".
#     Finds community books that depend on <targets>, and runs cert.pl on them.
#     <targets> are books, without file type extension, relative to acl2/books/.
#     When finding books that depend on <targets>,  certain "aggregating books"
#     are ignored unless "--agg" is specified. (*1)
#
#     Current requirements for running this script (*2):
#     1. ACL2 is set to the desired ACL2 executable
#     2. ACL2_ROOT is set to the main ACL2 directory, and
#     3. the current directory is an acl2/books directory
#

# (*1) "Aggregating books" are those with no significant content other than
#      include-book forms and possibly some xdoc.  The problem with including
#      aggregating books in the forward certification is that when they
#      are certified, they can cause many other included books to be certified,
#      including some in which the user may not be interested.
#      If you would like to add some books to the default list, see
#      *standard-aggregating-books* in books/kestrel/utilities/forcert.lisp

# (*2) Note, we can consider using a similar method of finding the acl2
#      executable and the books directory as 'cert.pl' does.  That might be
#      overly complicated for most users, though.


################################################################################
#
# Process command line
#

# defaults:
my $num_cores = 1;
my $include_aggregating_books = 0;  # meaning false

GetOptions ('help|h' => sub { STDERR->print("forcert.pl [-j <cores>] [--agg] <targets>...\n");
                              exit 0; },
            'j=i' => \$num_cores,  # 'j=i' means j takes an integer value
            'agg!' => \$include_aggregating_books);
            # "agg!" means also accept "--noagg", but since that is the default
            # it can be confusing for the help string to mention it as an alternative.

#print "\n num_cores = ", $num_cores, "\n";
#print "\n include_aggregating_books = ", $include_aggregating_books, "\n";

# Now @ARGV is the list of books given.
# Later we check if the books given exist.


################################################################################
#
# Set up environment variables
#

print "Turning off ACL2_CUSTOMIZATION.\n";
$ENV{"ACL2_CUSTOMIZATION"} = "NONE";

####################

if (! defined($ENV{"ACL2"}) ) {
    print STDERR "\nERROR: Environment variable ACL2 must be set to an ACL2 executable.\n";
    exit 1;
}
my $executable = $ENV{"ACL2"};

####################

# It is necessary to define ACL2_ROOT or else we get
# ERROR: in makefile-deps-file-to-forward-alist: (:COULD-NOT-OPEN-CHANNEL "")

if (! defined($ENV{"ACL2_ROOT"}) ) {
    print STDERR "\nERROR: Environment variable ACL2_ROOT must be set to an ACL2 direcgtory.\n";
    exit 1;
}

# Currently not used in script but used by the ACL2 world
# my $acl2_root = $ENV{"ACL2_ROOT"};


####################

# For now we require that the current directory is ".../acl2/books".
# This simplifies reading from files specified by relative pathnames.
# If this becomes limiting we can make it more flexible by
# finding the books directory in some way and adjusting file I/O.

my $dir = getcwd;

# This works as a check that we are in the books dir.
# Consider
if ($dir =~ /acl2\/books\z/) {
    ;
} else {
    print "ERROR: forcert.pl must be called from an acl2/books directory\n";
    exit 1;
}

################################################################################
#
# Normalize file extensions and exit if any .lisp book doesn't exist.
#
# The target books are now in @ARGV.
# They are supposed to be relative to the community books directory, $dir.
# They may be "path-to/xxx.lisp", "path-to/xxx.cert", or "path-to/xxx".
# Here we normalize all of these to "path-to/xxx" and put them in the variable
# $normed_targets, and we require that when we append ".lisp" to each of these
# path exists.
#

my @normed_targets = ();
my $missing_targets = 0;
my $normed_target;
foreach my $target (@ARGV) {
    $normed_target = $target;
    if ( $target =~ /(.*)\.lisp/ ) {
        $normed_target = $1;
    } elsif ( $target =~ /(.*)\.cert/ ) {
        $normed_target = $1;
    }
    if (! -e "${dir}/${normed_target}.lisp")
      { print STDERR "ERROR: the file ${dir}/${normed_target}.lisp does not exist.\n";
        $missing_targets += 1; }
    else {
        push(@normed_targets, $normed_target);
    }
}
if ($missing_targets != 0) { print STDERR "Exiting.\n";
                             exit 1; }



################################################################################
#
# Check the file that contains the lisp form of the Makefile dependencies.
#

if ( -e 'build/Makefile-deps.lsp') {
    print "Using build/Makefile-deps.lsp file that was generated the last time you did a make in the books directory.\n";
    # TODO: look at the date and report how old it is.
    # Maybe also controlled with start switch.
} else {
    print "ERROR: No build/Makefile-deps.lsp\n";
    print "You can generate it with `make --dry-run regression`\n";
    # TODO: maybe just make it generate it, or control behavior with command line option
    exit 1;
}

################################################################################
#
# Certify forcert.lisp and books it depends on.
#

print "\nMaking sure depgraph books are certified.\n";
my $out1 = `cert.pl -j${num_cores} kestrel/utilities/forcert 1> /dev/null 2> /dev/null`;
# Consider doing something more with output.

if ($? != 0) {
    print "\nERROR: something went wrong with `cert.pl -j${num_cores} kestrel/utilities/forcert`\n";
    print   "       If forcert.cert.out was written, it may contain clues.\n";
    exit 1;
}

################################################################################
#
# Temporary file that will store the forward fringe, the fringe of the set
# of books that depend on the targets.
#

my ($tfh, $tfilename) = tempfile();
# print "tfilename = ", $tfilename, "\n";


################################################################################
#
# Construct string to pass to ACL2 via stdin.
# ACL2 will compute the forward fringe and write it to tempfile.
#

# All double quotes in the string need an escaped backslash preceding them.

# There might be a better way to turn off ttag notes, but this idiom is
# used by other scripts that invoke acl2:
my $lisp_turn_off_ttag_notes = '(value :q) (defun print-ttag-note (val active-book-name include-bookp deferred-p state) (declare (ignore val active-book-name include-bookp deferred-p)) state) (lp) ';

# Silently include book forcert
#my $lisp_include_forcert = '(with-output :off :all (include-book \\"kestrel/utilities/forcert\\" :dir :system)) ';
my $lisp_include_forcert = '(include-book \\"kestrel/utilities/forcert\\" :dir :system) ';

# Put the targets into a lisp list of strings
my $lisp_targets = "(\\\"".(join "\\\" \\\"", @normed_targets)."\\\")";
#print "lisp_targets = ", ${lisp_targets}, "\n";

# Aggregating books
my $lisp_exclude_agg;
if ( $include_aggregating_books ) {
    $lisp_exclude_agg = "NIL";
} else {
    $lisp_exclude_agg = "T";
}

# Call function to find the fringe and write to tempfile.
my $lisp_compute_fringe =  "(expand-forcert-targets-into \'${lisp_targets} \\\"${tfilename}\\\" ${lisp_exclude_agg} state)";
#print "lisp_compute_fringe = ", ${lisp_compute_fringe}, "\n";

# Combine the above
my $lisp_stdin_string = $lisp_turn_off_ttag_notes.$lisp_include_forcert.$lisp_compute_fringe;
#print "lisp_stdin_string = ", ${lisp_stdin_string}, "\n";

print "\nCalling ACL2 to compute forward fringe of targets.\n";

# Now call ACL2
my $out2 = `echo "${lisp_stdin_string}" | ${executable}`;
#print "\n out2 = ", $out2, "\n";

# Notes:
# * consider directing the output to another temporary file
# * ACL2 by default returns an exit status of 0 even if there was an error.
#   There could be something we can set that would make ACL2 immediately
#   exit with a nonzero exit status when it gets an error.
#   Because of the default behavior, there is no need to have a final
#   (good-bye 0) form in the stdin string.
# * Not sure what to do with the $out2 string.


################################################################################
#
# Call cert.pl on the fringe books found.
#

# A little bit of observability
print "\n";
print "For your information, this is the temporary filename\n";
print "containing the forward fringe:\n";
print "    ${tfilename}\n";

print "\nCalling cert.pl on fringe.\n";

# Like backtick but lets output flow to callers stdout/stderr.
system("cert.pl -j${num_cores} --targets ${tfilename}");


################################################################################
#
# Close temporary files
#

close $tfh
    or warn "Error closing temp file";
# TODO: remove temporary file when this script stabilizes and we have
#       better observability into what it does.
