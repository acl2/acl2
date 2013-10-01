#!/usr/bin/env perl

# wait.pl -- wait for a file to show up on NFS.
# Adapted from the cert.pl build system
#
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

use warnings;
use strict;

if (@ARGV != 1) {
    usage_error();
}

my $filename = $ARGV[0];

if (-f $filename) {
    exit(0);
}

my $MAX_NFS_LAG = $ENV{"MAX_NFS_LAG"} || 100;
wait_for_nfs($filename);

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
    for(my $i = 0; $i < $MAX_NFS_LAG; $i++)
    {
	print "NFS Lag?  Waited $i seconds for $filename...\n";
	sleep(1);

	return 1 if nfs_file_exists($filename);
    }
    return 0;
}

sub usage_error
{
    print <<END;
wait.pl -- Wait for a file to appear over a slow network file system (NFS).

Usage: wait.pl FILENAME

  - Waits up to 100 seconds for FILENAME to appear.
  - Exit with code 0 as soon as it appears, or with code 1 on timeout.
  - The timeout can be configured with the environment variable MAX_NFS_LAG.

END

    exit(1);
}


