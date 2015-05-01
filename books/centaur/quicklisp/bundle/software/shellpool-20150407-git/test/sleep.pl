#!/usr/bin/env perl

use strict;
use warnings;

$|=1;

if (@ARGV != 1)
{
    print "Usage: sleep.pl SECONDS\n";
    exit(1);
}

my $SECS = $ARGV[0];

for(; $SECS > 0; --$SECS) {
    print "Sleeping for $SECS more seconds.\n";
    sleep(1);
}

print "All done sleeping.\n";
exit(0);
