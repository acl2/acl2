#!/usr/bin/env perl

use strict;
use warnings;

$|=1;

if (@ARGV != 1)
{
    print "Usage: badsleep.pl SECONDS\n";
    exit(1);
}

sub ignoresig {
    my $signame = shift;
    print "Ignoring SIG$signame\n";
}

$SIG{'INT'} = 'ignoresig';
$SIG{'HUP'} = 'ignoresig';
$SIG{'TERM'} = 'ignoresig';

my $SECS = $ARGV[0];

for(; $SECS > 0; --$SECS) {
    print "Sleeping for $SECS more seconds.\n";
    sleep(1);
}

print "All done sleeping.\n";
exit(0);
