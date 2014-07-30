#!/usr/bin/env perl

use strict;
use warnings;

print "Testing getopt demo2 program:\n";

sub test
{
    my $args = shift;
    my $expected_out = shift;
    my $expected_code = shift;

    print "Testing $args. ";
    my $out = `./demo2 $args`;
    my $code = $? >> 8;

    chomp($out);
    if ($out ne $expected_out) {
        print "Fail: expected $expected_out but got $out\n";
	exit(1);
    }

    if ($code != $expected_code) {
	print "Fail: expected exit status $expected_code but got $code\n";
	exit(1);
    }

    print "OK.\n";
}

my $HELPMSG = <<END;
demo2: how to write a command line program in ACL2
    -h,--help             Print a help message and exit with status 0.
    -v,--version          Print out a version message and exit with
                          status 0.
    -f,--fail             Print nothing and exit with status 1.
END

my $VERSION = "demo2: version 1.234";

# Some tests of blank arguments
test("", "colorless green ideas sleep furiously", 0);
test(" ", "colorless green ideas sleep furiously", 0);
test("  ", "colorless green ideas sleep furiously", 0);

# Help is the highest priority.
test("-h", $HELPMSG, 0);
test("--help", $HELPMSG, 0);
test("-v -h", $HELPMSG, 0);
test("-h -v", $HELPMSG, 0);
test("--help -v", $HELPMSG, 0);
test("-v --help", $HELPMSG, 0);
test("--help --version", $HELPMSG, 0);
test("--version --help", $HELPMSG, 0);
test("-f -h", $HELPMSG, 0);
test("-h -f", $HELPMSG, 0);
test("--help -f", $HELPMSG, 0);
test("-f --help", $HELPMSG, 0);
test("--help --fail", $HELPMSG, 0);
test("--fail --help", $HELPMSG, 0);

# Version is the next highest
test("-v", $VERSION, 0);
test("--version", $VERSION, 0);
test("-v -f", $VERSION, 0);
test("-f -v", $VERSION, 0);
test("--fail -v", $VERSION, 0);
test("-v --fail", $VERSION, 0);
test("--fail --version", $VERSION, 0);
test("--version --fail", $VERSION, 0);

# Fail has the least priority
test("-f", "", 1);
test("--fail", "", 1);

# Some tests of invalid args
test("-o", "Unrecognized option -o.", 1);
test("--oops", "Unrecognized option --oops", 1);  # BOZO should print a period I guess.
test("-v=5", "Option --version can't take an argument", 1);
test("-v=", "Option --version can't take an argument", 1);

# Some tests of tricky/hard arguments for certain Lisps
test("-e", "Unrecognized option -e.", 1);
test("-l", "Unrecognized option -l.", 1);
test("-Z", "Unrecognized option -Z.", 1);
test("-I", "Unrecognized option -I.", 1);
test("--eval", "Unrecognized option --eval", 1);
test("--load", "Unrecognized option --load", 1);

