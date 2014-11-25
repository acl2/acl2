#!/usr/bin/env perl
#
# SATLINK - Link from ACL2 to SAT Solvers
# Copyright (C) 2013-2014 Centaur Technology
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
# Original authors: Jared Davis <jared@centtech.com>
#                   Sol Swords <sswords@centtech.com>

use strict;
use warnings;
use Cwd;
use Getopt::Long;
use File::Copy;
use Digest::MD5 qw(md5_base64);

sub read_whole_file
{
    my $filename = shift;
    open (my $fh, "<", $filename) or die("Can't open $filename: $!\n");
    local $/ = undef;
    my $ret = <$fh>;
    close($fh);
    return $ret;
}

sub write_whole_file
{
    my $filename = shift;
    my $contents = shift;
    open(my $file, ">", $filename) or die("can't open $filename: $!");
    print $file $contents;
    close($file);
}

my $filename;
my $comment = "";
my $status;
GetOptions("filename=s" => \$filename,
           "comment=s" => \$comment,
	   "status=s" => \$status)
    or die("Error in command line arguments\n");

die "--filename is required" if !$filename;
die "--status is required" if !$status;
die "not a regular file: $filename" if ! -f $filename;
die "invalid status: $status" if ($status ne "sat" && $status ne "unsat");

print "; add-benchmark.pl: adding $filename ($status)\n";

# Make sure dest dir exists
my $dir = getcwd;
if (! -d "$dir/satlink-benchmarks") {
    mkdir("$dir/satlink-benchmarks") or die("Unable to create $dir/satlink-benchmarks")
}

# Create the destination filename using an md5sum, since this will
# (1) map repeated occurrences of the same problem to the same output filename
# (2) avoid (practically speaking) any problems being overwritten accidentally
#
# Better to use md5_base64 since it compresses the checksum from 32 characters
# (for md5_hex) to 22 characters.  BUT, it may use the characters + and /.  The
# / character is no good for filenames, so replace it with _.
my $contents = read_whole_file($filename);
my $md5 = md5_base64($contents);
$md5 =~ s/\//_/g;

my $outfile = "$md5.$status";

print "; add-benchmark.pl: saving as $outfile\n";

my $out = <<END;
c ACL2 Satlink Benchmark
c $comment
$contents
END

write_whole_file("$dir/satlink-benchmarks/$outfile", $out);

print "; add-benchmark.pl: wrote $outfile\n";
