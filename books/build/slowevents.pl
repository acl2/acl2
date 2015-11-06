#!/usr/bin/env perl

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
# Original author: Jared Davis <jared@centtech.com>

# slowevents.pl - what events in a book are slow?

use warnings;
use strict;
use FindBin qw($RealBin);
use Getopt::Long qw(:config bundling);

(do "$RealBin/certlib.pl") or die("Error loading $RealBin/certlib.pl:\n $!");

my $HELP_MESSAGE = '

 slowevents.pl [OPTIONS] book1.lisp [book2.lisp ...]

 This program shows which events in your book took the most time.  It is just a
 tool for summarizing the .cert.out file.  The books to summarize must be
 certified first for this to work.

 Typical Example:

     slowevents.pl `find . -name "*.lisp"` --limit 10

 Usage:

 You can give file names as in cert.pl, e.g., you can write foo.lisp, or
 foo.cert, or just foo.

 Options:

   -h               Print this help message and exit.
   --help

   -l SECS          Set the minimum time threshold for events to be
   --limit SECS     reported (default: 1.0)

 Notes:

 See also critpath.pl and memsum.pl.

';

my %OPTIONS = (
  'help'    => '',
  'limit'   => '1.0',
);

my $options_okp = GetOptions('h|help'    => \$OPTIONS{'help'},
                             'l|limit=s' => \$OPTIONS{'limit'});

if (!$options_okp || $OPTIONS{"help"})
{
    print $HELP_MESSAGE;
    exit ($OPTIONS{"help"} ? 0 : 1);
}

my @books = @ARGV;

sub elide_form_basic
{
    my $form = shift;
    for(my $i = 0; $i < 5; ++$i)
    {
	$form =~ s/\(LOCAL(.*)\)/$1/;
	$form =~ s/\(DEF.* (.*)\)/$1/;
	$form =~ s/\(TABLE (.*)\)//;
	$form =~ s/\(MAKE-EVENT (.*)\)//;
	$form =~ s/\(MUTUAL-RECURSION (.*)\)//;
	$form =~ s/\(IN-THEORY .*\)//;
	$form =~ s/\$INLINE//;
	$form =~ s/^T$//;
	$form =~ s/^\)$//;
	$form =~ s/\(PROGN(.*)/$1/;
	$form =~ s/\(DEF(.*) (.*)/$2/;
	$form =~ s/\(WITH-OUTPUT :[^ ]* (.*)/$1/;
	$form =~ s/^[ ]*//;
	$form =~ s/[ ]*$//;
    }
    return $form;
}

sub elide_form_aggressive
{
    my $form = shift;
    for(my $i = 0; $i < 5; ++$i) {
	$form = elide_form_basic($form);
	$form =~ s/\(?PROGN(.*)\)/$1/;
	$form =~ s/\(?MUTUAL-RECURSION//;
	$form =~ s/\(?VERIFY-GUARDS//;
	$form =~ s/\(?ENCAPSULATE NIL (.*)\)/$1/;
	$form =~ s/\(?ENCAPSULATE NIL\)?$//;
	$form =~ s/^\(//;
	$form =~ s/\)$//;
	$form =~ s/^[ ]*//;
	$form =~ s/[ ]*$//;
    }
    return $form;
}

sub pre_filter_forms
{
    my $forms = shift;
    my @ret = ();

    foreach my $form (@$forms)
    {
	$form =~ s/^[ ]*//;       # trim everything
	$form =~ s/[ ]*$//;
	$form =~ s/\.\.\.//g;     # eliminate any inner ... elisions
	$form =~ s/\([ ]*/(/g;    # eliminate whitespace after (
	$form =~ s/[ ]*\)/)/g;    # eliminate whitespace before )

	# Throw out certify-book forms since they're useless
	$form =~ s/\(CERTIFY-BOOK.*\)//g;
	if (!($form =~ /^ *$/)) {
	    push(@ret, $form);
	}
    }
    return \@ret;
}

sub elide_forms
{
    my $forms = shift;

    if (@$forms == 0) {
	die "Expected at least one form.";
    }

    if (@$forms == 1)
    {
	# Don't bother eliding it.
	return @$forms[0];
    }

    # Elide the first and last forms more lightly, and the inner forms more aggressively.
    my @ans = ();
    foreach my $form (@$forms)
    {
	$form = elide_form_basic($form);
	if (!($form =~ /^ *$/)) {
	    push(@ans, "$form");
	}
    }
    my $ret = "";
    my $middle_count = 0;
    my $cutoff = 4;
    $ret .= $ans[0];
    for(my $i = 1; $i < @ans-1; ++$i)
    {
	my $item = elide_form_aggressive($ans[$i]);
	if (!($item =~ /^[ ]*$/)) {
	    $middle_count++;
	    if ($middle_count < $cutoff) {
		$ret .= " $item";
	    }
	}
    }
    if ($middle_count > $cutoff) {
	$ret .= " [..." .  ($middle_count - $cutoff) . " more...]";
    }

    $ret .= " " . $ans[@ans-1];
    return $ret;
}

sub analyze
{
    my $bookname = shift;
    my $ans = shift;
    my $outfile = to_cert_name($bookname, "cert.out");

    my $fd;
    if (!open ($fd, "<", $outfile)) {
	print "Could not open $outfile\n";
	return;
    }
    my $forms = [];
    while (my $line = <$fd>)
    {
	if ($line =~ /^Form: (.*)$/)
	{
	    my $form = $1;
	    push(@$forms, $form);
	}
	elsif ($line =~ /^Time:[ ]*([0-9]+.[0-9]+) seconds/)
	{
	    my $time = $1;
	    my $entry = {};
	    $entry->{'book'} = $bookname;
	    $entry->{'forms'} = $forms;
	    $entry->{'time'} = $time;
	    push(@$ans, $entry);
	    $forms = [];
	}
    }

    close $fd;
}

my $times = [];
foreach my $book (@books) {
    analyze($book, $times);
}

my @stimes = sort { $a->{'time'} <=> $b->{'time'} } @$times;

foreach my $entry (@stimes)
{
    my $bookname = $entry->{'book'};
    my $time = $entry->{'time'};
    my $forms = $entry->{'forms'};

    next unless ($time >= $OPTIONS{'limit'});

    $forms = pre_filter_forms($forms);
    next if (@$forms == 0);

    $forms = elide_forms($forms);
    printf("%10ss %s\n%10s  %s\n\n", $time, $bookname, "", $forms);
}
