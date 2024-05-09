#!/bin/bash

# Copyright (C) 2023, ForrestHunt, Inc.
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# Execute this in the books/ directory.

find . -name '*_acl2data.out' -print -exec grep -Fh ';total_count_hints' {} \; | fgrep ';total_count_hints' > total_count_hints.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';total_count_hypotheses' {} \; | fgrep ';total_count_hypotheses' > total_count_hypotheses.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';total_count_book_runes' {} \; | fgrep ';total_count_book_runes' > total_count_book_runes.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';total_count_single_rune' {} \; | fgrep ';total_count_single_rune' > total_count_single_rune.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';failure_count_hints' {} \; | fgrep ';failure_count_hints' > failure_count_hints.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';failure_count_hypotheses' {} \; | fgrep ';failure_count_hypotheses' > failure_count_hypotheses.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';failure_count_book_runes' {} \; | fgrep ';failure_count_book_runes' > failure_count_book_runes.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';failure_count_single_rune' {} \; | fgrep ';failure_count_single_rune' > failure_count_single_rune.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';failure_count' {} \; | fgrep ';failure_count' > failure_count.txt

find . -name '*_acl2data.out' -print -exec grep -Fh ';total_count' {} \; | fgrep ';total_count' > total_count.txt
