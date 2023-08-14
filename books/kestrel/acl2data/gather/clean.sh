#!/bin/sh

# Copyright (C) 2023, ForrestHunt, Inc.
# Written by Matt Kaufmann
# License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

# This script does cleaning that is in addition to what is done by
# books/build/clean.pl.  It isn't necessary if one runs "make
# clean-books" in the top-level ACL2 directory or "make moreclean"
# in the books/ directory.

export this_dir=`cd $(dirname $0) && pwd`

cd $this_dir

rm -rf tests/runs/ Makefile-tmp
