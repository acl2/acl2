#!/bin/bash
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

# Build the ICU library (ICU4C) of one release from its source, for
# ../icu-oracle.py.  See the section "Validation" of ../../README.md.
#
# Usage:
#
#     build-icu.sh TAG COMMIT PREFIX
#
#     TAG      a release tag of https://github.com/unicode-org/icu,
#              e.g. release-76-1
#     COMMIT   the commit that the tag must name; the script stops if the
#              tag names another commit
#     PREFIX   the directory to install into; the shared libraries are
#              then in PREFIX/lib
#
# The libraries are built with the data that data-filter.json (in the
# directory of this script) lists, which leaves out the locale data: the
# oracle does not use it, and the build takes a few minutes without it.
# Only the directory icu4c/source of the repository is fetched, into a
# temporary directory, which is removed at the end.
#
# This needs git, make, a C++ compiler and python3.

set -euo pipefail

if [ $# -ne 3 ]; then
    sed -n '10,30p' "$0"
    exit 2
fi
tag=$1
commit=$2
prefix=$3
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "== fetching $tag"
git clone --quiet --depth 1 --branch "$tag" --filter=blob:none --sparse \
    https://github.com/unicode-org/icu "$work/icu"
actual=$(git -C "$work/icu" rev-parse HEAD)
if [ "$actual" != "$commit" ]; then
    echo "build-icu.sh: error: $tag is commit $actual, not $commit"
    exit 1
fi
git -C "$work/icu" sparse-checkout set icu4c/source

echo "== building (this takes several minutes)"
mkdir "$work/build"
cd "$work/build"
ICU_DATA_FILTER_FILE="$here/data-filter.json" \
    "$work/icu/icu4c/source/configure" --quiet --prefix="$prefix" \
    --disable-tests --disable-samples --disable-extras --disable-icuio \
    --disable-layoutex > configure.log
make --quiet -j "$(nproc)" > make.log 2>&1 \
    || { tail -30 make.log; exit 1; }
make --quiet install > install.log 2>&1 \
    || { tail -30 install.log; exit 1; }
echo "== installed $tag in $prefix"
