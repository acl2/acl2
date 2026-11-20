#!/bin/bash
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

# Compare the ACL2 library, on EVERY code point, with independent
# implementations of one version of Unicode: the Rust crates that rustc
# uses, and Python.  See the section "Validation" of ../README.md.
#
# Usage:
#
#     run.sh VERSION WORK_DIR [PYTHON...]
#
#     VERSION    a Unicode version that the library supports, e.g. 16.0.0
#     WORK_DIR   a directory for the files that are written (several
#                hundred megabytes); it is created if it does not exist
#     PYTHON...  the command that runs a Python interpreter whose
#                unicodedata module is for VERSION (Python 3.14 for 16.0.0,
#                Python 3.15 for 17.0.0), preferably with the `regex`
#                module of the same version of Unicode installed;
#                if it is omitted, the comparison with Python is skipped
#
# If the environment variable UCD_DIR is set, it is the directory with the
# files of VERSION, laid out as for tools/generate-ucd-books.py; then the
# Python oracle also computes the skeletons of UTS #39, from the files
# security/confusables.txt and DerivedCoreProperties.txt of that directory.
#
# This needs acl2 and cargo on the PATH, and the book dump in this
# directory certified (cert.pl dump).  cargo downloads the crates.
#
# The exit status is 0 if nothing differs.

set -euo pipefail

if [ $# -lt 2 ]; then
    sed -n '10,36p' "$0"
    exit 2
fi
version=$1
work=$2
shift 2
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$work"
work=$(cd "$work" && pwd)

echo "== ACL2: writing $work/acl2-$version.txt, acl2-pairs-$version.txt"
echo "   and acl2-stream-safe-$version.txt"
acl2 > "$work/acl2-$version.log" 2>&1 <<EOF2
(include-book "$here/dump")
(in-package "UNICODE")
(dump-properties (version-v$version) "$work/acl2-$version.txt" state)
(dump-pairs (version-v$version) "$work/acl2-pairs-$version.txt" state)
(dump-stream-safe (version-v$version) "$work/acl2-stream-safe-$version.txt"
                  state)
EOF2
files=("$work/acl2-$version.txt")
status=0

echo "== Rust: building and running the oracle"
cargo build --release --quiet \
      --manifest-path "$here/rust-oracle/v$version/Cargo.toml"
oracle="$here/rust-oracle/v$version/target/release/oracle"
"$oracle" "$version" code-points > "$work/rust-$version.txt"
files+=("$work/rust-$version.txt")
"$oracle" "$version" pairs "$work/acl2-pairs-$version.txt" || status=1
"$oracle" "$version" stream-safe "$work/acl2-stream-safe-$version.txt" \
    || status=1

if [ $# -gt 0 ]; then
    echo "== Python: running the oracle"
    "$@" "$here/python-oracle.py" "$version" code-points \
         ${UCD_DIR:+"$UCD_DIR"} > "$work/python-$version.txt"
    files+=("$work/python-$version.txt")
    "$@" "$here/python-oracle.py" "$version" pairs \
         "$work/acl2-pairs-$version.txt" || status=1
fi

echo "== Comparing every code point"
python3 "$here/compare.py" "${files[@]}" || status=1

if [ $status -eq 0 ]; then
    echo "== Unicode $version: no differences"
else
    echo "== Unicode $version: DIFFERENCES FOUND"
fi
exit $status
