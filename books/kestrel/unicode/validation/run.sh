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
# security/confusables.txt and DerivedCoreProperties.txt of that directory,
# checks the aliases of NameAliases.txt, and reads the labels of the code
# points from extracted/DerivedGeneralCategory.txt.  With UCD_DIR and
# without PYTHON, the labels alone are read from that file, with python3.
#
# This needs acl2 and cargo on the PATH, and the book dump in this
# directory certified (cert.pl dump).  cargo downloads the crates.
#
# The files that ACL2 writes for VERSION are removed from WORK_DIR first,
# so that what is compared is what this run writes.  The exit status is 0
# if ACL2 writes its three files to the end and nothing differs.

set -euo pipefail

if [ $# -lt 2 ]; then
    sed -n '10,40p' "$0"
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
dumps=("$work/acl2-$version.txt" "$work/acl2-pairs-$version.txt"
       "$work/acl2-stream-safe-$version.txt")
rm -f "${dumps[@]}"
# ACL2 exits with status 0 also when a form fails, for example when the
# book dump is not certified; so the files are checked.  The programs
# that read them check that they are complete.  No customization file is
# loaded: one could start ACL2 in another package.
ACL2_CUSTOMIZATION=NONE acl2 > "$work/acl2-$version.log" 2>&1 <<EOF2
(include-book "$here/dump")
(in-package "UNICODE")
(dump-properties (version-v$version) "$work/acl2-$version.txt" state)
(dump-pairs (version-v$version) "$work/acl2-pairs-$version.txt" state)
(dump-stream-safe (version-v$version) "$work/acl2-stream-safe-$version.txt"
                  state)
EOF2
for file in "${dumps[@]}"; do
    if [ ! -s "$file" ]; then
        echo "== ACL2 did not write $file"
        echo "   see $work/acl2-$version.log"
        exit 1
    fi
done
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
if grep -q '^    "have-unicode-bidi",' \
        "$here/rust-oracle/v$version/Cargo.toml"; then
    echo "== Rust: the display order of text (this takes a minute)"
    "$oracle" "$version" display-order || status=1
fi

if [ $# -gt 0 ]; then
    echo "== Python: running the oracle"
    "$@" "$here/python-oracle.py" "$version" code-points \
         ${UCD_DIR:+"$UCD_DIR"} > "$work/python-$version.txt"
    files+=("$work/python-$version.txt")
    "$@" "$here/python-oracle.py" "$version" pairs \
         "$work/acl2-pairs-$version.txt" || status=1
elif [ -n "${UCD_DIR:-}" ]; then
    echo "== Reading the labels from the files of the version"
    python3 "$here/python-oracle.py" "$version" files "$UCD_DIR" \
            > "$work/files-$version.txt"
    files+=("$work/files-$version.txt")
fi

echo "== Comparing every code point"
python3 "$here/compare.py" "${files[@]}" || status=1

if [ $status -eq 0 ]; then
    echo "== Unicode $version: no differences"
else
    echo "== Unicode $version: DIFFERENCES OR ERRORS (see above)"
fi
exit $status
