#!/bin/bash
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

# Compare the ACL2 library, on EVERY code point, with ICU, and with the
# Python module unicodedata2 for the versions of Unicode that it is for,
# in the image that the Dockerfile of this directory builds.
#
# Usage:
#
#     compare-all.sh WORK_DIR
#
#     WORK_DIR   the directory in which ../run.sh has written the files
#                of the ACL2 library: acl2-VERSION.txt, and
#                acl2-pairs-VERSION.txt, for one or more versions
#
# For each supported version whose file acl2-VERSION.txt is in WORK_DIR,
# this writes icu-VERSION.txt there, and unicodedata2-VERSION.txt if the
# module is for that version, and compares them with the file of the
# library; with the module, it also checks the pairs of
# acl2-pairs-VERSION.txt.
#
# If the directory /ucd/VERSION has the files of the version, laid out as
# for tools/generate-ucd-books.py, they are used as ../run.sh uses UCD_DIR.
#
# The exit status is 0 if a version was compared and nothing differs.

set -euo pipefail

if [ $# -ne 1 ]; then
    sed -n '10,31p' "$0"
    exit 2
fi
work=$1
validation=$(cd "$(dirname "$0")/.." && pwd)
python=/opt/unicodedata2/bin/python
status=0
compared=0

for version in 16.0.0 17.0.0 18.0.0; do
    if [ ! -s "$work/acl2-$version.txt" ]; then
        echo "== Unicode $version: no acl2-$version.txt in $work; skipped"
        continue
    fi
    compared=1
    echo "== Unicode $version: running the ICU oracle"
    python3 "$validation/icu-oracle.py" "$version" "/opt/icu/$version/lib" \
            > "$work/icu-$version.txt"
    files=("$work/icu-$version.txt")
    if "$python" -c 'import sys, unicodedata2
sys.exit(unicodedata2.unidata_version != sys.argv[1])' "$version"; then
        echo "== Unicode $version: running the Python oracle (unicodedata2)"
        ucd=()
        if [ -d "/ucd/$version" ]; then
            ucd=("/ucd/$version")
        fi
        "$python" "$validation/python-oracle.py" "$version" code-points \
                  "${ucd[@]}" > "$work/unicodedata2-$version.txt"
        files+=("$work/unicodedata2-$version.txt")
        "$python" "$validation/python-oracle.py" "$version" pairs \
                  "$work/acl2-pairs-$version.txt" || status=1
    fi
    echo "== Unicode $version: comparing every code point"
    python3 "$validation/compare.py" "$work/acl2-$version.txt" \
            "${files[@]}" || status=1
done

if [ $compared -eq 0 ]; then
    echo "== no file of the ACL2 library in $work: run ../run.sh first"
    exit 2
elif [ $status -eq 0 ]; then
    echo "== no differences"
else
    echo "== DIFFERENCES OR ERRORS (see above)"
fi
exit $status
