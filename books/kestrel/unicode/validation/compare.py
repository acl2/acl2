#!/usr/bin/env python3
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Compare, for EVERY code point, a file written by the ACL2 function
DUMP-PROPERTIES of dump.lisp with files written by the oracles
(rust-oracle and python-oracle.py), which are independent implementations
of the same version of Unicode.

Usage:

    compare.py ACL2-FILE ORACLE-FILE...

Each oracle column is named `property@source`.  It is compared with the
ACL2 column `property`, for every code point, except that:

  * rustc_id_start is compared with "XID_Start, or the underscore",
    rustc_id_continue with XID_Continue, and rustc_whitespace with
    Pattern_White_Space: that is how rustc's lexer defines them;

  * a field `!` means that the oracle cannot say (the Rust oracle writes it
    for the surrogates, which are not Rust chars); such fields are counted
    but not compared;

  * for the precomposed Hangul syllables, the dm column of the Python
    oracle is compared with the ACL2 NFD column: the Decomposition_Mapping
    of an LVT syllable is the pair of an LV syllable and a T jamo, but
    Python's unicodedata.decomposition returns its full decomposition.

This script also checks the ACL2 file against itself: a code point has
Full_Composition_Exclusion exactly when its NFC form is not itself, and
the columns that the library proves to be the same in all versions have
the values that those theorems say.

The exit status is 1 if anything differs.
"""

import sys

NUM_CP = 0x110000


def die(message):
    sys.exit("compare.py: error: " + message)


def read(path):
    """Return (column names, list of rows of fields indexed by code point)."""
    with open(path) as f:
        header = f.readline().rstrip("\n")
        if not header.startswith("#cp;"):
            die("%s: no header" % path)
        columns = header[1:].split(";")
        rows = []
        for cp, line in enumerate(f):
            fields = line.rstrip("\n").split(";")
            if len(fields) != len(columns) or fields[0] != str(cp):
                die("%s: bad line for code point %d" % (path, cp))
            rows.append(fields)
    if len(rows) != NUM_CP:
        die("%s: %d code points, not %d" % (path, len(rows), NUM_CP))
    return columns, rows


def main():
    if len(sys.argv) < 2:
        die("usage: compare.py ACL2-FILE ORACLE-FILE...")
    acl2_columns, acl2 = read(sys.argv[1])
    index = {name: i for i, name in enumerate(acl2_columns)}
    for name in ["xids", "xidc", "pws", "bidic", "bidif", "ccc", "fce",
                 "dm", "nfd", "nfc", "nfkd", "nfkc", "gc", "di", "vs", "jc",
                 "nchar", "dep", "pcm", "psyn"]:
        if name not in index:
            die("%s: no column %s" % (sys.argv[1], name))

    def expected(prop, source):
        """The ACL2 values to compare an oracle column for PROP with."""
        if prop == "rustc_id_start":
            i = index["xids"]
            return ["1" if (row[i] == "1" or cp == 0x5F) else "0"
                    for cp, row in enumerate(acl2)]
        if prop == "rustc_id_continue":
            prop = "xidc"
        if prop == "rustc_whitespace":
            prop = "pws"
        if prop not in index:
            die("no ACL2 column for %s" % prop)
        i = index[prop]
        if prop == "dm" and source == "python":
            nfd = index["nfd"]
            return ["c:" + row[nfd] if 0xAC00 <= cp <= 0xD7A3 else row[i]
                    for cp, row in enumerate(acl2)]
        return [row[i] for row in acl2]

    failed = False

    def report(what, compared, skipped, differences):
        nonlocal failed
        status = "ok" if not differences else "DIFFERENT"
        print("%-34s %s: %d code points compared, %d skipped, %d different"
              % (what, status, compared, skipped, len(differences)))
        for cp, ours, theirs in differences[:10]:
            print("    U+%04X: ACL2 %r, other %r" % (cp, ours, theirs))
        if differences:
            failed = True

    # The ACL2 file against itself.
    nfc, fce = index["nfc"], index["fce"]
    report("fce = (nfc is not identity)", NUM_CP, 0,
           [(cp, row[fce], row[nfc]) for cp, row in enumerate(acl2)
            if (row[fce] == "1") != (row[nfc] != str(cp))])
    pws = {*range(0x9, 0xE), 0x20, 0x85, 0x200E, 0x200F, 0x2028, 0x2029}
    report("pws = the 11 code points", NUM_CP, 0,
           [(cp, row[index["pws"]], "") for cp, row in enumerate(acl2)
            if (row[index["pws"]] == "1") != (cp in pws)])
    bidic = {0x61C, 0x200E, 0x200F, *range(0x202A, 0x202F),
             *range(0x2066, 0x206A)}
    report("bidic = the 12 code points", NUM_CP, 0,
           [(cp, row[index["bidic"]], "") for cp, row in enumerate(acl2)
            if (row[index["bidic"]] == "1") != (cp in bidic)])

    # The oracles.
    for path in sys.argv[2:]:
        columns, rows = read(path)
        for i, column in enumerate(columns):
            if i == 0:
                continue
            prop, _, source = column.partition("@")
            ours = expected(prop, source)
            compared = skipped = 0
            differences = []
            for cp, row in enumerate(rows):
                if row[i] == "!":
                    skipped += 1
                    continue
                compared += 1
                if row[i] != ours[cp]:
                    differences.append((cp, ours[cp], row[i]))
            report(column, compared, skipped, differences)

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
