#!/usr/bin/env python3
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Write what Python says about every code point, in the format of dump.lisp,
for comparison with the ACL2 library.

Usage:

    python-oracle.py VERSION code-points [UCD-DIR] > FILE
    python-oracle.py VERSION pairs PAIRS-FILE

VERSION, e.g. 16.0.0, must be the version of Unicode of the Python
interpreter's unicodedata module (unicodedata.unidata_version); the script
stops if it is not.  Python 3.14 has Unicode 16.0.0 and Python 3.15 has
Unicode 17.0.0.

The first form writes a header line and one line for each code point.
Each column is named `property@source`, where the source is

    python   the interpreter itself: the unicodedata module, and
             str.isidentifier for XID_Start and XID_Continue.
             unicodedata.bidirectional gives the Bidi_Class of the
             assigned characters only; for the others the field is `!`,
             which means "cannot say".
    regex    the third-party `regex` module, which has its own Unicode
             tables; its columns are written only if it is installed and
             its tables are for VERSION (it does not say which version
             they are for, so this is determined by asking it about two
             code points: see XID_START_PROBES)

    python-and-files
             the internal skeleton of UTS #39, computed here from
             unicodedata.normalize and from two files of VERSION that
             are read from UCD-DIR: security/confusables.txt for the
             prototypes, and DerivedCoreProperties.txt for
             Default_Ignorable_Code_Point.  These columns are written
             only if UCD-DIR is given; it is laid out as for
             tools/generate-ucd-books.py.

Python strings may contain surrogates, so there is a line for every code
point.

The second form reads a file written by DUMP-PAIRS of dump.lisp, with lines
`first second composite nfc...`, and checks the NFC form of each pair
against unicodedata.normalize.  It exits with status 1 if any differs.
"""

import sys
import unicodedata

BIDI_FORMATTING = {"LRE", "RLE", "LRO", "RLO", "PDF", "LRI", "RLI", "FSI",
                   "PDI"}


def die(message):
    sys.exit("python-oracle.py: error: " + message)


# The first code point that got XID_Start in each version of Unicode.
# The regex module does not say which version of Unicode its tables are
# for, and it does not have the Age property; so we ask it about these.
XID_START_PROBES = {16: 0x1C89, 17: 0x088F, 18: 0x0558}


def regex_sets(version):
    """Property sets from the regex module, or None if it is not installed
    or cannot be shown to be for this version of Unicode."""
    try:
        import regex
    except ImportError:
        print("python-oracle.py: the regex module is not installed",
              file=sys.stderr)
        return None
    xid_start = regex.compile(r"\p{XID_Start}")
    major = int(version.split(".")[0])
    this, following = (XID_START_PROBES.get(major),
                       XID_START_PROBES.get(major + 1))
    if (version != "%d.0.0" % major or this is None or following is None
            or not xid_start.match(chr(this))
            or xid_start.match(chr(following))):
        print("python-oracle.py: cannot tell that the regex module %s"
              " is for Unicode %s; not using it"
              % (regex.__version__, version), file=sys.stderr)
        return None
    print("python-oracle.py: the regex module %s is for Unicode %s"
          " (it has XID_Start for U+%04X and not for U+%04X)"
          % (regex.__version__, version, this, following), file=sys.stderr)
    sets = {}
    for column, prop in [("xids", "XID_Start"), ("xidc", "XID_Continue"),
                         ("pws", "Pattern_White_Space"),
                         ("bidic", "Bidi_Control")]:
        pattern = regex.compile(r"\p{%s}" % prop)
        sets[column] = [bool(pattern.match(chr(cp)))
                        for cp in range(0x110000)]
    return sets


def data_lines(path, version):
    """The data lines of a file of the Unicode Character Database or of
    UTS #39, as lists of fields, after a check of the version."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    head = "\n".join(lines[:12])
    if version not in head and version[:-2] not in head:
        die("%s is not for Unicode %s" % (path, version))
    for line in lines:
        line = line.split("#", 1)[0].strip()
        if line:
            yield [field.strip() for field in line.split(";")]


def skeleton_function(version, ucd_dir):
    """The internal skeleton of UTS #39, Section 4, as a function on
    strings, from the files of VERSION in UCD-DIR."""
    prototype = {}
    for fields in data_lines(ucd_dir + "/security/confusables.txt", version):
        prototype[chr(int(fields[0], 16))] = "".join(
            chr(int(cp, 16)) for cp in fields[1].split())
    ignorable = set()
    for fields in data_lines(ucd_dir + "/DerivedCoreProperties.txt",
                             version):
        if fields[1] == "Default_Ignorable_Code_Point":
            ends = [int(cp, 16) for cp in fields[0].split("..")]
            ignorable.update(chr(cp) for cp in range(ends[0], ends[-1] + 1))

    def skeleton(s):
        s = unicodedata.normalize("NFD", s)
        s = "".join(prototype.get(c, c) for c in s if c not in ignorable)
        return unicodedata.normalize("NFD", s)

    return skeleton


def seq(s):
    return " ".join(str(ord(c)) for c in s)


def code_points(version, ucd_dir):
    sets = regex_sets(version)
    skeleton = skeleton_function(version, ucd_dir) if ucd_dir else None
    columns = ["xids@python", "xidc@python", "bidif@python", "ccc@python",
               "dm@python", "nfd@python", "nfc@python", "nfkd@python",
               "nfkc@python", "gc@python", "bc@python", "dd@python"]
    if sets:
        columns += ["xids@regex", "xidc@regex", "pws@regex", "bidic@regex"]
    if skeleton:
        columns += ["skel@python-and-files", "skelm@python-and-files"]
    out = sys.stdout
    out.write("#cp;" + ";".join(columns) + "\n")
    for cp in range(0x110000):
        c = chr(cp)
        # str.isidentifier: the first character must have XID_Start or be
        # an underscore, and the others must have XID_Continue.
        xids = c.isidentifier() and c != "_"
        xidc = ("a" + c).isidentifier()
        bidi = unicodedata.bidirectional(c)
        mapping = unicodedata.decomposition(c)
        if not mapping:
            dm = "-"
        else:
            parts = mapping.split(" ")
            kind = "c:"
            if parts[0].startswith("<"):
                kind, parts = "k:", parts[1:]
            dm = kind + " ".join(str(int(p, 16)) for p in parts)
        fields = [str(cp),
                  "1" if xids else "0",
                  "1" if xidc else "0",
                  bidi if bidi in BIDI_FORMATTING else "-",
                  str(unicodedata.combining(c)),
                  dm,
                  seq(unicodedata.normalize("NFD", c)),
                  seq(unicodedata.normalize("NFC", c)),
                  seq(unicodedata.normalize("NFKD", c)),
                  seq(unicodedata.normalize("NFKC", c)),
                  unicodedata.category(c),
                  bidi if bidi else "!",
                  str(unicodedata.decimal(c, "-"))]
        if sets:
            fields += ["1" if sets[k][cp] else "0"
                       for k in ("xids", "xidc", "pws", "bidic")]
        if skeleton:
            fields += [seq(skeleton(c)),
                       seq(skeleton("a" + c + "\u0301\u0327"))]
        out.write(";".join(fields) + "\n")


def pairs(path):
    lines = differences = 0
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("#"):
                continue
            lines += 1
            fields = line.split(" ")
            first, second = int(fields[0]), int(fields[1])
            nfc = seq(unicodedata.normalize("NFC", chr(first) + chr(second)))
            if nfc != " ".join(fields[3:]):
                differences += 1
                if differences <= 20:
                    print("DIFFERENT: %s (here: %s)" % (line, nfc))
    print("pairs@python: %d pairs, %d different" % (lines, differences))
    return differences == 0


def main():
    if len(sys.argv) < 3:
        die("usage: python-oracle.py VERSION code-points [UCD-DIR]"
            " | python-oracle.py VERSION pairs FILE")
    version = sys.argv[1]
    if unicodedata.unidata_version != version:
        die("this Python (%s) has Unicode %s, not %s"
            % (sys.version.split()[0], unicodedata.unidata_version, version))
    print("python-oracle.py: Python %s has Unicode %s"
          % (sys.version.split()[0], unicodedata.unidata_version),
          file=sys.stderr)
    if sys.argv[2] == "code-points" and len(sys.argv) in (3, 4):
        code_points(version, sys.argv[3] if len(sys.argv) == 4 else None)
    elif sys.argv[2] == "pairs" and len(sys.argv) == 4:
        if not pairs(sys.argv[3]):
            sys.exit(1)
    else:
        die("bad arguments")


if __name__ == "__main__":
    main()
