#!/usr/bin/env python3
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Generate the data books of [books]/kestrel/unicode from the UCD.

This script reads the files of ONE explicitly named version of the
Unicode Character Database (UCD) and writes the ACL2 books in

    ../data/v<VERSION>/

Each generated book corresponds to one UCD file and records, in its
header, the URL of that file and the SHA-256 of the bytes that were read.

Usage:

    generate-ucd-books.py VERSION UCD_DIR [--fetch] [--base-url URL]
                                          [--pin] [--check]

    VERSION    A Unicode version, written out in full, e.g. 16.0.0.
               There is no default and nothing means "latest".
    UCD_DIR    A directory laid out like
               https://www.unicode.org/Public/<VERSION>/ucd/
               (so the extracted/ files are in UCD_DIR/extracted/).
    --fetch    Download into UCD_DIR the needed files that are not
               already there (from --base-url, which defaults to
               https://www.unicode.org/Public/<VERSION>/ucd/).
    --pin      Record the SHA-256 of each file read for this version in
               ucd-sources.json (next to this script).  This is how a new
               Unicode version is added.  Without --pin, the version must
               already be in ucd-sources.json and every file read must
               have the SHA-256 recorded there.
    --check    Do not write anything; exit with status 1 if any generated
               book differs from the one in the tree.

The UCD files are not checked into the repository.

What is read, and how:

  * Derived properties are read from the UCD's derived files
    (DerivedCoreProperties.txt, DerivedNormalizationProps.txt, and the
    files in extracted/); they are not recomputed here.  Where the same
    information can also be computed from UnicodeData.txt and
    CompositionExclusions.txt, this script computes it too, but only to
    cross-check the files against each other; it stops on any difference.

  * Code points that a file does not list take the default value given
    by the file's "# @missing:" lines (UAX #44, Section 4.2.10); a later
    @missing line overrides an earlier one for the range it names.
    Binary properties have no @missing lines; their default is "no".

  * In UnicodeData.txt, a pair of lines whose names end in ", First>" and
    ", Last>" stands for a whole range of code points (UAX #44,
    Section 4.2.3).

  * The surrogates U+D800..U+DFFF are code points and have property
    values like any others; nothing here removes them.
"""

import argparse
import hashlib
import json
import re
import sys
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIBRARY = HERE.parent
MANIFEST = HERE / "ucd-sources.json"

MAX_CP = 0x10FFFF
NUM_CP = MAX_CP + 1

# The UCD files this script reads, relative to the ucd/ directory of a
# version.  The ones marked True yield a generated book; the others are
# used only to interpret or cross-check those.
UCD_FILES = {
    "DerivedCoreProperties.txt": True,
    "PropList.txt": True,
    "UnicodeData.txt": True,
    "DerivedNormalizationProps.txt": True,
    "extracted/DerivedCombiningClass.txt": True,
    "extracted/DerivedBidiClass.txt": True,
    "NormalizationTest.txt": True,
    "CompositionExclusions.txt": False,
    "extracted/DerivedDecompositionType.txt": False,
    "PropertyValueAliases.txt": False,
}

# Hangul syllables (Unicode Standard, Section 3.12).  Their canonical
# decompositions are algorithmic and are not listed in UnicodeData.txt.
HANGUL_S_BASE = 0xAC00
HANGUL_S_COUNT = 11172

# The Bidi_Class values of the explicit directional formatting characters
# (UAX #9, Sections 2.1 to 2.5), by their short aliases.
BIDI_EXPLICIT_FORMATTING = ["LRE", "RLE", "LRO", "RLO", "PDF",
                            "LRI", "RLI", "FSI", "PDI"]


def die(message):
    sys.exit("generate-ucd-books.py: error: " + message)


###############################################################################
# Reading the UCD.

class Source:
    """A UCD file that has been read: its bytes, text, URL and SHA-256."""

    def __init__(self, version, ucd_dir, relpath):
        self.relpath = relpath
        self.url = canonical_url(version, relpath)
        self.data = (ucd_dir / relpath).read_bytes()
        self.sha256 = hashlib.sha256(self.data).hexdigest()
        self.text = self.data.decode("utf-8")
        self.lines = self.text.split("\n")
        check_header_version(version, relpath, self.lines)


def canonical_url(version, relpath):
    return "https://www.unicode.org/Public/%s/ucd/%s" % (version, relpath)


def check_header_version(version, relpath, lines):
    """Most UCD files start with '# <Name>-<version>.txt'; check it."""
    stem = Path(relpath).stem
    m = re.match(r"^# %s-(\d+\.\d+\.\d+)\.txt\s*$" % re.escape(stem),
                 lines[0] if lines else "")
    if m:
        if m.group(1) != version:
            die("%s is for Unicode %s, not %s"
                % (relpath, m.group(1), version))
    elif stem != "UnicodeData":
        # UnicodeData.txt has no header; every other file we read does.
        die("%s: no version in the first line: %r" % (relpath, lines[:1]))


CP_RANGE_RE = re.compile(r"^([0-9A-F]{4,6})(?:\.\.([0-9A-F]{4,6}))?$")


def parse_cp_range(field, where):
    m = CP_RANGE_RE.match(field)
    if not m:
        die("%s: bad code point or range: %r" % (where, field))
    lo = int(m.group(1), 16)
    hi = int(m.group(2), 16) if m.group(2) else lo
    if not (0 <= lo <= hi <= MAX_CP):
        die("%s: bad range: %r" % (where, field))
    return lo, hi


def parse_property_file(source):
    """Parse a UCD file in the usual 'range ; field ; field # comment' form.

    Return (entries, missing): two lists of (lo, hi, fields), in file
    order, the first for the data lines and the second for the
    '# @missing:' lines.  The fields are stripped strings.
    """
    entries, missing = [], []
    for number, line in enumerate(source.lines, start=1):
        where = "%s:%d" % (source.relpath, number)
        m = re.match(r"^#\s*@missing:\s*(.*)$", line)
        if m:
            fields = [f.strip() for f in m.group(1).split(";")]
            lo, hi = parse_cp_range(fields[0], where)
            missing.append((lo, hi, fields[1:]))
            continue
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split(";")]
        lo, hi = parse_cp_range(fields[0], where)
        entries.append((lo, hi, fields[1:]))
    return entries, missing


def binary_property(source, parsed, name):
    """The set of code points with a binary property, as a bool list.

    Binary properties are listed as 'range ; Name'.  Code points not
    listed do not have the property (there are no @missing lines for
    binary properties).
    """
    entries, missing = parsed
    for _, _, fields in missing:
        if fields and fields[0] == name:
            die("%s: unexpected @missing line for binary property %s"
                % (source.relpath, name))
    has = [False] * NUM_CP
    found = False
    for lo, hi, fields in entries:
        if fields[0] != name:
            continue
        if len(fields) != 1:
            die("%s: %s has a value; it is not binary"
                % (source.relpath, name))
        found = True
        for cp in range(lo, hi + 1):
            if has[cp]:
                die("%s: U+%04X listed twice for %s"
                    % (source.relpath, cp, name))
            has[cp] = True
    if not found:
        die("%s: property %s not found" % (source.relpath, name))
    return has


def enumerated_property(source, parsed, name=None):
    """The value of an enumerated property for every code point, as a list.

    If NAME is None the file is for a single property and its lines are
    'range ; value'; otherwise the lines of interest are
    'range ; NAME ; value'.  Defaults come from the @missing lines, which
    are applied in file order (later lines override earlier ones), and
    then the data lines are applied.  Every code point must end up with a
    value, and no code point may be listed twice.
    """
    entries, missing = parsed
    skip = 0 if name is None else 1
    value = [None] * NUM_CP
    for lo, hi, fields in missing:
        if name is not None and (not fields or fields[0] != name):
            continue
        if len(fields) != skip + 1:
            die("%s: bad @missing line for %s" % (source.relpath, name))
        for cp in range(lo, hi + 1):
            value[cp] = fields[skip]
    listed = [False] * NUM_CP
    for lo, hi, fields in entries:
        if name is not None and fields[0] != name:
            continue
        if len(fields) != skip + 1:
            die("%s: bad line for %s at U+%04X"
                % (source.relpath, name, lo))
        for cp in range(lo, hi + 1):
            if listed[cp]:
                die("%s: U+%04X listed twice for %s"
                    % (source.relpath, cp, name))
            listed[cp] = True
            value[cp] = fields[skip]
    for cp in range(NUM_CP):
        if value[cp] is None:
            die("%s: no value and no @missing default for U+%04X (%s)"
                % (source.relpath, cp, name))
    return value


def parse_value_aliases(source):
    """Parse PropertyValueAliases.txt.

    Return a dict from (property short name, any alias of a value) to the
    list of all the aliases of that value, in file order.  For ccc the
    first alias is the number.
    """
    aliases = {}
    for line in source.lines:
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split(";")]
        prop, names = fields[0], fields[1:]
        for alias in names:
            aliases[(prop, alias)] = names
    return aliases


def parse_unicode_data(source):
    """Parse UnicodeData.txt.

    Return (ccc, decomposition, listed): ccc[cp] is the
    Canonical_Combining_Class (field 3) as an int; decomposition[cp] is
    None or (tag, mapping) for field 5, where tag is None for a canonical
    mapping and the '<...>' tag otherwise, and mapping is a list of code
    points; listed[cp] says whether the file covers cp.  Code points that
    are not covered get ccc 0 and no decomposition, which are the
    defaults that UAX #44 gives for unlisted code points.
    """
    ccc = [0] * NUM_CP
    decomposition = [None] * NUM_CP
    listed = [False] * NUM_CP
    previous = -1
    first = None  # (code point, range name) of a pending ', First>' line
    for number, line in enumerate(source.lines, start=1):
        where = "%s:%d" % (source.relpath, number)
        if not line:
            continue
        fields = line.split(";")
        if len(fields) != 15:
            die("%s: expected 15 fields" % where)
        cp = int(fields[0], 16)
        if not (previous < cp <= MAX_CP):
            die("%s: code points out of order" % where)
        name = fields[1]
        lo = cp
        range_line = True
        if first is not None:
            if name != "<%s, Last>" % first[1]:
                die("%s: expected the Last line of range %s"
                    % (where, first[1]))
            if fields[2:] != first_fields:
                die("%s: First and Last lines differ" % where)
            lo = first[0] + 1  # the First line was already recorded
            first = None
        elif name.endswith(", First>"):
            first = (cp, name[1:-len(", First>")])
            first_fields = fields[2:]
        elif name.endswith(", Last>"):
            die("%s: Last without First" % where)
        else:
            range_line = False
        this_ccc = int(fields[3])
        if not (0 <= this_ccc <= 254):
            die("%s: bad combining class" % where)
        this_decomposition = None
        if fields[5]:
            if range_line:
                die("%s: decomposition in a First/Last range" % where)
            parts = fields[5].split(" ")
            tag = None
            if parts[0].startswith("<"):
                if not re.match(r"^<[A-Za-z]+>$", parts[0]):
                    die("%s: bad decomposition tag" % where)
                tag, parts = parts[0], parts[1:]
            if not parts or not all(re.match(r"^[0-9A-F]{4,6}$", p)
                                    for p in parts):
                die("%s: bad decomposition mapping" % where)
            this_decomposition = (tag, [int(p, 16) for p in parts])
        for c in range(lo, cp + 1):
            listed[c] = True
            ccc[c] = this_ccc
            decomposition[c] = this_decomposition
        previous = cp
    if first is not None:
        die("%s: First without Last at the end" % source.relpath)
    return ccc, decomposition, listed


def parse_normalization_test(source):
    """Parse NormalizationTest.txt into a list of (part number, tests).

    Each test is a list of the five columns, each a list of code points.
    """
    parts = []
    for number, line in enumerate(source.lines, start=1):
        where = "%s:%d" % (source.relpath, number)
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"^@Part(\d+)$", line)
        if m:
            if int(m.group(1)) != len(parts):
                die("%s: parts out of order" % where)
            parts.append((len(parts), []))
            continue
        fields = line.split(";")
        # each line ends with a semicolon, so there is an empty sixth field
        if len(fields) != 6 or fields[5].strip() or not parts:
            die("%s: bad test line" % where)
        columns = []
        for field in fields[:5]:
            cps = [int(x, 16) for x in field.split()]
            if not cps or not all(0 <= cp <= MAX_CP for cp in cps):
                die("%s: bad column" % where)
            columns.append(cps)
        parts[-1][1].append(columns)
    if not parts:
        die("%s: no tests" % source.relpath)
    return parts


###############################################################################
# From per-code-point values to sorted tables.

def to_ranges(has):
    """The maximal ranges (lo, hi) of code points cp with has[cp] true."""
    ranges = []
    cp = 0
    while cp < NUM_CP:
        if has[cp]:
            lo = cp
            while cp + 1 < NUM_CP and has[cp + 1]:
                cp += 1
            ranges.append((lo, cp))
        cp += 1
    return ranges


def check_ranges(ranges):
    """Sorted, disjoint and not adjacent: the maximal ranges of a set."""
    previous_hi = -2
    for lo, hi in ranges:
        assert 0 <= lo <= hi <= MAX_CP
        assert previous_hi + 1 < lo
        previous_hi = hi


###############################################################################
# Writing ACL2.

def hexcp(cp):
    return "#x%04X" % cp


class Book:
    """The text of one generated book."""

    def __init__(self, version, name, title, sources, includes,
                 system_includes=()):
        self.version = version
        self.name = name
        self.lines = []
        out = self.lines.append
        out("; Unicode Library")
        out(";")
        out("; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)")
        out(";")
        out("; License: A 3-clause BSD license."
            " See the LICENSE file distributed with ACL2.")
        out(";")
        out("; Author: Eric McCarthy (bendyarm on GitHub)")
        out("")
        out(";" * 80)
        out("")
        out("; " + title)
        out(";")
        out("; This file is GENERATED by ../../tools/generate-ucd-books.py"
            " -- do not edit it.")
        out("; To regenerate it, see the README.md file"
            " in the directory two levels up.")
        out(";")
        out("; Unicode version: " + version)
        for source in sources:
            out("; Source: " + source.url)
            out("; SHA-256: " + source.sha256)
        out(";")
        out("; The tables in this file are derived from"
            " the Unicode Character Database,")
        out("; which is Copyright (C) Unicode, Inc."
            " and is distributed under the")
        out("; Unicode License V3;"
            " see the file LICENSE-UNICODE two directories up.")
        out("")
        out(";" * 80)
        out("")
        out('(in-package "UNICODE")')
        out("")
        for include in includes:
            out('(include-book "../../%s")' % include)
        if includes:
            out("")
        for include in system_includes:
            out('(include-book "%s" :dir :system)' % include)
        if system_includes:
            out("")

    def comment(self, text=""):
        for line in text.split("\n"):
            self.lines.append(("; " + line).rstrip())

    def blank(self):
        self.lines.append("")

    def rule(self):
        self.lines.append(";" * 80)
        self.lines.append("")

    def constant(self, name):
        return "*%s-v%s*" % (name, self.version)

    def range_list(self, name, has, what):
        """Emit a constant whose value is the list of the maximal ranges
        of the code points cp with has[cp] true."""
        ranges = to_ranges(has)
        check_ranges(ranges)
        self.comment("%s: %d ranges, %d code points."
                     % (what, len(ranges), sum(has)))
        self.blank()
        const = self.constant(name)
        self.lines.append("(defconst %s" % const)
        if not ranges:
            self.lines.append("  nil)")
        else:
            items = ["(range %s %s)" % (hexcp(lo), hexcp(hi))
                     for lo, hi in ranges]
            self.lines.append("  (list %s" % items[0])
            for item in items[1:]:
                self.lines.append("        %s" % item)
            self.lines[-1] += "))"
        self.blank()
        self.assert_equal("(len %s)" % const, len(ranges))
        self.assert_equal("(range-list-size %s)" % const, sum(has))
        self.blank()

    def tree_map(self, name, entries, quoted, recognizer):
        """Emit a constant whose value is the tree map with the given
        entries, which are the texts of the pairs of an alist: either
        the elements of a quoted list, or forms to evaluate."""
        const = self.constant(name)
        self.lines.append("(defconsts %s" % const)
        self.lines.append("  (treemap::update-from-alist")
        if not entries:
            self.lines.append("   nil")
        elif quoted:
            self.lines.append("   '(%s" % entries[0])
            for entry in entries[1:]:
                self.lines.append("     %s" % entry)
            self.lines[-1] += ")"
        else:
            self.lines.append("   (list %s" % entries[0])
            for entry in entries[1:]:
                self.lines.append("         %s" % entry)
            self.lines[-1] += ")"
        self.lines.append("   (treemap::empty)))")
        self.blank()
        self.assert_holds("(%s %s)" % (recognizer, const))
        self.assert_equal("(treemap::size %s)" % const, len(entries))
        return const

    def assert_holds(self, form):
        """Emit an assertion that FORM is true."""
        line = "(assert-event %s)" % form
        if len(line) <= 79:
            self.lines.append(line)
        else:
            self.lines.append("(assert-event")
            self.lines.append(" %s)" % form)

    def assert_equal(self, left, right):
        """Emit an assertion that LEFT is equal to RIGHT."""
        line = "(assert-event (equal %s %s))" % (left, right)
        if len(line) <= 79:
            self.lines.append(line)
        else:
            self.lines.append("(assert-event")
            self.lines.append(" (equal %s" % left)
            self.lines.append("        %s))" % right)

    def text(self):
        return "\n".join(self.lines).rstrip("\n") + "\n"


def book_derived_core_properties(version, sources):
    source = sources["DerivedCoreProperties.txt"]
    parsed = parse_property_file(source)
    book = Book(version, "derived-core-properties",
                "Properties from DerivedCoreProperties.txt.",
                [source], ["ranges"])
    xid_start = binary_property(source, parsed, "XID_Start")
    xid_continue = binary_property(source, parsed, "XID_Continue")
    book.range_list("xid-start", xid_start, "XID_Start")
    book.rule()
    book.range_list("xid-continue", xid_continue, "XID_Continue")
    return book


def book_prop_list(version, sources):
    source = sources["PropList.txt"]
    parsed = parse_property_file(source)
    book = Book(version, "prop-list",
                "Properties from PropList.txt.",
                [source], ["ranges"])
    book.range_list("pattern-white-space",
                   binary_property(source, parsed, "Pattern_White_Space"),
                   "Pattern_White_Space")
    book.rule()
    book.range_list("bidi-control",
                   binary_property(source, parsed, "Bidi_Control"),
                   "Bidi_Control")
    return book


def combining_classes(sources):
    """Canonical_Combining_Class of every code point, as ints,
    from extracted/DerivedCombiningClass.txt."""
    source = sources["extracted/DerivedCombiningClass.txt"]
    aliases = parse_value_aliases(sources["PropertyValueAliases.txt"])
    value = enumerated_property(source, parse_property_file(source))

    def number(v):
        # The data lines give numbers; the @missing line gives a name.
        if re.match(r"^\d+$", v):
            n = int(v)
        elif ("ccc", v) in aliases:
            n = int(aliases[("ccc", v)][0])
        else:
            die("%s: unknown combining class %r" % (source.relpath, v))
        if not (0 <= n <= 254):
            die("%s: bad combining class %r" % (source.relpath, v))
        return n

    cache = {}
    result = []
    for v in value:
        if v not in cache:
            cache[v] = number(v)
        result.append(cache[v])
    return result


def book_derived_combining_class(version, sources):
    source = sources["extracted/DerivedCombiningClass.txt"]
    book = Book(version, "derived-combining-class",
                "Canonical_Combining_Class,"
                " from extracted/DerivedCombiningClass.txt.",
                [source], ["maps"], ["std/util/defconsts"])
    ccc = combining_classes(sources)
    entries = [(cp, c) for cp, c in enumerate(ccc) if c != 0]
    book.comment(
        "The map from the code points whose Canonical_Combining_Class\n"
        "is not 0 (Not_Reordered) to their classes.\n"
        "All the code points that are not in the map have class 0:\n"
        "that is the file's @missing default, and the generator checks\n"
        "that the code points the file lists with class 0 are not here.\n"
        "%d code points, %d distinct classes."
        % (len(entries), len(set(c for _, c in entries))))
    book.blank()
    book.tree_map("canonical-combining-class",
                  ["(%s . %d)" % (hexcp(cp), c) for cp, c in entries],
                  True, "combining-class-mapp")
    return book


def book_unicode_data(version, sources):
    source = sources["UnicodeData.txt"]
    book = Book(version, "unicode-data",
                "Decomposition mappings, from UnicodeData.txt.",
                [source], ["maps"], ["std/util/defconsts"])
    ccc, decomposition, listed = parse_unicode_data(source)

    # Cross-check: field 3 against extracted/DerivedCombiningClass.txt.
    derived_ccc = combining_classes(sources)
    for cp in range(NUM_CP):
        if ccc[cp] != derived_ccc[cp]:
            die("combining class of U+%04X: UnicodeData.txt has %d,"
                " DerivedCombiningClass.txt has %d"
                % (cp, ccc[cp], derived_ccc[cp]))

    # Cross-check: field 5 against extracted/DerivedDecompositionType.txt.
    # The Hangul syllables have type Canonical there although their
    # decompositions are not listed in UnicodeData.txt.
    dt_source = sources["extracted/DerivedDecompositionType.txt"]
    dt = enumerated_property(dt_source, parse_property_file(dt_source))
    for cp in range(NUM_CP):
        if HANGUL_S_BASE <= cp < HANGUL_S_BASE + HANGUL_S_COUNT:
            expected = "Canonical"
            if decomposition[cp] is not None:
                die("U+%04X: Hangul syllable with a listed decomposition"
                    % cp)
        elif decomposition[cp] is None:
            expected = "None"
        elif decomposition[cp][0] is None:
            expected = "Canonical"
        else:
            expected = "a compatibility type"
        actual = dt[cp]
        if actual not in ("None", "Canonical"):
            actual = "a compatibility type"
        if actual != expected:
            die("decomposition type of U+%04X: UnicodeData.txt implies %s,"
                " DerivedDecompositionType.txt has %s"
                % (cp, expected, dt[cp]))

    canonical = [(cp, d[1]) for cp, d in enumerate(decomposition)
                 if d is not None and d[0] is None]
    compatibility = [(cp, d[1]) for cp, d in enumerate(decomposition)
                     if d is not None and d[0] is not None]

    def items(table):
        return ["(%s)" % " ".join(hexcp(c) for c in [cp] + mapping)
                for cp, mapping in table]

    book.comment(
        "This file has the Decomposition_Mapping property (field 5 of\n"
        "UnicodeData.txt), in two maps: one for the canonical mappings\n"
        "(the ones without a <tag>) and one for the compatibility\n"
        "mappings (the ones with a <tag>; the tag is not recorded here).\n"
        "Each map is built from an alist whose entries are lists:\n"
        "a code point, then the code points of its mapping.\n"
        "The mappings are as in the file: they are not expanded\n"
        "recursively.  A code point that is in neither map has no\n"
        "decomposition mapping (that is, it maps to itself), with the\n"
        "exception of the Hangul syllables U+AC00..U+D7A3, whose canonical\n"
        "decompositions are given by an algorithm, not by the file.\n"
        "(The code points of the First/Last ranges of the file, and the\n"
        "code points that the file does not list, have no mappings.)")
    book.blank()
    book.comment("Canonical decomposition mappings: %d entries."
                 % len(canonical))
    book.blank()
    book.tree_map("canonical-decomposition-mapping", items(canonical),
                  True, "decomposition-mapp")
    book.blank()
    book.rule()
    book.comment("Compatibility decomposition mappings: %d entries."
                 % len(compatibility))
    book.blank()
    book.tree_map("compatibility-decomposition-mapping",
                  items(compatibility), True, "decomposition-mapp")
    return book


def full_composition_exclusion_from_primary_data(sources):
    """Full_Composition_Exclusion computed from CompositionExclusions.txt
    and UnicodeData.txt, as UAX #15 defines it.  Used only to cross-check
    DerivedNormalizationProps.txt."""
    ccc, decomposition, _ = parse_unicode_data(sources["UnicodeData.txt"])
    source = sources["CompositionExclusions.txt"]
    entries, _ = parse_property_file(source)
    excluded = [False] * NUM_CP
    for lo, hi, fields in entries:
        if fields:
            die("%s: unexpected fields" % source.relpath)
        for cp in range(lo, hi + 1):
            excluded[cp] = True
    for cp in range(NUM_CP):
        d = decomposition[cp]
        if d is None or d[0] is not None:
            continue
        mapping = d[1]
        if len(mapping) == 1:
            excluded[cp] = True  # singleton
        elif ccc[cp] != 0 or ccc[mapping[0]] != 0:
            excluded[cp] = True  # non-starter decomposition
    return excluded


def book_derived_normalization_props(version, sources):
    source = sources["DerivedNormalizationProps.txt"]
    parsed = parse_property_file(source)
    book = Book(version, "derived-normalization-props",
                "Properties from DerivedNormalizationProps.txt.",
                [source], ["ranges"])

    fce = binary_property(source, parsed, "Full_Composition_Exclusion")
    if fce != full_composition_exclusion_from_primary_data(sources):
        die("Full_Composition_Exclusion in DerivedNormalizationProps.txt"
            " differs from the one computed from CompositionExclusions.txt"
            " and UnicodeData.txt")
    book.range_list("full-composition-exclusion", fce,
                   "Full_Composition_Exclusion")

    # The quick check properties.  Their default, from the @missing
    # lines, is Yes; we emit the code points with the other values.
    for prop, name, values in [("NFD_QC", "nfd-quick-check", "N"),
                               ("NFC_QC", "nfc-quick-check", "NM"),
                               ("NFKD_QC", "nfkd-quick-check", "N"),
                               ("NFKC_QC", "nfkc-quick-check", "NM")]:
        value = enumerated_property(source, parsed, prop)
        seen = set(value)
        if not seen <= set(["Yes", "Y"] + list(values)):
            die("%s: unexpected values %r" % (prop, seen))
        if value[0] != "Yes":
            die("%s: the default is not Yes" % prop)
        for v, word in [("N", "no"), ("M", "maybe")]:
            if v in values:
                book.rule()
                book.range_list("%s-%s" % (name, word),
                               [x == v for x in value],
                               "%s=%s" % (prop, word.capitalize()))
    return book


def book_derived_bidi_class(version, sources):
    source = sources["extracted/DerivedBidiClass.txt"]
    aliases = parse_value_aliases(sources["PropertyValueAliases.txt"])
    book = Book(version, "derived-bidi-class",
                "Part of Bidi_Class, from extracted/DerivedBidiClass.txt.",
                [source], ["maps"], ["std/util/defconsts"])
    value = enumerated_property(source, parse_property_file(source))
    short = {}
    for v in set(value):
        if ("bc", v) not in aliases:
            die("%s: unknown Bidi_Class %r" % (source.relpath, v))
        short[v] = aliases[("bc", v)][0]
    # We keep only the nine classes of interest.
    entries = [(cp, short[v]) for cp, v in enumerate(value)
               if short[v] in BIDI_EXPLICIT_FORMATTING]
    if set(v for _, v in entries) != set(BIDI_EXPLICIT_FORMATTING):
        die("%s: some explicit formatting class has no code points"
            % source.relpath)
    book.comment(
        "The map from the code points whose Bidi_Class is one of the\n"
        "classes of the explicit directional formatting characters\n"
        "(UAX #9, Sections 2.1 to 2.5) to their classes:\n"
        "LRE, RLE, LRO, RLO, PDF, LRI, RLI, FSI, PDI.\n"
        "The other values of Bidi_Class are not in this file.\n"
        "The classes are read from the derived file, honoring its\n"
        "@missing lines.\n"
        "%d code points." % len(entries))
    book.blank()
    book.tree_map("bidi-formatting-class",
                  ["(cons %s (bidi-formatting-class-%s))"
                   % (hexcp(cp), v.lower()) for cp, v in entries],
                  False, "bidi-formatting-class-mapp")
    return book


def book_normalization_test(version, sources):
    source = sources["NormalizationTest.txt"]
    parts = parse_normalization_test(source)
    book = Book(version, "normalization-test",
                "The normalization conformance test, NormalizationTest.txt.",
                [source], ["tests/normalization-test-types"],
                ["std/util/defconsts"])
    book.comment(
        "The value of the constant below is the list of the parts of the\n"
        "test file, in file order.  Each part has its number and its\n"
        "lines, in file order.  Each line has the five columns of a line\n"
        "of the file (source, NFC, NFD, NFKC, NFKD), each column being a\n"
        "list of code points.\n"
        "The book ../../tests/normalization-test-v%s runs the tests.\n"
        "%s"
        % (version,
           "\n".join("Part %d: %d lines." % (n, len(tests))
                     for n, tests in parts)))
    book.comment()
    book.comment(
        "The constant is introduced with DEFCONSTS, which evaluates the\n"
        "form when this book is certified and records the value, so that\n"
        "the thousands of calls below are not compiled.")
    book.blank()
    const = book.constant("normalization-test")
    lines = book.lines
    lines.append("(defconsts %s" % const)
    lines.append("  (list")
    for number, tests in parts:
        lines.append("   (normalization-test-part")
        lines.append("    %d" % number)
        lines.append("    (list")
        for columns in tests:
            lines.append("     (normalization-test-line %s)" % " ".join(
                "'(%s)" % " ".join(hexcp(cp) for cp in column)
                for column in columns))
        lines[-1] += "))"
    lines[-1] += "))"
    lines.append("")
    book.assert_equal("(len %s)" % const, len(parts))
    for number, tests in parts:
        lines.append("(assert-event")
        lines.append(" (equal (len (normalization-test-part->lines")
        lines.append("              (nth %d %s)))" % (number, const))
        lines.append("        %d))" % len(tests))
    return book


BOOKS = [book_derived_core_properties,
         book_prop_list,
         book_derived_combining_class,
         book_unicode_data,
         book_derived_normalization_props,
         book_derived_bidi_class,
         book_normalization_test]


CERT_ACL2 = """\
; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file is GENERATED by ../../tools/generate-ucd-books.py.

(include-book "../../portcullis")

; cert-flags: ? t
"""


###############################################################################
# Main.

def fetch(version, ucd_dir, base_url):
    for relpath in UCD_FILES:
        path = ucd_dir / relpath
        if path.exists():
            continue
        url = base_url.rstrip("/") + "/" + relpath
        print("fetching " + url)
        path.parent.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(url) as response:
            path.write_bytes(response.read())


def main():
    parser = argparse.ArgumentParser(
        description="Generate the data books of [books]/kestrel/unicode"
                    " from one version of the Unicode Character Database.",
        epilog="See the comment at the top of this script.")
    parser.add_argument("version", help="a Unicode version, e.g. 16.0.0")
    parser.add_argument("ucd_dir", type=Path,
                        help="directory with the UCD files of that version")
    parser.add_argument("--fetch", action="store_true")
    parser.add_argument("--base-url")
    parser.add_argument("--pin", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    version = args.version
    if not re.match(r"^[1-9]\d*\.\d+\.\d+$", version):
        die("the version must be written in full, like 16.0.0")
    if args.fetch:
        fetch(version, args.ucd_dir,
              args.base_url or canonical_url(version, ""))
    elif args.base_url:
        die("--base-url is only for --fetch")

    sources = {}
    for relpath in UCD_FILES:
        if not (args.ucd_dir / relpath).is_file():
            die("missing %s (use --fetch to download it)"
                % (args.ucd_dir / relpath))
        sources[relpath] = Source(version, args.ucd_dir, relpath)

    # The pinned SHA-256 values.
    manifest = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    read = {relpath: {"url": s.url, "sha256": s.sha256}
            for relpath, s in sorted(sources.items())}
    if args.pin:
        if args.check:
            die("--pin and --check do not go together")
        manifest[version] = read
        MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True)
                            + "\n")
        print("recorded the SHA-256 of %d files of Unicode %s in %s"
              % (len(read), version, MANIFEST.name))
    elif version not in manifest:
        die("Unicode %s is not in %s; use --pin to add it"
            % (version, MANIFEST.name))
    elif manifest[version] != read:
        for relpath in UCD_FILES:
            if manifest[version].get(relpath) != read[relpath]:
                print("  %s: SHA-256 %s, but %s has %s"
                      % (relpath, read[relpath]["sha256"], MANIFEST.name,
                         manifest[version].get(relpath, {}).get("sha256")))
        die("the UCD files differ from the ones recorded in %s"
            % MANIFEST.name)

    out_dir = LIBRARY / "data" / ("v" + version)
    outputs = {out_dir / "cert.acl2": CERT_ACL2}
    for make in BOOKS:
        book = make(version, sources)
        outputs[out_dir / (book.name + ".lisp")] = book.text()

    different = 0
    for path, text in outputs.items():
        old = path.read_text() if path.exists() else None
        if old == text:
            continue
        different += 1
        if args.check:
            print("differs: %s" % path)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            print("wrote %s" % path)
    if args.check:
        if different:
            sys.exit(1)
        print("the %d generated files of Unicode %s are up to date"
              % (len(outputs), version))
    elif not different:
        print("the %d generated files of Unicode %s were already up to date"
              % (len(outputs), version))


if __name__ == "__main__":
    main()
