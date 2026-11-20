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
               (so the extracted/ files are in UCD_DIR/extracted/ and
               emoji-data.txt is in UCD_DIR/emoji/), with the two data
               files of UTS #39 that are read in UCD_DIR/security/.
    --fetch    Download into UCD_DIR the needed files that are not
               already there.  The files of the UCD come from --base-url,
               which defaults to
               https://www.unicode.org/Public/<VERSION>/ucd/;
               the files of UTS #39 come from where the Unicode
               Consortium publishes them for that version (see
               canonical_url below).
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

  * The properties with many values (General_Category, Bidi_Class,
    Script, Script_Extensions, Block, Identifier_Type) are written as
    lists of runs that cover every code point, the defaults included.
    The default of Script_Extensions is written "<script>" in its file:
    it is the set of the one script that the Script property gives.

  * IdentifierStatus.txt and IdentifierType.txt are data files of
    UTS #39, not of the UCD.  They have a version of Unicode in their
    headers, which is checked like those of the UCD files.
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
    "extracted/DerivedGeneralCategory.txt": True,
    "NormalizationTest.txt": True,
    "Scripts.txt": True,
    "ScriptExtensions.txt": True,
    "Blocks.txt": True,
    "emoji/emoji-data.txt": True,
    "security/IdentifierStatus.txt": True,
    "security/IdentifierType.txt": True,
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
# The 23 values of Bidi_Class, in the order of UAX #9, Table 4.
BIDI_CLASSES = ["L", "R", "AL",
                "EN", "ES", "ET", "AN", "CS", "NSM", "BN",
                "B", "S", "WS", "ON",
                "LRE", "LRO", "RLE", "RLO", "PDF",
                "LRI", "RLI", "FSI", "PDI"]

# The 12 values of Identifier_Type, in the order of UTS #39, Table 1.
IDENTIFIER_TYPES = ["Not_Character", "Deprecated", "Default_Ignorable",
                    "Not_NFKC", "Not_XID", "Exclusion", "Obsolete",
                    "Technical", "Uncommon_Use", "Limited_Use",
                    "Inclusion", "Recommended"]

BIDI_EXPLICIT_FORMATTING = ["LRE", "RLE", "LRO", "RLO", "PDF",
                            "LRI", "RLI", "FSI", "PDI"]

# The values of General_Category, by their short aliases, in the order of
# UAX #44, Table 12.  This is also the order of the constructors of the
# ACL2 type general-category; the names of the constructors are the long
# aliases, which this script takes from PropertyValueAliases.txt.
GENERAL_CATEGORIES = ["Lu", "Ll", "Lt", "Lm", "Lo",
                      "Mn", "Mc", "Me",
                      "Nd", "Nl", "No",
                      "Pc", "Pd", "Ps", "Pe", "Pi", "Pf", "Po",
                      "Sm", "Sc", "Sk", "So",
                      "Zs", "Zl", "Zp",
                      "Cc", "Cf", "Cs", "Co", "Cn"]


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
    """Where the Unicode Consortium publishes a file of a version.

    The data files of UTS #39 are outside the ucd/ directory, and they
    moved: up to Unicode 16.0.0 they are in Public/security/<version>/,
    and from 17.0.0 on in Public/<version>/security/.
    """
    if relpath.startswith("security/"):
        name = relpath[len("security/"):]
        if int(version.split(".")[0]) <= 16:
            return ("https://www.unicode.org/Public/security/%s/%s"
                    % (version, name))
        return ("https://www.unicode.org/Public/%s/security/%s"
                % (version, name))
    return "https://www.unicode.org/Public/%s/ucd/%s" % (version, relpath)


def check_header_version(version, relpath, lines):
    """Most UCD files start with '# <Name>-<version>.txt'; check it.

    emoji-data.txt and the files of UTS #39 start with '# <Name>.txt'
    and give the version a few lines down, as 'Version: 17.0.0',
    'Version: 17.0' or 'Emoji Version 16.0'; check that instead.
    """
    stem = Path(relpath).stem
    m = re.match(r"^# %s-(\d+\.\d+\.\d+)\.txt\s*$" % re.escape(stem),
                 lines[0] if lines else "")
    if m:
        if m.group(1) != version:
            die("%s is for Unicode %s, not %s"
                % (relpath, m.group(1), version))
    elif stem == "UnicodeData":
        # UnicodeData.txt has no header; every other file we read does.
        pass
    elif lines and re.match(r"^# %s\.txt\s*$" % re.escape(stem), lines[0]):
        found = None
        for line in lines[1:15]:
            m = re.match(r"^#.*\bVersion:? (\d+\.\d+(?:\.\d+)?)\b", line)
            if m:
                found = m.group(1)
                break
        if found is None:
            die("%s: no version in the header" % relpath)
        if found != version and found + ".0" != version:
            die("%s is for Unicode %s, not %s" % (relpath, found, version))
    else:
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

    Return (ccc, decomposition, listed, category): ccc[cp] is the
    Canonical_Combining_Class (field 3) as an int; decomposition[cp] is
    None or (tag, mapping) for field 5, where tag is None for a canonical
    mapping and the '<...>' tag otherwise, and mapping is a list of code
    points; listed[cp] says whether the file covers cp; category[cp] is
    the General_Category (field 2), by its short alias.  Code points that
    are not covered get ccc 0, no decomposition and the category Cn,
    which are the defaults that UAX #44 gives for unlisted code points.
    """
    ccc = [0] * NUM_CP
    category = ["Cn"] * NUM_CP
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
        if fields[2] not in GENERAL_CATEGORIES or fields[2] == "Cn":
            die("%s: bad general category" % where)
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
            category[c] = fields[2]
            decomposition[c] = this_decomposition
        previous = cp
    if first is not None:
        die("%s: First without Last at the end" % source.relpath)
    return ccc, decomposition, listed, category


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


def to_runs(value):
    """The maximal runs (lo, hi, v) of code points with the same value v,
    in order: together they cover every code point exactly once."""
    runs = []
    lo = 0
    for cp in range(1, NUM_CP + 1):
        if cp == NUM_CP or value[cp] != value[lo]:
            runs.append((lo, cp - 1, value[lo]))
            lo = cp
    return runs


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

    def run_table(self, name, macro, covers, runs, strings):
        """Emit a constant whose value is a list of runs, written with
        the macro MACRO; STRINGS gives, for the value of a run, the list
        of the strings to write after its two code points.  The runs
        must cover every code point, which the predicate COVERS checks
        when the book is certified."""
        assert runs and runs[0][0] == 0 and runs[-1][1] == MAX_CP
        assert all(runs[i][1] + 1 == runs[i + 1][0]
                   for i in range(len(runs) - 1))
        const = self.constant(name)
        # With defconsts the list is built when the book is certified and
        # its value is stored in the certificate; a defconst of this size
        # takes the Lisp compiler much longer.
        self.lines.append("(defconsts %s" % const)
        self.lines.append("  (%s" % macro)
        for lo, hi, value in runs:
            line = "   (%s %s" % (hexcp(lo), hexcp(hi))
            for string in strings(value):
                assert '"' not in string and "\\" not in string
                word = ' "%s"' % string
                if len(line) + len(word) > 78:
                    self.lines.append(line)
                    line = "   " + word
                else:
                    line += word
            self.lines.append(line + ")")
        self.lines[-1] += "))"
        self.blank()
        self.assert_equal("(len %s)" % const, len(runs))
        self.assert_holds("(%s 0 #x10FFFF %s)" % (covers, const))
        self.blank()
        return const

    def assert_range_list_size(self, ranges_form, size):
        """Emit an assertion on the number of code points of a list of
        ranges, given as lines of ACL2."""
        self.lines.append("(assert-event")
        self.lines.append(" (equal (range-list-size")
        for line in ranges_form[:-1]:
            self.lines.append("         " + line)
        self.lines.append("         %s)" % ranges_form[-1])
        self.lines.append("        %d))" % size)

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
    book.rule()
    book.range_list("default-ignorable-code-point",
                    binary_property(source, parsed,
                                    "Default_Ignorable_Code_Point"),
                    "Default_Ignorable_Code_Point")
    for name in ["ID_Start", "ID_Continue"]:
        book.rule()
        book.range_list(name.lower().replace("_", "-"),
                        binary_property(source, parsed, name), name)
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
    for name in ["Join_Control", "Variation_Selector",
                 "Noncharacter_Code_Point", "Deprecated",
                 "Prepended_Concatenation_Mark", "Pattern_Syntax",
                 "Other_ID_Start", "Other_ID_Continue",
                 "ID_Compat_Math_Start", "ID_Compat_Math_Continue",
                 "Regional_Indicator"]:
        book.rule()
        book.range_list(name.lower().replace("_", "-"),
                        binary_property(source, parsed, name), name)
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


def parse_decimal_digits(source):
    """The decimal digit values of UnicodeData.txt, as a dict.

    Field 6 is the value of a decimal digit, from 0 to 9; a character
    that has it has Numeric_Type=Decimal, and then fields 7 and 8 have
    the same value (UAX #44, Table 9).  The ranges that are given by a
    First and a Last line have no values.
    """
    digits = {}
    for number, line in enumerate(source.lines, start=1):
        if not line:
            continue
        fields = line.split(";")
        if fields[6] == "":
            continue
        where = "%s:%d" % (source.relpath, number)
        if not re.match(r"^[0-9]$", fields[6]):
            die("%s: bad decimal digit value" % where)
        if fields[7] != fields[6] or fields[8] != fields[6]:
            die("%s: fields 6, 7 and 8 differ for a decimal digit" % where)
        if fields[1].endswith(", First>") or fields[1].endswith(", Last>"):
            die("%s: decimal digit value in a First/Last range" % where)
        digits[int(fields[0], 16)] = int(fields[6])
    return digits


def parse_bidi_classes(source):
    """The Bidi_Class of the code points that UnicodeData.txt lists.

    Field 4 is the Bidi_Class, by its abbreviation.  Return a dict from
    the listed code points to it; a First and a Last line give it to the
    code points between them too.  Used only to cross-check
    extracted/DerivedBidiClass.txt, which also has the default values of
    the code points that UnicodeData.txt does not list.
    """
    classes = {}
    first = None
    for number, line in enumerate(source.lines, start=1):
        if not line:
            continue
        fields = line.split(";")
        where = "%s:%d" % (source.relpath, number)
        if fields[4] not in BIDI_CLASSES:
            die("%s: bad bidirectional class" % where)
        cp = int(fields[0], 16)
        lo = cp
        if fields[1].endswith(", Last>"):
            if first is None or fields[4] != classes[first]:
                die("%s: First and Last lines differ" % where)
            lo = first + 1
        first = cp if fields[1].endswith(", First>") else None
        for c in range(lo, cp + 1):
            classes[c] = fields[4]
    return classes


def book_unicode_data(version, sources):
    source = sources["UnicodeData.txt"]
    book = Book(version, "unicode-data",
                "Decomposition mappings and decimal digit values,"
                " from UnicodeData.txt.",
                [source], ["maps"], ["std/util/defconsts"])
    ccc, decomposition, listed, _ = parse_unicode_data(source)

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
    digits = parse_decimal_digits(source)
    book.blank()
    book.rule()
    book.comment(
        "The values of the decimal digits (field 6 of UnicodeData.txt):\n"
        "a map from the code points that have Numeric_Type=Decimal\n"
        "to their values, which are numbers from 0 to 9.\n"
        "%d entries." % len(digits))
    book.blank()
    book.tree_map("decimal-digit",
                  ["(%s . %d)" % (hexcp(cp), v)
                   for cp, v in sorted(digits.items())],
                  True, "decimal-digit-mapp")
    return book


def full_composition_exclusion_from_primary_data(sources):
    """Full_Composition_Exclusion computed from CompositionExclusions.txt
    and UnicodeData.txt, as UAX #15 defines it.  Used only to cross-check
    DerivedNormalizationProps.txt."""
    ccc, decomposition, _, _ = parse_unicode_data(sources["UnicodeData.txt"])
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
                "Bidi_Class, from extracted/DerivedBidiClass.txt.",
                [source], ["maps", "bidi-class-tables"],
                ["std/util/defconsts"])
    value = enumerated_property(source, parse_property_file(source))
    short = {}
    for v in set(value):
        if ("bc", v) not in aliases:
            die("%s: unknown Bidi_Class %r" % (source.relpath, v))
        short[v] = aliases[("bc", v)][0]
    # Cross-check with field 4 of UnicodeData.txt, for the code points
    # that it lists (the others have default values, which only the
    # derived file gives).
    listed = parse_bidi_classes(sources["UnicodeData.txt"])
    for cp, v in sorted(listed.items()):
        if short[value[cp]] != v:
            die("%s: U+%04X is %s here but %s in UnicodeData.txt"
                % (source.relpath, cp, short[value[cp]], v))
    # For the first table we keep only the nine classes of interest.
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
        "The table after this one has all the values of Bidi_Class.\n"
        "The classes are read from the derived file, honoring its\n"
        "@missing lines.\n"
        "%d code points." % len(entries))
    book.blank()
    book.tree_map("bidi-formatting-class",
                  ["(cons %s (bidi-formatting-class-%s))"
                   % (hexcp(cp), v.lower()) for cp, v in entries],
                  False, "bidi-formatting-class-mapp")
    # The whole property.
    value = [short[v] for v in value]
    if set(value) != set(BIDI_CLASSES):
        die("%s: the values are not the 23 of UAX #9, Table 4"
            % source.relpath)
    long_name = {v: aliases[("bc", v)][1] for v in BIDI_CLASSES}
    runs = to_runs(value)
    count = {v: 0 for v in BIDI_CLASSES}
    for lo, hi, v in runs:
        count[v] += hi - lo + 1
    book.blank()
    book.rule()
    book.comment(
        "The Bidi_Class of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the value that all the code points from the first to the last"
        " have.\n"
        "A run is written as a triple, with the abbreviation of the value;\n"
        "the macro bidi-class-run-table makes the list of runs"
        " from the triples.\n"
        "The runs are maximal and in order, and cover every code point.\n"
        "The values are read from the derived file, honoring its @missing"
        " lines,\n"
        "which give the defaults of the code points that are not assigned.\n"
        "%d runs.  Code points per value:" % len(runs))
    for v in BIDI_CLASSES:
        book.comment("  %-3s  %-23s %7d" % (v, long_name[v], count[v]))
    book.blank()
    const = book.run_table("bidi-class", "bidi-class-run-table",
                           "bidi-class-run-list-covers-p", runs,
                           lambda v: [v])
    book.comment("The number of code points that have each value.")
    book.blank()
    for v in BIDI_CLASSES:
        book.assert_range_list_size(
            ["(bidi-class-run-list-ranges",
             " (bidi-class-%s)" % long_name[v].lower().replace("_", "-"),
             " %s)" % const],
            count[v])
    return book


def book_derived_general_category(version, sources):
    source = sources["extracted/DerivedGeneralCategory.txt"]
    aliases = parse_value_aliases(sources["PropertyValueAliases.txt"])
    book = Book(version, "derived-general-category",
                "General_Category,"
                " from extracted/DerivedGeneralCategory.txt.",
                [source], ["general-category-tables"],
                ["std/util/defconsts"])
    value = enumerated_property(source, parse_property_file(source))
    short = {}
    for v in set(value):
        if ("gc", v) not in aliases:
            die("%s: unknown General_Category %r" % (source.relpath, v))
        short[v] = aliases[("gc", v)][0]
    value = [short[v] for v in value]
    if set(value) != set(GENERAL_CATEGORIES):
        die("%s: the values are not the thirty of UAX #44, Table 12"
            % source.relpath)
    # Cross-check with field 2 of UnicodeData.txt, whose default is Cn.
    _, _, _, category = parse_unicode_data(sources["UnicodeData.txt"])
    for cp in range(NUM_CP):
        if value[cp] != category[cp]:
            die("%s: U+%04X is %s here but %s in UnicodeData.txt"
                % (source.relpath, cp, value[cp], category[cp]))
    long_name = {v: aliases[("gc", v)][1] for v in GENERAL_CATEGORIES}

    def constructor(v):
        return "(general-category-%s)" % long_name[v].lower().replace("_",
                                                                      "-")

    runs = to_runs(value)
    count = {v: 0 for v in GENERAL_CATEGORIES}
    for lo, hi, v in runs:
        count[v] += hi - lo + 1
    book.comment(
        "The General_Category of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the value that all the code points from the first to the last"
        " have.\n"
        "A run is written as a triple, with the abbreviation of the value;\n"
        "the macro general-category-run-table makes the list of runs"
        " from the triples.\n"
        "The runs are maximal and in order, and cover every code point.\n"
        "The values are read from the derived file, which lists every"
        " code point,\n"
        "and are checked against field 2 of UnicodeData.txt.\n"
        "%d runs.  Code points per value:" % len(runs))
    for v in GENERAL_CATEGORIES:
        book.comment("  %s  %-21s %7d" % (v, long_name[v], count[v]))
    book.blank()
    const = book.run_table("general-category",
                           "general-category-run-table",
                           "general-category-run-list-covers-p", runs,
                           lambda v: [v])
    book.comment("The number of code points that have each value.")
    book.blank()
    for v in GENERAL_CATEGORIES:
        book.lines.append("(assert-event")
        book.lines.append(" (equal (range-list-size")
        book.lines.append("         (general-category-run-list-ranges")
        book.lines.append("          %s" % constructor(v))
        book.lines.append("          %s))" % const)
        book.lines.append("        %d))" % count[v])
    return book


def script_aliases(sources):
    """The scripts of PropertyValueAliases.txt: a list of (code, long
    name) in file order, and a dict from every alias to the code."""
    aliases = parse_value_aliases(sources["PropertyValueAliases.txt"])
    scripts, code = [], {}
    for (prop, alias), names in aliases.items():
        if prop != "sc":
            continue
        if not re.match(r"^[A-Z][a-z]{3}$", names[0]):
            die("PropertyValueAliases.txt: bad script code %r" % names[0])
        if (names[0], names[1]) not in scripts:
            scripts.append((names[0], names[1]))
        code[alias] = names[0]
    return scripts, code


def script_constructor(long_name):
    return "(script-%s)" % long_name.lower().replace("_", "-")


def script_values(sources):
    """The Script of every code point, as its four-letter code."""
    source = sources["Scripts.txt"]
    scripts, code = script_aliases(sources)
    value = enumerated_property(source, parse_property_file(source))
    for v in set(value):
        if v not in code:
            die("%s: unknown script %r" % (source.relpath, v))
    return scripts, code, [code[v] for v in value]


def book_scripts(version, sources):
    source = sources["Scripts.txt"]
    aliases_source = sources["PropertyValueAliases.txt"]
    book = Book(version, "scripts",
                "Script, from Scripts.txt.",
                [source, aliases_source], ["script-tables"],
                ["std/util/defconsts"])
    scripts, _, value = script_values(sources)
    long_name = dict(scripts)
    book.comment(
        "The scripts of this version of Unicode: the four-letter code and\n"
        "the long name of each value of the Script property, from\n"
        "PropertyValueAliases.txt.  Each must be an entry of the table\n"
        "from which the type of the scripts is defined.\n"
        "%d scripts." % len(scripts))
    book.blank()
    book.lines.append("(assert-event")
    book.lines.append(" (script-table-agrees-p")
    book.lines.append("  '((\"%s\" \"%s\")" % scripts[0])
    for entry in scripts[1:]:
        book.lines.append("    (\"%s\" \"%s\")" % entry)
    book.lines[-1] += ")))"
    book.blank()
    book.rule()
    runs = to_runs(value)
    count = {}
    for lo, hi, v in runs:
        count[v] = count.get(v, 0) + hi - lo + 1
    book.comment(
        "The Script of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the value that all the code points from the first to the last"
        " have.\n"
        "A run is written as a triple, with the four-letter code of the"
        " script;\n"
        "the macro script-run-table makes the list of runs"
        " from the triples.\n"
        "The runs are maximal and in order, and cover every code point.\n"
        "The code points that the file does not list have the value Zzzz\n"
        "(Unknown), as its @missing line says.\n"
        "%d runs; %d scripts have code points." % (len(runs), len(count)))
    book.blank()
    const = book.run_table("script", "script-run-table",
                           "script-run-list-covers-p", runs,
                           lambda v: [v])
    book.comment("The number of code points that have each value.")
    book.blank()
    for code, name in scripts:
        book.assert_range_list_size(
            ["(script-run-list-ranges",
             " %s" % script_constructor(name),
             " %s)" % const],
            count.get(code, 0))
    return book


def book_script_extensions(version, sources):
    source = sources["ScriptExtensions.txt"]
    scripts_source = sources["Scripts.txt"]
    book = Book(version, "script-extensions",
                "Script_Extensions, from ScriptExtensions.txt.",
                [source, scripts_source], ["script-tables"],
                ["std/util/defconsts"])
    scripts, code, script = script_values(sources)
    entries, missing = parse_property_file(source)
    if [fields for _, _, fields in missing] != [["<script>"]]:
        die("%s: the default is not <script>" % source.relpath)
    value = [None] * NUM_CP
    explicit = 0
    for lo, hi, fields in entries:
        if len(fields) != 1:
            die("%s: bad line at U+%04X" % (source.relpath, lo))
        codes = tuple(fields[0].split())
        if not codes or len(set(codes)) != len(codes):
            die("%s: bad set at U+%04X" % (source.relpath, lo))
        for c in codes:
            if code.get(c) != c:
                die("%s: %r is not the code of a script"
                    % (source.relpath, c))
        for cp in range(lo, hi + 1):
            if value[cp] is not None:
                die("%s: U+%04X listed twice" % (source.relpath, cp))
            value[cp] = codes
            explicit += 1
    for cp in range(NUM_CP):
        if value[cp] is None:
            value[cp] = (script[cp],)
    runs = to_runs(value)
    count = {}
    for lo, hi, codes in runs:
        for c in codes:
            count[c] = count.get(c, 0) + hi - lo + 1
    book.comment(
        "The Script_Extensions of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the set of scripts that all the code points from the first\n"
        "to the last have.\n"
        "A run is written as its two code points followed by the"
        " four-letter codes\n"
        "of the scripts, in the order of the file;\n"
        "the macro script-extensions-run-table makes the list of runs.\n"
        "The runs are maximal and in order, and cover every code point.\n"
        "The file lists %d code points.  The others have the default,\n"
        "which the file writes <script>: the set of the one script that\n"
        "Scripts.txt gives to the code point.\n"
        "%d runs." % (explicit, len(runs)))
    book.blank()
    const = book.run_table("script-extensions",
                           "script-extensions-run-table",
                           "script-extensions-run-list-covers-p", runs,
                           lambda codes: list(codes))
    book.comment("The number of code points whose set has each script.")
    book.blank()
    for c, name in scripts:
        book.assert_range_list_size(
            ["(script-extensions-run-list-member-ranges",
             " %s" % script_constructor(name),
             " %s)" % const],
            count.get(c, 0))
    return book


def book_blocks(version, sources):
    source = sources["Blocks.txt"]
    book = Book(version, "blocks",
                "Block, from Blocks.txt.",
                [source], ["block-tables"], ["std/util/defconsts"])
    entries, missing = parse_property_file(source)
    if [fields for _, _, fields in missing] != [["No_Block"]]:
        die("%s: the default is not No_Block" % source.relpath)
    names = [fields[0] for _, _, fields in entries]
    if len(set(names)) != len(names) or "No_Block" in names:
        die("%s: a block is listed twice" % source.relpath)
    for name in names:
        if not re.match(r"^[A-Za-z0-9][A-Za-z0-9 -]*[A-Za-z0-9]$", name):
            die("%s: unexpected block name %r" % (source.relpath, name))
    value = enumerated_property(source, (entries, missing))
    runs = to_runs(value)
    for lo, hi, fields in entries:
        if (lo, hi, fields[0]) not in runs:
            die("%s: block %r is not one run" % (source.relpath, fields[0]))
    book.comment(
        "The Block of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the name of the block that all the code points from the first\n"
        "to the last are in.\n"
        "The names are written as in the file, with spaces.\n"
        "The macro block-run-table makes the list of runs from the"
        " triples.\n"
        "The runs are in order and cover every code point:\n"
        "each block is one run, and the code points between blocks\n"
        "are in runs with the value No_Block, as the @missing line of the"
        " file says.\n"
        "%d blocks; %d runs; %d code points are in no block."
        % (len(entries), len(runs), value.count("No_Block")))
    book.blank()
    const = book.run_table("block", "block-run-table",
                           "block-run-list-covers-p", runs,
                           lambda v: [v])
    book.comment("The number of blocks, and each block is one run.")
    book.blank()
    book.assert_equal("(len (block-run-list-names %s))" % const,
                      len(entries))
    book.assert_holds("(no-duplicatesp-equal (block-run-list-names %s))"
                      % const)
    return book


def book_emoji_data(version, sources):
    source = sources["emoji/emoji-data.txt"]
    parsed = parse_property_file(source)
    book = Book(version, "emoji-data",
                "Emoji properties, from emoji/emoji-data.txt.",
                [source], ["ranges"])
    names = ["Emoji", "Emoji_Presentation", "Emoji_Modifier",
             "Emoji_Modifier_Base", "Emoji_Component",
             "Extended_Pictographic"]
    if set(fields[0] for _, _, fields in parsed[0]) != set(names):
        die("%s: the properties are not the six expected ones"
            % source.relpath)
    for i, name in enumerate(names):
        if i:
            book.rule()
        book.range_list(name.lower().replace("_", "-"),
                        binary_property(source, parsed, name), name)
    return book


def book_identifier_status(version, sources):
    source = sources["security/IdentifierStatus.txt"]
    book = Book(version, "identifier-status",
                "Identifier_Status, from the file IdentifierStatus.txt"
                " of UTS #39.",
                [source], ["ranges"])
    parsed = parse_property_file(source)
    value = enumerated_property(source, parsed)
    if set(value) != {"Allowed", "Restricted"}:
        die("%s: the values are not Allowed and Restricted"
            % source.relpath)
    book.comment(
        "The code points whose Identifier_Status is Allowed.\n"
        "The other code points have the value Restricted,\n"
        "as the @missing line of the file says.")
    book.blank()
    book.range_list("identifier-status-allowed",
                    [v == "Allowed" for v in value],
                    "Identifier_Status=Allowed")
    return book


def book_identifier_type(version, sources):
    source = sources["security/IdentifierType.txt"]
    book = Book(version, "identifier-type",
                "Identifier_Type, from the file IdentifierType.txt"
                " of UTS #39.",
                [source], ["identifier-type-tables"],
                ["std/util/defconsts"])
    entries, missing = parse_property_file(source)
    if [fields for _, _, fields in missing] != [["Not_Character"]]:
        die("%s: the default is not Not_Character" % source.relpath)
    value = [("Not_Character",)] * NUM_CP
    listed = [False] * NUM_CP
    for lo, hi, fields in entries:
        if len(fields) != 1:
            die("%s: bad line at U+%04X" % (source.relpath, lo))
        types = tuple(fields[0].split())
        if not types or len(set(types)) != len(types):
            die("%s: bad set at U+%04X" % (source.relpath, lo))
        for t in types:
            if t not in IDENTIFIER_TYPES:
                die("%s: unknown type %r" % (source.relpath, t))
        for cp in range(lo, hi + 1):
            if listed[cp]:
                die("%s: U+%04X listed twice" % (source.relpath, cp))
            listed[cp] = True
            value[cp] = types
    runs = to_runs(value)
    count = {t: 0 for t in IDENTIFIER_TYPES}
    for lo, hi, types in runs:
        for t in types:
            count[t] += hi - lo + 1
    book.comment(
        "The Identifier_Type of every code point, as a list of runs:\n"
        "each run is a first code point, a last code point,\n"
        "and the set of types that all the code points from the first\n"
        "to the last have.\n"
        "A run is written as its two code points followed by the names"
        " of the types,\n"
        "in the order of the file;\n"
        "the macro identifier-type-run-table makes the list of runs.\n"
        "The runs are maximal and in order, and cover every code point.\n"
        "The code points that the file does not list have the one type\n"
        "Not_Character, as its @missing line says.\n"
        "%d runs.  Code points per type:" % len(runs))
    for t in IDENTIFIER_TYPES:
        book.comment("  %-17s %7d" % (t, count[t]))
    book.blank()
    const = book.run_table("identifier-type", "identifier-type-run-table",
                           "identifier-type-run-list-covers-p", runs,
                           lambda types: list(types))
    book.comment("The number of code points whose set has each type.")
    book.blank()
    for t in IDENTIFIER_TYPES:
        book.assert_range_list_size(
            ["(identifier-type-run-list-member-ranges",
             " (identifier-type-%s)" % t.lower().replace("_", "-"),
             " %s)" % const],
            count[t])
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
         book_derived_general_category,
         book_scripts,
         book_script_extensions,
         book_blocks,
         book_emoji_data,
         book_identifier_status,
         book_identifier_type,
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
        if base_url is None or relpath.startswith("security/"):
            url = canonical_url(version, relpath)
        else:
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
        fetch(version, args.ucd_dir, args.base_url)
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
