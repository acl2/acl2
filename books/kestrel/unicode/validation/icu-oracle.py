#!/usr/bin/env python3
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Write what the ICU library says about every code point, in the format of
dump.lisp, for comparison with the ACL2 library.

Usage:

    icu-oracle.py VERSION ICU-LIB-DIR > FILE

VERSION, e.g. 16.0.0, must be the version of Unicode of the ICU library
(u_getUnicodeVersion); the script stops if it is not.  ICU 76 has Unicode
16.0.0, ICU 78 has Unicode 17.0.0 and ICU 79 has Unicode 18.0.0.

ICU-LIB-DIR is the directory with the shared libraries of one version of
ICU4C: libicudata, libicuuc and libicui18n.  The script icu/build-icu.sh
builds them from the source of a release of ICU.

The output has a header line and one line for each code point.  Each
column is named `property@icu`, where the property is a column of
dump.lisp, with the same format, except that:

  * blk is the name of the Block as ICU gives it, in the form of
    PropertyValueAliases.txt (Latin_1_Supplement) and not in that of
    Blocks.txt (Latin-1 Supplement);

  * idty has the names of the types in the order of their names;

  * correction is the alias of the name of the code point whose type is
    `correction`, which is the only kind of alias that u_charName gives,
    or empty if there is none.

compare.py compares these three columns accordingly.

Where the columns come from:

    xids, xidc, pws, bidic, fce, di, vs, jc, nchar, dep, pcm, psyn, ids,
    idc, emoji, epres, emod, ebase, ecomp, extpict, ri, wspace
            the set of the code points that have the binary property
            (u_getBinaryPropertySet)
    ccc, gc, sc, bc, bidif, blk, idst
            the value of the property (u_getIntPropertyValue), and for
            all but ccc and idst its name (u_getPropertyValueName)
    scx     uscript_getScriptExtensions
    idty    u_getIDTypes
    dd      u_charDigitValue
    dm      Decomposition_Type (u_getIntPropertyValue) and the mapping
            that unorm2_getRawDecomposition gives for NFKC
    nfd, nfc, nfkd, nfkc
            unorm2_normalize, on the code point alone
    skel, skelm
            uspoof_getSkeleton, which decomposes, removes the default
            ignorable code points, replaces by prototypes and decomposes
            again, as the internal skeleton of UTS #39 does
    name, correction
            u_charName.  Where it gives no name for a code point whose
            General_Category, by ICU, is not Cc, Cs, Co or Cn, the field
            is `!`, which means "cannot say": such a code point has a
            name [Unicode, Section 4.8], and ICU does not say what it
            is.  The script reports how many there are.  ICU 79.1 gives
            no name for the Jurchen characters and the small seal
            characters of Unicode 18.0.0.

A string is given to ICU in UTF-16.  A surrogate code point is given as
the one code unit that it is.
"""

import ctypes
import pathlib
import re
import sys

NUM_CP = 0x110000

# The columns for binary properties, with the names of the properties.
BINARY = [
    ("xids", "XID_Start"), ("xidc", "XID_Continue"),
    ("pws", "Pattern_White_Space"), ("bidic", "Bidi_Control"),
    ("fce", "Full_Composition_Exclusion"),
    ("di", "Default_Ignorable_Code_Point"), ("vs", "Variation_Selector"),
    ("jc", "Join_Control"), ("nchar", "Noncharacter_Code_Point"),
    ("dep", "Deprecated"), ("pcm", "Prepended_Concatenation_Mark"),
    ("psyn", "Pattern_Syntax"), ("ids", "ID_Start"), ("idc", "ID_Continue"),
    ("emoji", "Emoji"), ("epres", "Emoji_Presentation"),
    ("emod", "Emoji_Modifier"), ("ebase", "Emoji_Modifier_Base"),
    ("ecomp", "Emoji_Component"), ("extpict", "Extended_Pictographic"),
    ("ri", "Regional_Indicator"), ("wspace", "White_Space"),
]

COLUMNS = ["xids", "xidc", "pws", "bidic", "bidif", "ccc", "fce", "dm",
           "nfd", "nfc", "nfkd", "nfkc", "gc", "di", "vs", "jc", "nchar",
           "dep", "pcm", "psyn", "ids", "idc", "sc", "scx", "bc", "blk",
           "dd", "emoji", "epres", "emod", "ebase", "ecomp", "extpict",
           "ri", "idst", "idty", "skel", "skelm", "wspace", "name",
           "correction"]

EXPLICIT_FORMATTING = {"LRE", "RLE", "LRO", "RLO", "PDF",
                       "LRI", "RLI", "FSI", "PDI"}

# Values of ICU enumerations.
U_SHORT_PROPERTY_NAME, U_LONG_PROPERTY_NAME = 0, 1
U_UNICODE_CHAR_NAME, U_CHAR_NAME_ALIAS = 0, 3
U_DT_NONE, U_DT_CANONICAL = 0, 1
U_BUFFER_OVERFLOW_ERROR = 15


def die(message):
    sys.exit("icu-oracle.py: error: " + message)


def load_icu(lib_dir):
    """Load the three libraries of ICU from LIB_DIR, and return a function
    that gives the ICU function of a name."""
    lib_dir = pathlib.Path(lib_dir)
    major = None
    for path in sorted(lib_dir.glob("libicuuc*")):
        match = (re.fullmatch(r"libicuuc\.so\.(\d+)", path.name)
                 or re.fullmatch(r"libicuuc\.(\d+)\.dylib", path.name))
        if match:
            major = match.group(1)
            pattern = path.name.replace("icuuc", "%s")
    if major is None:
        die("no libicuuc.so.N or libicuuc.N.dylib in %s" % lib_dir)
    # The data first: the other two need it, and icui18n needs icuuc.
    libraries = [ctypes.CDLL(str(lib_dir / (pattern % name)),
                             mode=ctypes.RTLD_GLOBAL)
                 for name in ("icudata", "icuuc", "icui18n")]

    def function(name, restype, argtypes):
        # The functions of ICU have the version of ICU in their names,
        # unless the library was built without that.
        for library in libraries[1:]:
            for suffix in ("_" + major, ""):
                try:
                    fn = getattr(library, name + suffix)
                except AttributeError:
                    continue
                fn.restype = restype
                fn.argtypes = argtypes
                return fn
        die("no function %s in the ICU libraries" % name)
    return function


def utf16(cps):
    """The UTF-16 code units of a list of code points; a surrogate code
    point is the one code unit that it is."""
    units = []
    for cp in cps:
        if cp >= 0x10000:
            units.append(0xD800 + ((cp - 0x10000) >> 10))
            units.append(0xDC00 + ((cp - 0x10000) & 0x3FF))
        else:
            units.append(cp)
    return units


def from_utf16(units, length):
    """The code points of the first LENGTH code units of a buffer."""
    cps = []
    i = 0
    while i < length:
        unit = units[i]
        i += 1
        if (0xD800 <= unit < 0xDC00 and i < length
                and 0xDC00 <= units[i] < 0xE000):
            unit = 0x10000 + ((unit - 0xD800) << 10) + (units[i] - 0xDC00)
            i += 1
        cps.append(unit)
    return cps


def seq(cps):
    return " ".join(str(cp) for cp in cps)


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    version = sys.argv[1]
    function = load_icu(sys.argv[2])
    c_int, c_int32, c_void_p = ctypes.c_int, ctypes.c_int32, ctypes.c_void_p
    error_p = ctypes.POINTER(c_int)
    error_name = function("u_errorName", ctypes.c_char_p, [c_int])
    error = c_int(0)

    def check(what):
        # Warnings are negative.
        if error.value > 0:
            die("%s: %s" % (what, error_name(error.value).decode()))

    versions = (ctypes.c_uint8 * 4)()
    function("u_getUnicodeVersion", None, [c_void_p])(versions)
    unicode_version = "%d.%d.%d" % tuple(versions[:3])
    function("u_getVersion", None, [c_void_p])(versions)
    icu_version = "%d.%d" % tuple(versions[:2])
    if unicode_version != version:
        die("ICU %s has Unicode %s, not %s"
            % (icu_version, unicode_version, version))
    print("icu-oracle.py: ICU %s has Unicode %s"
          % (icu_version, unicode_version), file=sys.stderr)

    get_property_enum = function("u_getPropertyEnum", c_int,
                                 [ctypes.c_char_p])

    def property_enum(name):
        value = get_property_enum(name.encode())
        if value < 0:
            die("ICU does not have the property %s" % name)
        return value

    # The binary properties: a byte for each code point.
    get_set = function("u_getBinaryPropertySet", c_void_p, [c_int, error_p])
    range_count = function("uset_getRangeCount", c_int32, [c_void_p])
    get_item = function("uset_getItem", c_int32,
                        [c_void_p, c_int32, ctypes.POINTER(c_int32),
                         ctypes.POINTER(c_int32), c_void_p, c_int32,
                         error_p])
    binary = {}
    start, end = c_int32(0), c_int32(0)
    for column, name in BINARY:
        uset = get_set(property_enum(name), ctypes.byref(error))
        check(name)
        flags = bytearray(NUM_CP)
        # The ranges are the first items of a set.
        for i in range(range_count(uset)):
            get_item(uset, i, ctypes.byref(start), ctypes.byref(end),
                     None, 0, ctypes.byref(error))
            check("uset_getItem")
            flags[start.value:end.value + 1] = (
                b"\x01" * (end.value + 1 - start.value))
        binary[column] = flags

    # The properties with a value.
    get_int = function("u_getIntPropertyValue", c_int32, [c_int32, c_int])
    get_value_name = function("u_getPropertyValueName", ctypes.c_char_p,
                              [c_int, c_int32, c_int])
    names = {}

    def value_name(prop, value, choice):
        key = (prop, value, choice)
        if key not in names:
            name = get_value_name(prop, value, choice)
            if name is None:
                die("ICU has no name for the value %d of the property %d"
                    % (value, prop))
            names[key] = name.decode()
        return names[key]

    ccc_prop = property_enum("Canonical_Combining_Class")
    gc_prop = property_enum("General_Category")
    sc_prop = property_enum("Script")
    bc_prop = property_enum("Bidi_Class")
    blk_prop = property_enum("Block")
    dt_prop = property_enum("Decomposition_Type")
    idst_prop = property_enum("Identifier_Status")
    idty_prop = property_enum("Identifier_Type")
    digit_value = function("u_charDigitValue", c_int32, [c_int32])

    codes = (c_int * 64)()
    get_scx = function("uscript_getScriptExtensions", c_int32,
                       [c_int32, c_void_p, c_int32, error_p])
    get_id_types = function("u_getIDTypes", c_int32,
                            [c_int32, c_void_p, c_int32, error_p])

    # Normalization.
    normalizers = [
        function("unorm2_get%sInstance" % form, c_void_p, [error_p])(
            ctypes.byref(error))
        for form in ("NFD", "NFC", "NFKD", "NFKC")]
    check("unorm2_getNFDInstance and the like")
    nfkc = normalizers[3]
    normalize = function("unorm2_normalize", c_int32,
                         [c_void_p, c_void_p, c_int32, c_void_p, c_int32,
                          error_p])
    raw_decomposition = function("unorm2_getRawDecomposition", c_int32,
                                 [c_void_p, c_int32, c_void_p, c_int32,
                                  error_p])
    capacity = 256
    source = (ctypes.c_uint16 * 8)()
    dest = (ctypes.c_uint16 * capacity)()

    def put(cps):
        units = utf16(cps)
        source[:len(units)] = units
        return len(units)

    # The skeleton.
    checker = function("uspoof_open", c_void_p, [error_p])(
        ctypes.byref(error))
    check("uspoof_open")
    get_skeleton = function("uspoof_getSkeleton", c_int32,
                            [c_void_p, ctypes.c_uint32, c_void_p, c_int32,
                             c_void_p, c_int32, error_p])

    def skeleton(cps):
        length = get_skeleton(checker, 0, source, put(cps), dest, capacity,
                              ctypes.byref(error))
        check("uspoof_getSkeleton")
        return seq(from_utf16(dest, length))

    # The names.
    char_name = function("u_charName", c_int32,
                         [c_int32, c_int, ctypes.c_char_p, c_int32, error_p])
    name_buffer = ctypes.create_string_buffer(256)

    def name_of(cp, choice):
        char_name(cp, choice, name_buffer, 256, ctypes.byref(error))
        check("u_charName")
        return name_buffer.value.decode()

    out = sys.stdout
    out.write("#cp;" + ";".join(c + "@icu" for c in COLUMNS) + "\n")
    nameless = []
    for cp in range(NUM_CP):
        row = {column: str(flags[cp]) for column, flags in binary.items()}
        row["ccc"] = str(get_int(cp, ccc_prop))
        row["gc"] = value_name(gc_prop, get_int(cp, gc_prop),
                               U_SHORT_PROPERTY_NAME)
        row["sc"] = value_name(sc_prop, get_int(cp, sc_prop),
                               U_SHORT_PROPERTY_NAME)
        row["bc"] = value_name(bc_prop, get_int(cp, bc_prop),
                               U_SHORT_PROPERTY_NAME)
        row["bidif"] = row["bc"] if row["bc"] in EXPLICIT_FORMATTING else "-"
        row["blk"] = value_name(blk_prop, get_int(cp, blk_prop),
                                U_LONG_PROPERTY_NAME)
        status = value_name(idst_prop, get_int(cp, idst_prop),
                            U_LONG_PROPERTY_NAME)
        if status not in ("Allowed", "Restricted"):
            die("Identifier_Status of U+%04X is %s" % (cp, status))
        row["idst"] = "1" if status == "Allowed" else "0"

        count = get_scx(cp, codes, 64, ctypes.byref(error))
        check("uscript_getScriptExtensions")
        row["scx"] = " ".join(sorted(
            value_name(sc_prop, codes[i], U_SHORT_PROPERTY_NAME)
            for i in range(count)))
        count = get_id_types(cp, codes, 64, ctypes.byref(error))
        check("u_getIDTypes")
        row["idty"] = " ".join(sorted(
            value_name(idty_prop, codes[i], U_LONG_PROPERTY_NAME)
            for i in range(count)))

        digit = digit_value(cp)
        row["dd"] = str(digit) if digit >= 0 else "-"

        kind = get_int(cp, dt_prop)
        if kind == U_DT_NONE:
            row["dm"] = "-"
        else:
            length = raw_decomposition(nfkc, cp, dest, capacity,
                                       ctypes.byref(error))
            check("unorm2_getRawDecomposition")
            if length < 0:
                die("U+%04X has a Decomposition_Type and no mapping" % cp)
            row["dm"] = (("c:" if kind == U_DT_CANONICAL else "k:")
                         + seq(from_utf16(dest, length)))

        length = put([cp])
        for form, normalizer in zip(("nfd", "nfc", "nfkd", "nfkc"),
                                    normalizers):
            result = normalize(normalizer, source, length, dest, capacity,
                               ctypes.byref(error))
            check("unorm2_normalize")
            row[form] = seq(from_utf16(dest, result))

        row["skel"] = skeleton([cp])
        row["skelm"] = skeleton([0x61, cp, 0x301, 0x327])
        row["name"] = name_of(cp, U_UNICODE_CHAR_NAME)
        if not row["name"] and row["gc"] not in ("Cc", "Cs", "Co", "Cn"):
            row["name"] = "!"
            nameless.append(cp)
        row["correction"] = name_of(cp, U_CHAR_NAME_ALIAS)
        out.write("%d;%s\n" % (cp, ";".join(row[c] for c in COLUMNS)))
    if nameless:
        print("icu-oracle.py: u_charName gives no name for %d code points"
              " that have one, from U+%04X to U+%04X"
              % (len(nameless), nameless[0], nameless[-1]), file=sys.stderr)


if __name__ == "__main__":
    main()
