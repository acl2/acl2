#!/usr/bin/env python3
# Unicode Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Write how the ICU library displays random short strings, as test cases
for the function bidi-display of the ACL2 library.

Usage:

    icu-display.py SEED COUNT MAX-LENGTH [kept] > FILE

SEED is the seed of the random numbers, COUNT the number of strings, and
MAX-LENGTH the greatest length of a string.  With `kept`, the strings have
none of the characters that rule X9 of the Unicode Bidirectional Algorithm
removes.

This needs the shared library of ICU (libicuuc), with any version of
Unicode: the strings are made of characters whose properties are the same
in the versions of Unicode since 6.3 (see ALPHABET).  The version of
Unicode of the library is written to the standard error.  If the
environment variable ICU_LIB_DIR is set, the library is taken from that
directory, as icu-oracle.py takes it; otherwise it is the one that the
system has.

For each string and for a direction of the paragraph (left to right, right
to left, or that of the first strong character), ICU is asked for

  - the text as it is displayed, by ubidi_writeReordered with the options
    UBIDI_KEEP_BASE_COMBINING and UBIDI_DO_MIRRORING, which are rules L3
    and L4;
  - the levels, by ubidi_getLevels.

The output is one Lisp object, a list of cases

    (DIRECTION (CODE-POINT ...) (DISPLAYED-CODE-POINT ...) (LEVEL ...))

where DIRECTION is :ltr, :rtl or :fs.  The function compare-display of the
book compare-display reads it.  See the section "Validation" of
../README.md.
"""

import ctypes
import ctypes.util
import os
import pathlib
import random
import re
import sys

# Characters of the classes that the algorithm tells apart: letters and
# digits of both directions, separators, brackets and other mirrored
# characters, two combining marks, and the formatting characters.
ALPHABET = [
    0x61, 0x62,                   # L
    0x31, 0x32,                   # EN
    0x20,                         # WS
    0x28, 0x29, 0x5B, 0x5D,       # ON, paired brackets
    0x3C, 0x3E, 0xAB,             # ON, mirrored, not brackets
    0x21,                         # ON
    0x2C, 0x2B, 0x24,             # CS, ES, ET
    0x09,                         # S
    0x5D0, 0x5D1,                 # R
    0x627,                        # AL
    0x661,                        # AN
    0x301, 0x5B0,                 # NSM
    0x202A, 0x202B, 0x202C, 0x202D, 0x202E,   # LRE RLE PDF LRO RLO
    0x2066, 0x2067, 0x2068, 0x2069,           # LRI RLI FSI PDI
    0x200E, 0x200F,               # L and R: the two marks
    0x200D,                       # BN
]

# The characters of ALPHABET that rule X9 removes.
REMOVED = (0x202A, 0x202B, 0x202C, 0x202D, 0x202E, 0x200D)

UBIDI_KEEP_BASE_COMBINING = 1
UBIDI_DO_MIRRORING = 2
UBIDI_DEFAULT_LTR = 0xFE
DIRECTIONS = [(0, ':ltr'), (1, ':rtl'), (UBIDI_DEFAULT_LTR, ':fs')]


def load_icu():
    """Return a function that gives the ICU function of a name."""
    lib_dir = os.environ.get('ICU_LIB_DIR')
    if lib_dir:
        names = [path.name for path in pathlib.Path(lib_dir).glob('libicuuc*')
                 if re.fullmatch(r'libicuuc\.so\.\d+', path.name)]
        if not names:
            sys.exit('icu-display.py: no libicuuc.so.N in ' + lib_dir)
        name = os.path.join(lib_dir, names[0])
        # icuuc needs the data library.
        ctypes.CDLL(name.replace('icuuc', 'icudata'), mode=ctypes.RTLD_GLOBAL)
    else:
        name = ctypes.util.find_library('icuuc')
        if name is None:
            sys.exit('icu-display.py: the ICU library (icuuc) was not found')
    library = ctypes.CDLL(name)
    # The functions of ICU have the version of ICU in their names,
    # unless the library was built without that.
    match = re.search(r'\.so\.(\d+)', name)
    suffixes = ['_' + match.group(1)] if match else []
    suffixes.append('')

    def function(name, restype, argtypes):
        for suffix in suffixes:
            try:
                fn = getattr(library, name + suffix)
            except AttributeError:
                continue
            fn.restype = restype
            fn.argtypes = argtypes
            return fn
        sys.exit('icu-display.py: no function %s in the ICU library' % name)
    return function


def main():
    if len(sys.argv) not in (4, 5) or sys.argv[4:] not in ([], ['kept']):
        sys.exit(__doc__)
    seed, count, max_length = (int(arg) for arg in sys.argv[1:4])
    alphabet = ALPHABET
    if sys.argv[4:] == ['kept']:
        alphabet = [cp for cp in ALPHABET if cp not in REMOVED]

    function = load_icu()
    error_p = ctypes.POINTER(ctypes.c_int)
    get_unicode_version = function('u_getUnicodeVersion', None,
                                   [ctypes.c_void_p])
    ubidi_open = function('ubidi_open', ctypes.c_void_p, [])
    ubidi_close = function('ubidi_close', None, [ctypes.c_void_p])
    ubidi_set_para = function(
        'ubidi_setPara', None,
        [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int32, ctypes.c_uint8,
         ctypes.c_void_p, error_p])
    ubidi_write_reordered = function(
        'ubidi_writeReordered', ctypes.c_int32,
        [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int32, ctypes.c_uint16,
         error_p])
    ubidi_get_levels = function('ubidi_getLevels',
                                ctypes.POINTER(ctypes.c_uint8),
                                [ctypes.c_void_p, error_p])

    version = (ctypes.c_uint8 * 4)()
    get_unicode_version(version)
    print('icu-display.py: the ICU library has Unicode %d.%d.%d'
          % tuple(version[:3]), file=sys.stderr)

    def display(cps, paragraph_level):
        # every character of ALPHABET is one UTF-16 code unit
        length = len(cps)
        source = (ctypes.c_uint16 * (length + 1))(*cps, 0)
        destination = (ctypes.c_uint16 * (length + 1))()
        error = ctypes.c_int(0)
        bidi = ubidi_open()
        ubidi_set_para(bidi, source, length, paragraph_level, None,
                       ctypes.byref(error))
        written = ubidi_write_reordered(
            bidi, destination, length + 1,
            UBIDI_KEEP_BASE_COMBINING | UBIDI_DO_MIRRORING,
            ctypes.byref(error))
        levels = ubidi_get_levels(bidi, ctypes.byref(error))
        if error.value > 0:
            sys.exit('icu-display.py: ICU error %d' % error.value)
        result = list(destination[:written]), [levels[i]
                                               for i in range(length)]
        ubidi_close(bidi)
        return result

    generator = random.Random(seed)
    print('(')
    for _ in range(count):
        length = generator.randint(1, max_length)
        cps = [generator.choice(alphabet) for _ in range(length)]
        paragraph_level, direction = generator.choice(DIRECTIONS)
        displayed, levels = display(cps, paragraph_level)
        print('(%s (%s) (%s) (%s))'
              % (direction,
                 ' '.join(str(cp) for cp in cps),
                 ' '.join(str(cp) for cp in displayed),
                 ' '.join(str(level) for level in levels)))
    print(')')


if __name__ == '__main__':
    main()
