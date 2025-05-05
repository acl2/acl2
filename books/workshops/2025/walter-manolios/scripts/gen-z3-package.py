#!/bin/env python3
# SPDX-FileCopyrightText: Copyright (c) 2025 Andrew T. Walter <me@atwalter.com>
# SPDX-License-Identifier: MIT

"""

This script will automatically generate a package file for the Z3 C API
types and function bindings that the Lisp-Z3 interface requires. To use
it, you must have the pyclibrary package installed, as well as the
headers for Z3's C API (you should have this if you have Z3 installed).

The Lisp-Z3 system expects the package file to exist at
`src/ffi/package.lisp`.

To use this script, you must provide the path to the z3.h header file.
The location of this file depends on your OS and how you installed Z3,
but here are a few options:

- If you installed Z3 using Homebrew, the path to the file should be
  the result of running `brew --prefix z3`, followed by `/include/z3.h`.

- If you installed Z3 using a Linux package manager, or by building from
  scratch, the file should be located at `/usr/include/z3.h` or
  `/usr/local/include/z3.h`.

Once you have the path to z3.h (denoted <z3-path> below), you can run
this script in the following way (assuming you're in the root directory
of this repo):

`python scripts/gen-z3-package.py <z3-path> -o <output-file>`

where <output-file> denotes a path to the output file that should be
created. Note that if <output-file> exists and you would like to
overwrite it, you will also need to pass the -f flag. For example, to
regenerate the `package.lisp` file that Lisp-Z3 expects, I run the
following:

`python scripts/gen-z3-package.py <z3-path> -o src/ffi/package.lisp -f`

"""

from pyclibrary import CParser
import sys
from pathlib import Path
import argparse
from itertools import chain
from util import find_z3_headers, get_typedef_enum, gather_enums, lispify_underscores

def output_z3_ctypes_package(opaque_names, enum_names, outfile):
    header = """
(defpackage #:z3-c-types
  (:documentation "Low-level Z3 types")
  (:use #:cffi)
  (:import-from #:cl #:in-package)
  (:export
"""
    outfile.write(header)
    for name in chain(opaque_names, enum_names):
        outfile.write(f'   #:{name}\n')
    outfile.write('))\n')

def output_z3_c_package(fn_names, outfile):
    header = """
(defpackage #:z3-c
  (:documentation "Bound low-level Z3 C API functions.")
  (:use #:cl #:cffi #:z3-c-types)
  (:export
"""
    outfile.write(header)
    for name in fn_names:
        outfile.write(f'   #:{lispify_underscores(name)}\n')
    outfile.write('))\n')

def gen_package_file(defs, fns_to_keep, outfile):
    # For whatever reason pyclibrary seems to categorize the opaque
    # pointer types as "variables"
    opaque_names = list(defs['variables'].keys())
    enum_names = list(gather_enums(defs).keys())
    fn_names = list(defs['functions'].keys())
    if fns_to_keep is not None:
        fn_names = list(filter(lambda x: x.name.lower() in fns_to_keep, fn_names))
    header = [';; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>',
              ';; SPDX-License-Identifier: MIT']
    for line in header:
        outfile.write(line)
        outfile.write('\n')
    output_z3_ctypes_package(opaque_names, enum_names, outfile)
    output_z3_c_package(fn_names, outfile)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Automatically generate a package file for the Z3 C API types and functions that were extracted from the Z3 C API headers.')
    parser.add_argument('header', type=Path, help='The z3.h header file to read from.')
    parser.add_argument('-o', '--output', type=Path, help='The file to write the generated grovel code to. Outputs to stdout if not provided.')
    parser.add_argument('-f', '--force', action='store_true', help='Force overwriting')
    parser.add_argument('--include-only', type=Path, help='Only output the functions whose names are listed (separated by newlines) in the file at the given path.')
    args = parser.parse_args()
    if args.output is not None and not args.force and args.output.exists():
        print('The output file already exists! If you would like to overwrite it, provide the -f argument. Exiting...')
        sys.exit(1)
    fns_to_keep = None
    if args.include_only is not None:
        if not args.include_only.exists():
            print('The given --include-only file does not exist! Exiting...')
            sys.exit(1)
        elif not args.include_only.is_file():
            print('The given --include-only file is a non-file object (e.g. a directory or another special kind of file)! Exiting...')
            sys.exit(1)
        else:
            fns_to_keep = parse_fns_to_keep(args.include_only)
    headers = find_z3_headers(args.header)
    if len(headers) == 0:
        print('Was unable to find the rest of the Z3 header files given the contents of the main header file. Exiting...')
        sys.exit(1)
    parser = CParser(headers)
    if args.output is None:
        gen_package_file(parser.defs, fns_to_keep, sys.stdout)
    else:
        with open(args.output, 'w') as f:
            gen_package_file(parser.defs, fns_to_keep, f)
