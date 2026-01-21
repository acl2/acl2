#!/bin/env python3
# SPDX-FileCopyrightText: Copyright (c) 2025 Andrew T. Walter <me@atwalter.com>
# SPDX-License-Identifier: MIT

"""

This script will automatically generate an binding file for the
functions exposed by the Z3 C API. This is required to make the
functions accessible to Lisp-Z3. To use this script, you must have the
pyclibrary package installed, as well as the headers for Z3's C API
(you should have this if you have Z3 installed).

The Lisp-Z3 system expects the binding file to exist at
`src/ffi/z3-api.lisp`.

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

`python scripts/gen-z3-api.py <z3-path> -o <output-file>`

where <output-file> denotes a path to the output file that should be
created. Note that if <output-file> exists and you would like to
overwrite it, you will also need to pass the -f flag. For example, to
regenerate the `z3-api.lisp` file that Lisp-Z3 expects, I run the
following:

`python scripts/gen-z3-api.py <z3-path> -o src/ffi/z3-api.lisp -f`

One reason why one might want to regenerate the `z3-api.lisp` file is
to make available additional functions that are not included in the
`z3-api.lisp` file that ships with Lisp-Z3. The set of functions that
we include bindings for is intentionally minimized in an attempt to
provide support for as wide a range of Z3 versions as possible.

"""

import sys
import copy
from pathlib import Path
import argparse
import re
from collections import namedtuple
from pyclibrary import CParser
from itertools import chain
from util import find_z3_headers, lispify_underscores, parse_fns_to_keep

type_mapping = {
    "void": ":void",
    "int": ":int",
    "signed": ":int",
    "unsigned": ":uint",
    "bool": ":bool",
    "string": ":string",
    "int64_t": ":int64",
    "uint64_t": ":uint64",
    "float": ":float",
    "double": ":double",
    "void_ptr": ":pointer",
    "Z3_bool": ":bool",
    "Z3_char_ptr": ":pointer",
    "Z3_string_ptr": ":pointer",
    "Z3_string": ":string",
    "Z3_error_handler": ":pointer",
}

def c_type_to_lisp(ty):
    if len(ty.declarators) > 0:
        return ":pointer"
    if ty.type_spec in type_mapping:
        return type_mapping[ty.type_spec]
    if ty.type_spec.startswith("Z3_") and (ty.type_spec.endswith("_eh") or ty.type_spec.endswith("_fptr")):
        return ":pointer"
    return 'z3-c-types::'+ty.type_spec

def find_fresh_param_name(base, param_names):
    names = set(param_names)
    fresh_name = base
    ctr = 1
    while fresh_name in names:
        fresh_name = base + str(ctr)
        ctr = ctr + 1
    return fresh_name

def list_replace(l, old, new_fn):
    return [new_fn() if x == old else x for x in l]

def fix_t(param_names):
    '''Replace any parameter names of `t` with something else.
    Common Lisp doesn't allow the use of `t` as a variable name.
    '''
    # t is usually used for an AST argument
    return list_replace(param_names, "t", lambda: find_fresh_param_name("ast", param_names))

def process_brief(brief):
    r'''Process supported markup in the text of a brief.
    Right now, this is only \c, which indicates the next word should be
    rendered as code and \ccode which does the same but for a block of
    text.
    In both cases, we'll just surround the argument with grave accents,
    Markdown-style.
    '''
    processed_c = re.sub(r'\\c ([^\r\n\t\f\v .]+)', lambda x: f'`{x.group(1)}`', brief)
    processed_ccode = re.sub(r'\\ccode\{([^}]+)\}', lambda x: f'`{x.group(1)}`', processed_c)
    processed_pound_ref = re.sub(r'#(\w+)', lambda x: f'`{x.group(1)}`', processed_ccode)
    return processed_pound_ref

FunctionSpec = namedtuple("FunctionSpec", ["name", "ret", "args", "brief"])

def fix_none_names(in_names):
    names = copy.copy(in_names)
    for idx, name in enumerate(names):
        if name is None:
            names[idx] = find_fresh_param_name("x", names)
    return names

def process_fn(name, spec, briefs):
    return_ty = spec[0]
    params = spec[1]
    param_names = list(map(lambda x: x[0], params))
    param_tys = list(map(lambda x: x[1], params))
    # Hack to detect void argument lists
    if len(params) == 1 and params[0][0] is None and params[0][1].type_spec == "void":
        param_names = []
        param_tys = []
    else:
        param_names = fix_none_names(param_names)
        param_names = fix_t(list(map(lispify_underscores, param_names)))
    args = list(zip(param_names, param_tys))
    if name in briefs:
        brief = briefs[name]
    else:
        brief = ""
    processed_brief = process_brief(brief)
    return FunctionSpec(name=name, ret=return_ty, args=args, brief=processed_brief)

def get_api_fns(headers, parser):
    briefs = {}
    for header in headers:
        with open(header, 'r') as f:
            briefs.update(get_fn_briefs(f))
    return [process_fn(name, spec, briefs) for (name, spec) in parser.defs['functions'].items()]

def get_fn_briefs(f):
    # This really should be written as a proper parser, but I
    # don't have the bandwidth to do so right now.
    # This ignores the "long description" for each function, which
    # we probably want to include at some point.
    # Also ignoring the section header comments (e.g. `@name Goals`)
    in_comment = False
    in_brief = False
    brief = []
    briefs = {}
    for line in f:
        sline = line.strip()
        if sline.endswith("*/"):
            in_comment = False
            in_brief = False
            brief = []
        elif sline.startswith("/*"):
            in_comment = True
        elif in_comment:
            if sline.startswith("\\brief"):
                in_brief = True
                brief.append(sline.removeprefix("\\brief").strip())
            elif in_brief and len(sline) > 0:
                brief.append(sline)
            elif in_brief:
                in_brief = False
            elif sline.startswith("def_API("):
                name = sline.removeprefix("def_API(").split(",", maxsplit=1)[0].strip().strip('\'')
                briefs[name] = ' '.join(brief)
            elif sline.startswith("extra_API("):
                name = sline.removeprefix("extra_API(").split(",", maxsplit=1)[0].strip().strip('\'')
                briefs[name] = ' '.join(brief)
    return briefs

def write_fn_to_lisp_file(f, fn, is_extra=False):
    macro_name = "defcfun"
    if is_extra:
        macro_name = "defcfun?"
    brief = fn.brief.replace('"', r'\"')
    args = '\n  '.join(map(lambda arg: f'({arg[0]} {c_type_to_lisp(arg[1])})', fn.args))
    f.write(f'''\n({macro_name} "{fn.name}" {c_type_to_lisp(fn.ret)}
  "{brief}"
  {args})
''')

lisp_file_header = ''';; THIS FILE IS AUTOGENERATED
;; See scripts/gen_z3_api.py for more information
(in-package :z3-c)

(defmacro defcfun? (name &rest args)
  "A version of defcfun that first checks whether the foreign function
exists, and warns if it does not."
  `(if (not (cffi:foreign-symbol-pointer ,name))
       (warn "Couldn't find function with name ~S, skipping..." ,name)
     (defcfun ,name ,@args)))
'''

def gen_lisp_file(f, api_fns):
    f.write(lisp_file_header)
    for api_fn in api_fns:
        write_fn_to_lisp_file(f, api_fn)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Automatically generate a file that contains function bindings for Z3 API functions.')
    parser.add_argument('header', type=Path, help='The z3.h header file to read from.')
    parser.add_argument('-o', '--output', type=Path, help='The file to write the generated function bindings to. Outputs to stdout if not provided.')
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
    api_fns = get_api_fns(headers, parser)
    if args.include_only is not None:
        # Limit to functions that should be included
        api_fns = list(filter(lambda x: x.name.lower() in fns_to_keep, api_fns))
    if args.output is None:
        gen_lisp_file(sys.stdout, api_fns)
    else:
        with open(args.output, 'w') as f:
            gen_lisp_file(f, api_fns)
