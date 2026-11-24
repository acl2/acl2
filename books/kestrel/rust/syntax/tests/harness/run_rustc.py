#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Run test inputs through rustc, inside a token-counting macro.

usage: run_rustc.py TESTS OUT [--edition 2021|2024] [--jobs N] [--deep]

TESTS is a JSON file holding a list of {"id": str, "text": str},
or a directory of such files; OUT is a JSON file, or a directory
(one result file per test file; files already there are skipped,
so an interrupted run can be resumed).

Each result is {"ok": bool, "n": int or null, "errs": [str]}:
"ok" says that rustc reported no error while lexing the input,
and "n" is then the number of token trees in it
(with --deep: the number of tokens, a delimited group counting as one
plus its contents).

The input is placed in the arguments of a macro that only counts its
argument tokens, so that just the errors of rustc's lexer fire:
later phases never see the tokens.  The count comes back through
the size mismatch of an array type.

The compiler is the one that `rustup which --toolchain TOOLCHAIN rustc`
names, unless the environment variable RUSTC gives a path.
"""
import argparse, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

TOOLCHAIN = '1.87.0'

ATTRS = ('#![recursion_limit = "1000000"]\n'
         '#![allow(unused, text_direction_codepoint_in_comment, '
         'text_direction_codepoint_in_literal)]\n')

# Counts the top-level token trees of its arguments.
TOP_HEAD = (ATTRS +
            'macro_rules! count { () => {0usize}; '
            '($h:tt $($t:tt)*) => {1usize + count!($($t)*)}; }\n'
            'pub const N: usize = count!(\n')

# Counts all the tokens, flattening delimited groups;
# the accumulator keeps the expansion flat for long inputs.
DEEP_HEAD = (ATTRS +
             'macro_rules! count {\n'
             ' (@ [$($acc:tt)*]) => { <[()]>::len(&[$($acc)*]) };\n'
             ' (@ [$($acc:tt)*] ( $($i:tt)* ) $($t:tt)*) =>'
             ' { count!(@ [$($acc)* (),] $($i)* $($t)*) };\n'
             ' (@ [$($acc:tt)*] [ $($i:tt)* ] $($t:tt)*) =>'
             ' { count!(@ [$($acc)* (),] $($i)* $($t)*) };\n'
             ' (@ [$($acc:tt)*] { $($i:tt)* } $($t:tt)*) =>'
             ' { count!(@ [$($acc)* (),] $($i)* $($t)*) };\n'
             ' (@ [$($acc:tt)*] $h:tt $($t:tt)*) =>'
             ' { count!(@ [$($acc)* (),] $($t)*) };\n'
             '}\n'
             'pub const N: usize = count!(@ []\n')

# The line feed before ");" ends a line comment at the end of the input.
TAIL = '\n);\nconst _: [(); N] = [(); 0];\n'

SIZE_RE = re.compile(r'expected an array with a size of (\d+), found one with a size of 0')


def find_rustc():
    if os.environ.get('RUSTC'):
        return os.environ['RUSTC']
    return subprocess.run(['rustup', 'which', '--toolchain', TOOLCHAIN, 'rustc'],
                          capture_output=True, text=True, check=True).stdout.strip()


def run_one(args):
    test, rustc, edition, deep, workdir = args
    d = tempfile.mkdtemp(dir=workdir)
    src = os.path.join(d, 't.rs')
    with open(src, 'w', encoding='utf-8', newline='') as f:
        f.write((DEEP_HEAD if deep else TOP_HEAD) + test['text'] + TAIL)
    p = subprocess.run([rustc, '--edition', edition, '--crate-type', 'lib',
                        '--emit=metadata', '--error-format=json', '--out-dir', d, src],
                       capture_output=True, text=True)
    errs, n = [], None
    for line in p.stderr.splitlines():
        if not line.startswith('{'):
            continue
        try:
            j = json.loads(line)
        except ValueError:
            continue
        if not j.get('level', '').startswith('error'):
            continue
        msg = j.get('message', '')
        if msg.startswith('aborting due to'):
            continue
        code = (j.get('code') or {}).get('code')
        m = SIZE_RE.search(line)
        if code == 'E0308' and m:  # the count, not an error of the input
            n = int(m.group(1))
            continue
        errs.append((code + ': ' if code else '') + msg)
    if p.returncode == 0 and not errs:
        n = 0  # no tokens: the two array sizes agree
    for fn in os.listdir(d):
        os.remove(os.path.join(d, fn))
    os.rmdir(d)
    return test['id'], {'ok': not errs, 'n': None if errs else n, 'errs': errs}


def run_file(tests_file, out_file, rustc, edition, deep, jobs):
    tests = json.load(open(tests_file, encoding='utf-8'))
    workdir = tempfile.mkdtemp(prefix='rustc-probe-')
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        res = dict(ex.map(run_one, [(t, rustc, edition, deep, workdir) for t in tests]))
    os.rmdir(workdir)
    json.dump(res, open(out_file, 'w', encoding='utf-8'), ensure_ascii=True, indent=0)
    print(f'{os.path.basename(tests_file)}: {len(res)} tests, edition {edition}, '
          f'{sum(r["ok"] for r in res.values())} accepted', flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('tests')
    ap.add_argument('out')
    ap.add_argument('--edition', default='2021', choices=['2021', '2024'])
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--deep', action='store_true')
    a = ap.parse_args()
    rustc = find_rustc()
    if os.path.isdir(a.tests):
        os.makedirs(a.out, exist_ok=True)
        for fn in sorted(os.listdir(a.tests)):
            if fn.endswith('.json') and not os.path.exists(os.path.join(a.out, fn)):
                run_file(os.path.join(a.tests, fn), os.path.join(a.out, fn),
                         rustc, a.edition, a.deep, a.jobs)
    else:
        run_file(a.tests, a.out, rustc, a.edition, a.deep, a.jobs)


main()
