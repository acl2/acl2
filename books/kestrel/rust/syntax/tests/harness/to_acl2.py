#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Convert test files to one file of code-point lists for the ACL2 driver.

usage: to_acl2.py OUT.lsp TESTS...

Each TESTS is a JSON file holding a list of {"id": str, "text": str},
or a directory of such files.  OUT.lsp holds a single ACL2 object:
a list with one entry ("id" cp1 cp2 ...) per test.

Two adjustments mirror what rustc sees in the probe of run_rustc.py:
a line feed is appended (the probe puts one after the input),
and each CR LF pair becomes LF (rustc normalizes these when it reads
a file; in our front end this is the job of the input layer,
which precedes lexing).
"""
import json, os, sys


def test_files(paths):
    for p in paths:
        if os.path.isdir(p):
            for fn in sorted(os.listdir(p)):
                if fn.endswith('.json'):
                    yield os.path.join(p, fn)
        else:
            yield p


def main():
    out, n = sys.argv[1], 0
    with open(out, 'w') as f:
        f.write('(\n')
        for fn in test_files(sys.argv[2:]):
            for t in json.load(open(fn, encoding='utf-8')):
                text = (t['text'] + '\n').replace('\r\n', '\n')
                f.write('("%s" %s)\n' % (t['id'], ' '.join(str(ord(ch)) for ch in text)))
                n += 1
        f.write(')\n')
    print(n, 'tests written to', out)


main()
