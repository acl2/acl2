#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Compare whole-file results: run_rustc.py --deep against rv-go-files.

usage: compare_files.py FILES.json RUSTC.json ACL2OUT.lsp

FILES.json comes from gen_files.py.  Prints the totals and, for each
file where the two sides disagree, its path, rustc's result, and where
the ACL2 lexer stopped (if it did).
"""
import collections, json, re, sys

ENTRY = re.compile(r'\("(file:\d+)"\s+(\d+|:UNBAL|\(:TOKERR\)|'
                   r'\(:LEXERR\s+(?:NIL|\([\d\s]*\))\s+(?:NIL|\([\d\s]*\))\))\)')


def decode(code_points):
    return ''.join(chr(int(x)) for x in re.findall(r'\d+', code_points))


def main():
    files = {t['id']: t for t in json.load(open(sys.argv[1], encoding='utf-8'))}
    rustc = json.load(open(sys.argv[2]))
    acl2 = dict(ENTRY.findall(open(sys.argv[3]).read()))
    totals, bad = collections.Counter(), []
    for tid, r in rustc.items():
        ours = acl2.get(tid)
        if ours is None:
            kind = 'missing from the ACL2 results'
        elif ours.isdigit():
            if not r['ok']:
                kind = 'rustc rejects, ACL2 accepts'
            else:
                kind = 'agree' if r['n'] == int(ours) else 'counts differ'
        else:
            kind = 'agree' if not r['ok'] else 'rustc accepts, ACL2 rejects'
        totals[kind] += 1
        if kind != 'agree':
            bad.append((kind, tid, r, ours))
    print(len(rustc), 'files')
    for kind, n in totals.most_common():
        print(f'{n:8d}  {kind}')
    for kind, tid, r, ours in bad:
        print(f"\n{kind}: {files[tid]['path']}")
        print('    rustc:', r['n'] if r['ok'] else r['errs'][:2])
        if ours and ours.startswith('(:LEXERR'):
            before, at = re.findall(r'NIL|\([\d\s]*\)', ours[8:])
            print(f'    ACL2 stops after {decode(before)!r} at {decode(at)!r}')
        else:
            print('    ACL2:', ours)


main()
