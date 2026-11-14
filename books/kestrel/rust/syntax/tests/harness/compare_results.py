#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Compare two sets of results on the short inputs.

usage: compare_results.py TESTSDIR DIR_A DIR_B [--examples N] [CATEGORY...]

DIR_A and DIR_B hold result files as written by run_rustc.py or by the
reference-driver: for each category, a map from test id to
{"ok": bool, "n": int or null, "errs": [str], ...}.  Compares, per test,
whether both accept the input and, if so, whether the numbers of
top-level token trees agree.  Prints the totals, then the disagreements
grouped by kind and by the first message of each side, with a few
examples each.

Use it to compare two versions of rustc, or the Reference's interpreter
with rustc.
"""
import argparse, collections, json, os, re


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('tests_dir')
    ap.add_argument('dir_a')
    ap.add_argument('dir_b')
    ap.add_argument('--examples', type=int, default=6)
    ap.add_argument('categories', nargs='*')
    a = ap.parse_args()

    totals, groups = collections.Counter(), collections.defaultdict(list)
    for fn in sorted(os.listdir(a.dir_a)):
        cat = fn[:-5]
        if not fn.endswith('.json') or (a.categories and cat not in a.categories):
            continue
        if not os.path.exists(os.path.join(a.dir_b, fn)):
            print(f'{fn}: missing from {a.dir_b}')
            continue
        texts = {t['id']: t['text']
                 for t in json.load(open(os.path.join(a.tests_dir, fn), encoding='utf-8'))}
        ra = json.load(open(os.path.join(a.dir_a, fn)))
        rb = json.load(open(os.path.join(a.dir_b, fn)))
        for tid, x in ra.items():
            y = rb.get(tid)
            if y is None:
                kind = 'missing from B'
            elif x['ok'] and y['ok']:
                kind = 'agree' if x['n'] == y['n'] else 'counts differ'
            elif not x['ok'] and not y['ok']:
                kind = 'agree'
            else:
                kind = 'A accepts, B rejects' if x['ok'] else 'A rejects, B accepts'
            totals[kind] += 1
            if kind != 'agree':
                def msg(r):
                    if r is None:
                        return '-'
                    m = r['errs'][0] if r['errs'] else 'n=%s' % r['n']
                    return re.sub(r'`[^`]*`', '`..`', m)[:60]
                groups[(kind, msg(x), msg(y))].append((tid, texts[tid]))

    print(sum(totals.values()), 'tests;  A =', a.dir_a, ' B =', a.dir_b)
    for kind, n in totals.most_common():
        print(f'{n:8d}  {kind}')
    for (kind, ma, mb), g in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        print(f'\n{len(g)}  {kind}  [A: {ma}]  [B: {mb}]')
        for tid, text in g[:a.examples]:
            print(f'      {tid:16s} {text!r}')


main()
