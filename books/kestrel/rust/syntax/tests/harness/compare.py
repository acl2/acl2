#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Compare the results of run_rustc.py with those of the ACL2 driver.

usage: compare.py TESTSDIR RUSTCDIR ACL2OUT.lsp [--out FILE] [--examples N]
                  [CATEGORY...]

Compares, per test, whether both sides accept the input and, if so,
whether the numbers of top-level token trees agree.  Prints the totals,
then the disagreements grouped by kind, known gap, and rustc's message,
with a few examples each; --out also writes all of them as JSON.

A disagreement is tagged as a known gap when the input contains
something the lexer does not cover yet (see known_gaps below);
remove a tag once its gap is closed.  The tags are heuristics on the
input text, so read the examples of a tagged group before trusting it.
"""
import argparse, collections, json, os, re


def known_gaps(text):
    tags = []
    if '/**' in text or '/*!' in text:
        tags.append('block-doc')
    if '\r' in text and ('///' in text or '//!' in text):
        tags.append('doc-cr')
    if any(ord(ch) > 127 for ch in text):
        tags.append('non-ascii')
    return tags


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('tests_dir')
    ap.add_argument('rustc_dir')
    ap.add_argument('acl2_out')
    ap.add_argument('--out')
    ap.add_argument('--examples', type=int, default=6)
    ap.add_argument('categories', nargs='*')
    a = ap.parse_args()

    acl2 = {}
    for m in re.finditer(r'\("([^"]+)"\s+(:ERR|:UNBAL|\d+)\)', open(a.acl2_out).read()):
        acl2[m.group(1)] = m.group(2)

    totals, rows = collections.Counter(), []
    for fn in sorted(os.listdir(a.rustc_dir)):
        cat = fn[:-5]
        if not fn.endswith('.json') or (a.categories and cat not in a.categories):
            continue
        texts = {t['id']: t['text']
                 for t in json.load(open(os.path.join(a.tests_dir, fn), encoding='utf-8'))}
        for tid, r in json.load(open(os.path.join(a.rustc_dir, fn))).items():
            ours = acl2.get(tid)
            if ours is None:
                kind = 'missing from the ACL2 results'
            elif ours == ':UNBAL':  # rustc rejects these while building token trees
                kind = 'agree' if not r['ok'] else 'rustc accepts, ACL2 has unbalanced delimiters'
            elif ours == ':ERR':
                kind = 'agree' if not r['ok'] else 'rustc accepts, ACL2 rejects'
            elif not r['ok']:
                kind = 'rustc rejects, ACL2 accepts'
            else:
                kind = 'agree' if r['n'] == int(ours) else 'counts differ'
            totals[kind] += 1
            if kind != 'agree':
                rows.append({'cat': cat, 'kind': kind, 'known': known_gaps(texts[tid]),
                             'id': tid, 'text': texts[tid], 'rustc': r, 'acl2': ours})

    print(sum(totals.values()), 'tests')
    for kind, n in totals.most_common():
        print(f'{n:8d}  {kind}')

    groups = collections.defaultdict(list)
    for row in rows:
        r = row['rustc']
        msg = r['errs'][0] if r['errs'] else 'n=%s' % r['n']
        msg = re.sub(r'`[^`]*`', '`..`', msg)
        groups[(row['kind'], ' '.join(row['known']) or '-', msg)].append(row)
    for (kind, known, msg), g in sorted(groups.items(), key=lambda kv: (kv[0][1] != '-', -len(kv[1]))):
        print(f'\n{len(g)}  {kind}  [known gap: {known}]  [rustc: {msg}]')
        for row in g[:a.examples]:
            print(f"      {row['id']:16s} {row['text']!r}  ACL2: {row['acl2']}")

    untagged = sum(1 for row in rows if not row['known'])
    print(f'\n{len(rows)} disagreements, {untagged} of them outside the known gaps')
    if a.out:
        json.dump(rows, open(a.out, 'w'), ensure_ascii=True, indent=0)


main()
