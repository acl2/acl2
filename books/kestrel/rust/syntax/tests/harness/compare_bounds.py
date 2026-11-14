#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Compare the token boundaries of the ACL2 lexer with those of the
Reference's interpreter.

usage: compare_bounds.py TESTSDIR REFDIR ACL2BOUNDS.lsp [--examples N]
                         [CATEGORY...]

REFDIR holds the results of the reference-driver; ACL2BOUNDS.lsp is
written by rust$::rv-go-bounds.  Compares, per test, whether both sides
accept the input and, if so, whether their tokens start and end at the
same places.  Prints the totals, then the disagreements grouped by kind
and known gap (as in compare.py), with a few examples each.
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
    ap.add_argument('ref_dir')
    ap.add_argument('acl2_bounds')
    ap.add_argument('--examples', type=int, default=6)
    ap.add_argument('categories', nargs='*')
    a = ap.parse_args()

    acl2 = {}
    # A rejected input is printed as a dotted pair: ("id" . :ERR).
    form = re.compile(r'\("([^"]+)"((?:\s+\(\d+ \. \d+\))*|\s+\.\s+:ERR|\s+\.\s+:UNBAL)\s*\)')
    for m in form.finditer(open(a.acl2_bounds).read()):
        body = m.group(2).strip(' .\n')
        acl2[m.group(1)] = (None if body in (':ERR', ':UNBAL') else
                            [[int(s), int(e)] for s, e in re.findall(r'\((\d+) \. (\d+)\)', body)])

    totals, groups = collections.Counter(), collections.defaultdict(list)
    for fn in sorted(os.listdir(a.ref_dir)):
        cat = fn[:-5]
        if not fn.endswith('.json') or (a.categories and cat not in a.categories):
            continue
        texts = {t['id']: t['text']
                 for t in json.load(open(os.path.join(a.tests_dir, fn), encoding='utf-8'))}
        for tid, r in json.load(open(os.path.join(a.ref_dir, fn))).items():
            if tid not in acl2:
                kind = 'missing from the ACL2 results'
            else:
                ours = acl2[tid]
                theirs = [t[:2] for t in r['toks']] if r['ok'] else None
                if ours is None and theirs is None:
                    kind = 'agree'
                elif ours is None:
                    kind = 'Reference accepts, ACL2 rejects'
                elif theirs is None:
                    kind = 'Reference rejects, ACL2 accepts'
                else:
                    kind = 'agree' if ours == theirs else 'boundaries differ'
            totals[kind] += 1
            if kind != 'agree':
                groups[(kind, ' '.join(known_gaps(texts[tid])) or '-')].append(
                    (tid, texts[tid], r['toks'], acl2.get(tid)))

    print(sum(totals.values()), 'tests')
    for kind, n in totals.most_common():
        print(f'{n:8d}  {kind}')
    untagged = 0
    for (kind, known), g in sorted(groups.items(), key=lambda kv: (kv[0][1] != '-', -len(kv[1]))):
        untagged += len(g) if known == '-' else 0
        print(f'\n{len(g)}  {kind}  [known gap: {known}]')
        for tid, text, toks, ours in g[:a.examples]:
            print(f'      {tid:16s} {text!r}\n          Reference: {toks}\n          ACL2:      {ours}')
    print(f'\n{sum(len(g) for g in groups.values())} disagreements, '
          f'{untagged} of them outside the known gaps')


main()
