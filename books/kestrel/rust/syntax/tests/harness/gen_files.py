#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Select real Rust source files for the whole-file check.

usage: gen_files.py OUT.json MAXFILES [ROOT]

Walks ROOT (default: the sources of the crates in the local cargo
registry, ~/.cargo/registry/src) and writes up to MAXFILES files of
300 to 12,000 bytes, spread evenly over the tree, as a list of
{"id": "file:<i>", "text": str, "path": str}.

Files that start with a byte order mark or a shebang line are skipped:
the probe of run_rustc.py puts the text in the middle of a file, where
rustc does not remove them.  Files with block doc comments are skipped
too, since the lexer does not cover those yet; delete SKIP when it does.

With a fourth argument, a regular expression, only files whose text
it matches are selected (e.g. to select files with float literals).
"""
import json, os, re, sys

SKIP = re.compile(r'/\*\*|/\*!')


def main():
    out, maxfiles = sys.argv[1], int(sys.argv[2])
    root = sys.argv[3] if len(sys.argv) > 3 else os.path.expanduser('~/.cargo/registry/src')
    only = re.compile(sys.argv[4]) if len(sys.argv) > 4 else None
    cands = []
    for d, _, files in os.walk(root):
        for fn in files:
            if fn.endswith('.rs'):
                p = os.path.join(d, fn)
                try:
                    size = os.path.getsize(p)
                except OSError:
                    continue
                if 300 <= size <= 12000:
                    cands.append(p)
    cands.sort()
    sel, skipped = [], 0
    # With a filter, look at every candidate and thin the matches afterwards.
    for p in cands[::1 if only else max(1, len(cands) // (maxfiles * 6))]:
        try:
            text = open(p, encoding='utf-8', newline='').read()
        except (OSError, UnicodeDecodeError):
            continue
        if text.startswith('\ufeff') or (text.startswith('#!') and not text.startswith('#![')):
            continue
        if SKIP.search(text):
            skipped += 1
            continue
        if only and not only.search(text):
            continue
        sel.append({'text': text, 'path': os.path.relpath(p, root)})
        if not only and len(sel) >= maxfiles:
            break
    if len(sel) > maxfiles:
        sel = [sel[i * len(sel) // maxfiles] for i in range(maxfiles)]
    sel = [dict(t, id='file:%d' % i) for i, t in enumerate(sel)]
    json.dump(sel, open(out, 'w', encoding='utf-8'), ensure_ascii=True)
    print(f'{len(cands)} candidates, {len(sel)} selected, {skipped} skipped for uncovered syntax, '
          f'{sum(len(t["text"]) for t in sel)} characters')


main()
