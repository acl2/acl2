#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Test the input layer on whole files, against rustc.

usage: input_format.py hand [--toolchain T]...
       input_format.py gen DIR
       input_format.py rustc DIR [--toolchain T] [--edition E] [--jobs N]
       input_format.py compare DIR RUSTC.json ACL2.lsp [--examples N]

The input layer is what comes before lexing: UTF-8 decoding, the byte
order mark, CR LF, and the shebang.  These apply to a file as a whole,
so a test here is the bytes of a whole file (run_rustc.py puts its
inputs in the middle of a file).

hand runs the hand-written cases below through rustc and checks that
each one compiles, or fails with the expected first error.  They show
what rustc does case by case, including for the files of modules and
of include!, and where two versions of rustc differ.

gen writes the generated tests: DIR/cases.json, a list of
{"id": str, "probe": str, "nolf": bool, "hex": str} with the bytes of
each file in hexadecimal, and DIR/cases.lsp, with the same bytes as a
list ("id" b1 b2 ...) for rust$::rv-go-input of the ACL2 driver.

rustc compiles each generated file as a library and writes
DIR/rustc-T-E.json: for each id, the errors as [code, line, message].

compare compares rustc's results with those of the ACL2 driver:

- The class of each file: not valid UTF-8; an error of the lexer;
  an error about delimiters, with its kind; or none of these.
  rustc reports the errors of its lexer before those of its parser,
  so a file is in the last class when no error of rustc's is one of
  the lexer's (see LEX), whatever its parser says.

- Whether the file starts with a shebang, for the files that are
  probes.  After "#!" and the text under test, a "kept" probe has an
  inner attribute and a function on the same line, and a call of the
  function on the next line: if it compiles, the line was not
  removed, so there is no shebang; if the function is not found, the
  line was removed.  A "removed" probe has the opening of a string
  that is never closed: if it compiles, the line was removed, so
  there is a shebang; if rustc reports the string, and no line feed
  comes before it, there is none.  Any other outcome says nothing.

The compiler is the one that `rustup which --toolchain T rustc` names.
"""
import argparse, collections, itertools, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

BOM = chr(0xfeff)
F ='pub fn f(){}'


def b(x):
    return x if isinstance(x, bytes) else x.encode('utf-8')


def find_rustc(toolchain):
    return subprocess.run(['rustup', 'which', '--toolchain', toolchain, 'rustc'],
                          capture_output=True, text=True, check=True).stdout.strip()


# ----------------------------------------------------------------------
# Hand-written cases.
# Each is (name, files, expected): files maps file names to contents
# (the root is root.rs); expected is 'ok' or a part of the first error
# line that rustc prints with --error-format=short, or a dictionary
# from toolchains to these when toolchains differ.

HAND = []


def case(name, root, expected, **others):
    files = {'root.rs': root}
    for k, v in others.items():
        files[k.replace('_', '.', 1)] = v
    HAND.append((name, files, expected))


UTF8 = 'did not contain valid UTF-8'
STR = 'unterminated double quote string'
NO_F = 'cannot find function `f`'

# UTF-8.  Every file that is read as source must be valid UTF-8.
case('U1-ff-in-comment', b'// \xff\n' + b(F), UTF8)
case('U2-overlong', b'// \xc0\xaf\n' + b(F), UTF8)
case('U3-surrogate', b'// \xed\xa0\x80\n' + b(F), UTF8)
case('U4-above-10ffff', b'// \xf4\x90\x80\x80\n' + b(F), UTF8)
case('U5-truncated-at-eof', b(F) + b'// \xe2\x82', UTF8)
case('U6-valid-4-byte', b'// \xf0\x9f\x98\x80\n' + b(F), 'ok')
case('U7-noncharacter-fffe', b'// \xef\xbf\xbe\n' + b(F), 'ok')
case('U8-nul-in-comment', b'// \x00\n' + b(F), 'ok')
case('U9-mod-invalid', 'mod m;', UTF8, m_rs=b'// \xff\n' + b(F))
case('U10-include-invalid', 'include!("i.rs");', UTF8, i_rs=b'// \xff\n' + b(F))
case('U11-include_str-invalid', 'pub const S: &str = include_str!("s.txt");',
     "wasn't a utf-8 file", s_txt=b'a\xffb')
case('U12-include_bytes-invalid',
     'pub const S: &[u8] = include_bytes!("s.txt");'
     ' const _: () = assert!(S.len() == 3);', 'ok', s_txt=b'a\xffb')
case('U13-5-byte-form', b'// \xf8\x88\x80\x80\x80\n' + b(F), UTF8)
case('U14-lone-continuation', b'// \x80\n' + b(F), UTF8)
case('U15-overlong-3-byte', b'// \xe0\x80\x80\n' + b(F), UTF8)
case('U16-max-10ffff', b'// \xf4\x8f\xbf\xbf\n' + b(F), 'ok')
case('U17-nul-outside', b'\x00' + b(F), 'unknown start of token: \\u{0}')

# Byte order mark: one is removed, at the start of a source file.
NOT_TOKEN = 'unknown start of token: \\u{feff}'
case('B1-bom', BOM + F, 'ok')
case('B2-bom-bom', BOM + BOM + F, NOT_TOKEN)
case('B3-bom-at-end', F + BOM, NOT_TOKEN)
case('B4-bom-shebang', BOM + '#!/x "\n' + F, 'ok')
case('B5-mod-bom', 'mod m;', 'ok', m_rs=BOM + F)
case('B6-include-bom', 'include!("i.rs");', 'ok', i_rs=BOM + F)
case('B7-include_str-bom-kept',
     'pub const S: &str = include_str!("s.txt");'
     ' const _: () = assert!(S.len() == 4);', 'ok', s_txt=BOM + 'a')
case('B8-bom-only', BOM, 'ok')
case('B9-bom-in-string', 'pub const S: &str = "' + BOM + '";'
     ' const _: () = assert!(S.len() == 3);', 'ok')
case('B10-space-bom', ' ' + BOM + F, NOT_TOKEN)
case('B11-bom-in-comment', '// ' + BOM + '\n' + F, 'ok')
case('B12-bom-then-string-with-bom', BOM + 'pub const S: &str = "' + BOM + '";', 'ok')
case('B13-include-expr-bom', 'pub const X: i32 = include!("e.rs");', 'ok', e_rs=BOM + '1')
case('B14-bom-crlf', BOM + '\r\n' + F, 'ok')

# CR LF becomes LF, once; any other CR stays.
case('C1-crlf-at-end', F + '\r\n', 'ok')
case('C2-cr-as-whitespace', 'pub\rfn f(){}', 'ok')
case('C3-doc-crlf', '/// a\r\n' + F, 'ok')
case('C4-doc-cr-crlf', '/// a\r\r\n' + F, 'bare CR not allowed in doc-comment')
case('C5-string-crlf-len3', 'const _: () = assert!("a\r\nb".len() == 3);', 'ok')
case('C6-raw-string-crlf-len3', 'const _: () = assert!(r"a\r\nb".len() == 3);', 'ok')
case('C7-string-bare-cr', 'pub const S: &str = "a\rb";', 'bare CR not allowed in string')
case('C8-string-cr-crlf', 'pub const S: &str = "a\r\r\nb";', 'bare CR not allowed in string')
case('C9-continuation-crlf', 'const _: () = assert!("a\\\r\n   b".len() == 2);', 'ok')
case('C10-byte-string-crlf-len3', 'const _: () = assert!(b"a\r\nb".len() == 3);', 'ok')
case('C11-comment-cr-crlf', '// c\r\r\n' + F, 'ok')
case('C12-include_str-crlf-kept',
     'pub const S: &str = include_str!("s.txt");'
     ' const _: () = assert!(S.len() == 4);', 'ok', s_txt='a\r\nb')
case('C13-include-crlf-len3', 'const _: () = assert!(include!("e.rs").len() == 3);',
     'ok', e_rs='"a\r\nb"')
case('C14-block-doc-crlf', '/** a\r\n b */' + F, 'ok')
case('C15-block-doc-cr', '/** a\r b */' + F, 'bare CR not allowed in block doc-comment')
case('C16-cr-cr-lf-whitespace', 'pub\r\r\nfn f(){}', 'ok')
case('C17-raw-string-cr-crlf', 'pub const S: &str = r"a\r\r\nb";',
     'bare CR not allowed in raw string')
case('C18-cr-cr-lf-lf-string', 'pub const S: &str = "a\r\r\n\nb";',
     'bare CR not allowed in string')
case('C19-lf-cr', 'pub\n\rfn f(){}', 'ok')
case('C20-crlf-in-c-string', 'const _: () = assert!(c"a\r\nb".count_bytes() == 3);', 'ok')
case('C21-raw-string-crlf-in-mod', 'mod m;', 'ok',
     m_rs='const _: () = assert!(r"a\r\nb".len() == 3);')
case('C22-crlf-ends-line-comment', '// c\r\n' + F + '// d\r\n', 'ok')
case('C23-continuation-cr-crlf', 'pub const S: &str = "a\\\r\r\n   b";',
     'unknown character escape: `\\r`')

# Shebang: what may come between "#!" and "[" in an inner attribute.
# For each text X there are the two probes described above.
# 'trivia': X is whitespace and comments that are not doc comments,
# so there is no shebang.  'shebang': X is something else on one line.
# 'doc-line': X is a line doc comment and a line feed; the shebang is
# removed and the "[" that starts the next line is an error there.
XS = [
    ('empty', '', 'trivia'), ('space', ' ', 'trivia'), ('tab', '\t', 'trivia'),
    ('lf', '\n', 'trivia'), ('cr', '\r', 'trivia'), ('crlf', '\r\n', 'trivia'),
    ('vt', '\x0b', 'trivia'), ('ff', '\x0c', 'trivia'), ('u0085', '\x85', 'trivia'),
    ('u200e', chr(0x200e), 'trivia'), ('u200f', chr(0x200f), 'trivia'),
    ('u2028', chr(0x2028), 'trivia'), ('u2029', chr(0x2029), 'trivia'),
    ('u00a0', '\xa0', 'shebang'), ('bom', BOM, 'shebang'),
    ('block', '/* c */', 'trivia'), ('block-empty', '/**/', 'trivia'),
    ('block-3', '/***/', 'trivia'), ('block-3-stars', '/*** c */', 'trivia'),
    ('block-nested', '/* a /* b */ c */', 'trivia'),
    ('block-2-lines', '/* a\n b */', 'trivia'),
    ('block-outer-doc', '/** d */', 'shebang'), ('block-inner-doc', '/*! d */', 'shebang'),
    ('line', '// c\n', 'trivia'), ('line-empty', '//\n', 'trivia'),
    ('line-4-slashes', '//// c\n', 'trivia'),
    ('line-outer-doc', '/// d\n', 'doc-line'), ('line-inner-doc', '//! d\n', 'doc-line'),
    ('line-3-slashes-only', '///\n', 'doc-line'), ('line-bang-only', '//!\n', 'doc-line'),
    ('mixed', ' /* c */ // x\n /* d */ ', 'trivia'),
    ('slash', '/', 'shebang'), ('a', 'a', 'shebang'), ('bang', '!', 'shebang'),
    ('hash', '#', 'shebang'),
    ('block-doc-then-block', '/** d *//* c */', 'shebang'),
    ('block-then-block-doc', '/* c *//** d */', 'shebang'),
]
for nm, x, tag in XS:
    case('S-removed-' + nm, '#!' + x + '[allow(unused)] "\n' + F,
         {'trivia': STR, 'shebang': 'ok', 'doc-line': 'root.rs:2:17: error[E0765]'}[tag])
    case('S-kept-' + nm, '#!' + x + '[allow(unused)] pub fn f(){}\npub fn g(){ f() }',
         {'trivia': 'ok', 'shebang': NO_F,
          'doc-line': 'root.rs:2:1: error: expected item, found `[`'}[tag])

# Shebang: where it starts and ends.
case('S1-shebang', '#!/usr/bin/env rustx "\n' + F, 'ok')
case('S2-shebang-only', '#!', 'ok')
case('S3-shebang-lf', '#!\n' + F, 'ok')
case('S4-leading-space', ' #!/x "\n' + F, 'root.rs:1:7: error[E0765]')
case('S5-leading-lf', '\n#!/x "\n' + F, 'root.rs:2:6: error[E0765]')
case('S6-two-shebangs', '#!/a "\n#!/b "\n' + F, 'root.rs:2:6: error[E0765]')
case('S7-shebang-crlf', '#!/x "\r\n' + F, 'ok')
case('S8-shebang-cr-only', '#!/x "\r' + F + '\npub fn g(){ f() }', NO_F)
case('S9-unterminated-block', '#!/* unterminated\n' + F, 'ok')
case('S10-unterminated-block-doc', '#!/** unterminated\n' + F, 'ok')
case('S11-unterminated-inner-doc', '#!/*! unterminated\n' + F, 'ok')
case('S12-block-2-lines-no-bracket', '#!/* a\n b */ ' + F, 'root.rs:2:4: error: expected one of')
case('S13-doc-line-then-bracket', '#!/// d\n[allow(unused)]\n' + F,
     'root.rs:2:1: error: expected item, found `[`')
case('S14-4-slashes-then-bracket', '#!//// d\n[allow(unused)]\n' + F, 'ok')
case('S15-slash-star-slash', '#!/*/ "\n' + F, 'ok')
case('S16-bracket-garbage', '#![ "\n' + F, 'root.rs:1:5: error[E0765]')
case('S17-hash-bang-no-lf', '#!/x "', 'ok')
case('S18-shebang-cr-crlf', '#!/x "\r\r\n' + F, 'ok')
case('S19-shebang-then-attribute', '#!/x "\n#![allow(unused)]\n' + F, 'ok')
case('S20-attr-then-shebang', '#![allow(unused)]\n#!/x "\n' + F, 'root.rs:2:6: error[E0765]')
case('S21-outer-doc-at-eof', '#!/**', 'ok')
case('S22-attribute-on-line-4', '#!\n\n\n[allow(unused)]\n' + F, 'ok')
case('S23-block-then-eof', '#!/* c */', 'ok')

# Shebang: in which files.  rustc 1.87.0 skips it in every source
# file; rustc 1.100.0 does not skip it in a file that include! reads
# as an expression or as statements.
SH = '#!/x "\n'
case('W1-mod-file', 'mod m;', 'ok', m_rs=SH + F)
case('W2-include-item', 'include!("i.rs");', 'ok', i_rs=SH + F)
case('W3-include-expr', 'pub fn f() -> i32 { include!("e.rs") }',
     {'1.87.0': 'ok', '1.100.0': 'e.rs:1:6: error[E0765]'}, e_rs=SH + '1')
case('W4-include-stmt', 'pub fn f() { include!("s.rs"); }',
     {'1.87.0': 's.rs:2:1: error: expected expression', '1.100.0': 's.rs:1:6: error[E0765]'},
     s_rs=SH + 'let _x = 1;')
case('W5-path-mod', '#[path = "p.rs"] mod p;', 'ok', p_rs=SH + F)
case('W6-mod-bom-shebang', 'mod m;', 'ok', m_rs=BOM + SH + F)
case('W7-include-in-fn-item', 'pub fn f() { include!("s.rs"); g() }',
     {'1.87.0': 's.rs:2:1: error: expected expression', '1.100.0': 's.rs:1:6: error[E0765]'},
     s_rs=SH + 'fn g(){}')
case('W8-include-const-expr', 'pub const X: i32 = include!("e.rs");',
     {'1.87.0': 'ok', '1.100.0': 'e.rs:1:6: error[E0765]'}, e_rs=SH + '1')
case('W9-include-in-mod-item', 'mod a { include!("i.rs"); }', 'ok', i_rs=SH + F)

# Frontmatter: rustc 1.100.0 lexes it at the start of a file, and
# rejects it as unstable; in rustc 1.87.0 the dashes are tokens.
DASHES = {'1.87.0': 'expected item, found `-`', '1.100.0': 'frontmatters are experimental'}
case('F1-frontmatter', '---\n[dependencies]\n---\n' + F, DASHES)
case('F2-shebang-frontmatter', '#!/x\n---\na\n---\n' + F, DASHES)
case('F3-include-expr-dashes',
     'pub const X: i32 = include!("e.rs"); const _: () = assert!(X == -6);',
     'ok', e_rs='---\n1\n---\n5')
case('F4-mod-dashes', 'mod m;', DASHES, m_rs='---\n[d]\n---\n' + F)
case('F5-include-item-dashes', 'include!("i.rs");', DASHES, i_rs='---\n[d]\n---\n' + F)
case('F6-dashes-not-at-start',
     'pub const X: i32 =\n---\n1\n---\n5; const _: () = assert!(X == -6);', 'ok')
case('F7-blank-line-then-dashes', '\n---\n[d]\n---\n' + F, DASHES)
case('F8-bom-dashes', BOM + '---\n[d]\n---\n' + F, DASHES)


def run_hand(toolchains):
    bad = 0
    for tc in toolchains:
        rustc, n = find_rustc(tc), 0
        for name, files, expected in HAND:
            if isinstance(expected, dict):
                if tc not in expected:
                    continue
                expected = expected[tc]
            with tempfile.TemporaryDirectory() as d:
                for fn, content in files.items():
                    with open(os.path.join(d, fn), 'wb') as f:
                        f.write(b(content))
                p = subprocess.run([rustc, '--edition', '2021', '--crate-type', 'lib',
                                    '--emit=metadata', '--error-format=short',
                                    '--color=never', '--out-dir', d, 'root.rs'],
                                   cwd=d, capture_output=True)
            errs = [ln for ln in p.stderr.decode('utf-8', 'replace').split('\n')
                    if 'error' in ln]
            got = 'ok' if p.returncode == 0 else (errs[0] if errs else '(no error line)')
            n += 1
            if (got == 'ok') != (expected == 'ok') or expected not in got:
                bad += 1
                print(f'{tc} {name}: expected {expected!r}, got {got!r}')
        print(f'rustc {tc}: {n} cases')
    print('all as expected' if not bad else f'{bad} NOT as expected')
    return 1 if bad else 0


# ----------------------------------------------------------------------
# Generated tests.

def words(alphabet, lo, hi):
    for n in range(lo, hi + 1):
        for t in itertools.product(alphabet, repeat=n):
            yield ''.join(t)


# What may come between "#!" and "[": whitespace and comments that are
# not doc comments ...
TRIVIA = [' ', '\t', '\n', '\r', '\r\n', '\x0b', '\x0c', '\x85',
          chr(0x200e), chr(0x200f), chr(0x2028), chr(0x2029),
          '/* c */', '/**/', '/***/', '/*** c */',
          '/* a /* b */ c */', '/* a\n b */', '// c\n', '//\n', '//// c\n']
# ... and what may not.  (No "#" and no "]": the probes rely on that.)
OTHER = ['/** d */', '/*! d */', '/// d\n', '//! d\n', '///\n', '//!\n', '/', 'a', '!',
         '*', '\xa0', BOM, '"x"', '(', '/*', '/**', '/*!', '[']
CORE = [' ', '\n', '\r\n', '/* c */', '/**/', '// c\n', '/** d */', '/// d\n', '/', 'a',
        '/*', '[']
PREFIXES = [BOM, BOM + BOM, ' ', '\n', '\r', '\r\n', BOM + '\n', BOM + ' ']
BYTES = [0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2, 0xdf,
         0xe0, 0xe1, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xff]


def kept(prefix, x):
    return prefix + '#!' + x + '[allow(unused)] pub fn f(){}\npub fn g(){ f() }'


def removed(prefix, x):
    return prefix + '#!' + x + '[allow(unused)] "\n' + F


def generate():
    """Yield (category, probe, nolf, bytes)."""
    # Shebang probes: all texts of up to two pieces, and of three
    # pieces of a smaller set.
    xs = list(words(TRIVIA + OTHER, 0, 2)) + list(words(CORE, 3, 3))
    for x in dict.fromkeys(xs):
        yield 'shebang', 'kept', '\n' not in x, b(kept('', x))
        yield 'shebang', 'removed', '\n' not in x, b(removed('', x))
    # The same probes after something else: only a byte order mark
    # leaves the "#!" at the start.
    for p in PREFIXES:
        for x in [''] + TRIVIA + OTHER:
            nolf = '\n' not in p + x
            yield 'prefix', 'kept', nolf, b(kept(p, x))
            yield 'prefix', 'removed', nolf, b(removed(p, x))
    # Short texts after "#!", for the class of the file alone.
    for w in words([' ', '\n', '\r', '/', '*', '!', '[', '"', 'a'], 0, 4):
        yield 'words', '', False, b('#!' + w)
    # Byte sequences in a comment, for UTF-8.
    seqs = [bytes(t) for n in (1, 2, 3) for t in itertools.product(BYTES, repeat=n)]
    seqs += [bytes(t) for t in itertools.product(
        [0xf0, 0xf1, 0xf3, 0xf4, 0xf5], [0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf],
        [0x80, 0xbf, 0x41], [0x80, 0xbf, 0x41])]
    for s in seqs:
        yield 'utf8', '', False, b'// ' + s + b'\n' + b(F)


def run_gen(d):
    os.makedirs(d, exist_ok=True)
    cases, counts = [], collections.Counter()
    for cat, probe, nolf, data in generate():
        cases.append({'id': f'{cat}:{counts[cat]}', 'probe': probe, 'nolf': nolf,
                      'hex': data.hex()})
        counts[cat] += 1
    json.dump(cases, open(os.path.join(d, 'cases.json'), 'w'), indent=0)
    with open(os.path.join(d, 'cases.lsp'), 'w') as f:
        f.write('(\n')
        for c in cases:
            f.write('("%s" %s)\n' % (c['id'], ' '.join(str(x) for x in bytes.fromhex(c['hex']))))
        f.write(')\n')
    for cat, n in counts.items():
        print(f'{cat:10s} {n:6d}')
    print(f'{"total":10s} {len(cases):6d}')


def rustc_one(args):
    c, rustc, edition, workdir = args
    d = tempfile.mkdtemp(dir=workdir)
    src = os.path.join(d, 't.rs')
    with open(src, 'wb') as f:
        f.write(bytes.fromhex(c['hex']))
    p = subprocess.run([rustc, '--edition', edition, '--crate-type', 'lib',
                        '--emit=metadata', '--error-format=json', '--out-dir', d, src],
                       capture_output=True)
    errs = []
    # Not splitlines: it also splits at characters that a message can quote.
    for line in p.stderr.decode('utf-8', 'replace').split('\n'):
        if not line.startswith('{'):
            continue
        try:
            j = json.loads(line)
        except ValueError:
            continue
        msg = j.get('message', '').replace(d + os.sep, '')  # a message can name the file
        if not j.get('level', '').startswith('error') or msg.startswith('aborting due to'):
            continue
        lines = [s['line_start'] for s in j.get('spans', []) if s.get('is_primary')]
        errs.append([(j.get('code') or {}).get('code') or '', lines[0] if lines else 0, msg])
    if p.returncode != 0 and not errs:
        errs.append(['', 0, 'rustc failed without an error message'])
    for fn in os.listdir(d):
        os.remove(os.path.join(d, fn))
    os.rmdir(d)
    return c['id'], errs


def run_rustc(d, toolchain, edition, jobs):
    cases = json.load(open(os.path.join(d, 'cases.json')))
    rustc = find_rustc(toolchain)
    workdir = tempfile.mkdtemp(prefix='rustc-input-')
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        res = dict(ex.map(rustc_one, [(c, rustc, edition, workdir) for c in cases]))
    os.rmdir(workdir)
    out = os.path.join(d, f'rustc-{toolchain}-{edition}.json')
    json.dump(res, open(out, 'w'), ensure_ascii=True, indent=0)
    print(f'{len(res)} files, {sum(not e for e in res.values())} compile; wrote {out}')


# The beginnings of the messages of rustc's lexer.
LEX = ('unknown start of token', 'unterminated', 'bare CR not allowed',
       'unknown character escape', 'unknown byte escape', 'empty character literal',
       'character literal may only contain one codepoint',
       'character constant must be escaped', 'byte constant must be escaped',
       'prefix `', 'invalid ', 'numeric character escape', 'incorrect unicode escape',
       'out of range hex escape', 'found invalid character', 'reserved ')
DELIM = (('mismatched closing delimiter', ':MISMATCHED'),
         ('this file contains an unclosed delimiter', ':UNCLOSED'),
         ('unexpected closing delimiter', ':UNEXPECTED'))


def rustc_class(errs):
    msgs = [e[2] for e in errs]
    if any('did not contain valid UTF-8' in m for m in msgs):
        return ':UTF8'
    if any(m.startswith(LEX) for m in msgs):
        return ':ERR'
    for m in msgs:
        for p, k in DELIM:
            if m.startswith(p):
                return k
    return ':OK'


def rustc_shebang(c, errs):
    """True, False, or None if rustc's result does not tell."""
    first = errs[0] if errs else None
    if c['probe'] == 'kept':
        if not errs:
            return False
        if first[0] == 'E0425' and 'function `f`' in first[2]:
            return True
    if c['probe'] == 'removed':
        if not errs:
            return True
        if first[0] == 'E0765' and c['nolf']:
            return False
    return None


def run_compare(d, rustc_file, acl2_file, examples):
    cases = json.load(open(os.path.join(d, 'cases.json')))
    rustc = json.load(open(rustc_file))
    acl2 = {m.group(1): (m.group(2), int(m.group(3))) for m in
            re.finditer(r'\("([^"]+)"\s+(:[A-Z0-9-]+)\s+(\d+)\)', open(acl2_file).read())}
    classes, shebangs, later = collections.Counter(), collections.Counter(), collections.Counter()
    theirs_all, rows = collections.Counter(), []
    for c in cases:
        errs = rustc[c['id']]
        text = bytes.fromhex(c['hex']).decode('utf-8', 'replace')
        if c['id'] not in acl2:
            classes['missing from the ACL2 results'] += 1
            continue
        ours, n = acl2[c['id']]
        theirs = rustc_class(errs)
        theirs_all[theirs] += 1
        classes['agree' if ours == theirs else 'DISAGREE'] += 1
        if ours != theirs:
            rows.append(('class', c['id'], text, f'rustc {theirs}, ACL2 {ours}', errs[:1]))
        if theirs == ':OK' and errs:
            later[re.sub(r'`[^`]*`', '`..`', errs[0][2])] += 1
        if c['probe']:
            s = rustc_shebang(c, errs)
            if s is None:
                shebangs['rustc does not tell'] += 1
            elif s == (n > 0):
                shebangs['agree: shebang' if s else 'agree: no shebang'] += 1
            else:
                shebangs['DISAGREE'] += 1
                rows.append(('shebang', c['id'], text,
                             f'rustc {"shebang" if s else "no shebang"}, ACL2 length {n}',
                             errs[:1]))
    print(len(cases), 'files')
    print('class of the file:')
    for k, n in classes.most_common():
        print(f'{n:8d}  {k}')
    print("rustc's classes:")
    for k, n in theirs_all.most_common():
        print(f'{n:8d}  {k}')
    print('shebang, on the probes:')
    for k, n in shebangs.most_common():
        print(f'{n:8d}  {k}')
    print("rustc's first error where no error is the lexer's (check that none is):")
    for k, n in later.most_common():
        print(f'{n:8d}  {k}')
    for row in rows[:examples]:
        print('DISAGREE', *[repr(x) for x in row])
    print(f'{len(rows)} disagreements')
    return 1 if rows else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('hand')
    p.add_argument('--toolchain', action='append')
    p = sub.add_parser('gen')
    p.add_argument('dir')
    p = sub.add_parser('rustc')
    p.add_argument('dir')
    p.add_argument('--toolchain', default='1.87.0')
    p.add_argument('--edition', default='2021', choices=['2021', '2024'])
    p.add_argument('--jobs', type=int, default=8)
    p = sub.add_parser('compare')
    p.add_argument('dir')
    p.add_argument('rustc_file')
    p.add_argument('acl2_file')
    p.add_argument('--examples', type=int, default=20)
    a = ap.parse_args()
    if a.cmd == 'hand':
        return run_hand(a.toolchain or ['1.87.0'])
    if a.cmd == 'gen':
        return run_gen(a.dir)
    if a.cmd == 'rustc':
        return run_rustc(a.dir, a.toolchain, a.edition, a.jobs)
    return run_compare(a.dir, a.rustc_file, a.acl2_file, a.examples)


sys.exit(main())
