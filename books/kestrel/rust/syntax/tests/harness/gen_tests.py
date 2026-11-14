#!/usr/bin/env python3
# Rust Library
#
# Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Eric McCarthy (bendyarm on GitHub)

"""Generate the short inputs of the lexer differential tests.

usage: gen_tests.py OUTDIR

Writes OUTDIR/<category>.json, each a list of {"id": "<category>:<i>",
"text": str}.  Most categories enumerate all the strings up to some
length over a small alphabet chosen to exercise one area of the lexical
grammar; the others combine hand-picked pieces.

The ids index the cached rustc results, so changing a category
invalidates its results: prefer adding a new category.
"""
import itertools, json, os, sys


def words(alphabet, lo, hi):
    for n in range(lo, hi + 1):
        for t in itertools.product(alphabet, repeat=n):
            yield ''.join(t)


cats = {}

# Quotes, hashes, underscores, and literal prefixes:
# reserved prefixes, lifetimes against character literals, raw forms.
cats['quote4'] = list(words(["'", '"', '#', '_', 'r', 'b', 'c', 'a', '1', ' '], 1, 4))
cats['quote5'] = list(words(["'", '"', '#', '_', 'r', 'a', '1'], 5, 5))

# Integer literals and their reserved forms
# (no '.', 'e', or 'E', which belong to float literals).
cats['int4'] = list(words(['0', '1', '2', '8', 'b', 'o', 'x', '_', 'a', 'g', 'u'], 1, 4))

# Bodies and escapes of character and string literals, in every kind of literal.
KINDS = [("'", "'"), ("b'", "'"), ('"', '"'), ('b"', '"'), ('c"', '"'),
         ('r"', '"'), ('br"', '"'), ('cr"', '"'), ('r#"', '"#')]
QKINDS = KINDS[:5]
W = ['\\', 'x', 'u', '{', '}', '0', '7', '8', 'F', 'n', 'r', 't', "'", '"', '_', 'a',
     '\xe9', '\n', '\r', '\t', '\0', '/', ' ']
cats['body2'] = [o + b + c for b in words(W, 0, 2) for (o, c) in KINDS]
HX = ['0', '7', '8', 'F', 'f', 'g', '_', '"', "'"]
cats['hexesc'] = [o + '\\x' + b + t + c for b in words(HX, 0, 2) for t in ['', 'a']
                  for (o, c) in QKINDS]
UB = [''.join(t) for n in range(0, 5) for t in itertools.product(['0', 'D', '_', 'g'], repeat=n)]
UB += ['D7FF', 'D800', 'DFFF', 'E000', '10FFFF', '110000', '0000000', '000000', '00_00_00',
       '1_0_F_F_F_F', '10FFFF_', '_10FFFF', 'FFFFFF', 'ffffff', '10ffff', '1F600', '7F', '80',
       'FF', '100', '0_', '0__', '1234567', '12345_6', '1_2_3_4_5_6_', '00000000', 'd800', 'dfff']
cats['uniesc'] = [o + '\\u{' + b + '}' + c for b in UB for (o, c) in QKINDS]
cats['uniesc'] += [o + b + c for b in ['\\u', '\\u{', '\\u{1', '\\u1}', '\\U{1}', '\\u {1}',
                                        '\\u{ 1}', '\\u{1 }', '\\u{1}}', '\\u{{1}', '\\u{+1}',
                                        '\\u{1}\\u{2}', 'a\\u{1}', '\\u{1}a']
                   for (o, c) in QKINDS]

# String continuations: a backslash and a line feed, then whitespace and more.
CONT = ['\\\n' + ''.join(t) for n in range(0, 4)
        for t in itertools.product([' ', '\t', '\n', '\r', 'a', '\\'], repeat=n)]
cats['strcont'] = [o + b + c for b in CONT for (o, c) in QKINDS]

# Comments: line, block (nested), and doc comments; carriage returns in them.
cats['comment5'] = list(words(['/', '*', '!', 'a', '\n', ' '], 1, 5))
cats['comment-cr'] = [p + b for p in ['//', '///', '//!', '////', '/*', '/**', '/*!']
                      for b in ['\r', 'a\rb', 'a\r', '\r\n', 'a\r\nb', '\ra']] + \
                     [p + b + '*/' for p in ['/*', '/**', '/*!', '/***']
                      for b in ['\r', 'a\rb', ' \r ', '', ' ', '*', '/', 'a']]

# Punctuation and maximal munch.
P = list('+-*/%^!&|<>=@_.,;:#$?~')
cats['punct2'] = list(words(P, 1, 2))
cats['punct3'] = list(words(P, 3, 3))
cats['punct4'] = list(words(list('.=<>-:'), 4, 4))

# Raw strings: numbers of "#" before and after, bodies, and what follows.
cats['raw'] = [p + '#' * oh + '"' + b + '"' + '#' * ch + t
               for p in ['r', 'br', 'cr']
               for oh in range(0, 4)
               for b in ['', 'a', '"', '"#', '"##', '#', '\\', 'a"b', '\r', '\xe9', '\0', '\n',
                         '\\"']
               for ch in range(0, 5)
               for t in ['', '#', '_', 'a', '_a', '"', ' x']]
cats['raw'] += [p + '#' * n + '"a"' + '#' * n + t for p in ['r', 'br', 'cr']
                for n in [254, 255, 256, 257] for t in ['', '#']]
cats['raw'] += ['r' + '#' * n + 'a' for n in range(0, 4)] + ['rb"a"', 'rb\'a\'', 'R"a"', 'Br"a"',
                'bR"a"', 'B"a"', 'C"a"', 'cR"a"', "r'a'", "br'a'", "cr'a'", "c'a'", 'rc"a"']

# Tokens of every kind, with a suffix, and with something right after.
LITS = ['1', '0x1', '0b1', "'a'", "b'a'", '"a"', 'b"a"', 'c"a"', 'r"a"', 'r#"a"#', 'br"a"',
        'cr"a"', 'x', '_', '_x', '_1', '__', 'r#x', "'a", "'r#a", "'_", "'static", 'fn', 'b',
        'r', 'br', 'c', 'cr', 'gen', 'r#fn', '_0x1', '_1_']
SUFF = ['', '_', '__', 'a', '_a', 'u8', 'r', 'b', 'e', 'E1', '1', '_1', 'br', 'g']
FOLL = ['', '#', "'", '"', '"x"', "'x'", '#!', ' #', "'x", 'r#a', '##', '.', "#'", '#"x"']
cats['follow'] = [l + s + f for l in LITS for s in SUFF for f in FOLL]

# Lifetimes and labels.
LT = ['a', 'ab', '_', '_a', '__', 'r', 'static', 'fn', 'self', 'r#a', 'r#fn', 'r#self', 'r#crate',
      'r#super', 'r#Self', 'r#_', 'r#_a', 'r#__', 'r#1', 'r#', 'r##', '1', '1a', '12', 'a1',
      '\xe9', 'a\u0301', 'r#r#a', 'r#a#', '#', '']
LF = ['', "'", '#', '"', ' ', "'b", '#a', '_', ':', "'a'", "''", "'#", '"x"', '\n', "\n'"]
cats['lifetime'] = ["'" + l + f for l in LT for f in LF]

# Identifiers, keywords, and their raw forms.
KW = ['as', 'async', 'await', 'break', 'const', 'continue', 'crate', 'dyn', 'else', 'enum',
      'extern', 'false', 'fn', 'for', 'if', 'impl', 'in', 'let', 'loop', 'match', 'mod', 'move',
      'mut', 'pub', 'ref', 'return', 'self', 'Self', 'static', 'struct', 'super', 'trait', 'true',
      'type', 'unsafe', 'use', 'where', 'while', 'abstract', 'become', 'box', 'do', 'final',
      'macro', 'override', 'priv', 'try', 'typeof', 'unsized', 'virtual', 'yield', 'gen',
      'macro_rules', 'raw', 'safe', 'union', 'foo', '_', '_x', 'x_', 'X9', '__', '_9', '9x']
cats['ident'] = [p + k + f for k in KW for p in ['', 'r#', "'", "'r#"] for f in ['', ' x', '!']]

# Whitespace characters, and characters that are not whitespace or tokens.
WS = ['\t', '\n', '\x0b', '\x0c', '\r', ' ', '\x85', '\u200e', '\u200f', '\u2028', '\u2029']
NWS = ['\xa0', '\ufeff', '\u2003', '\u180e', '\u200b', '\u3000', '\u200c', '\u200d', '\x00',
       '\x1f', '\x7f', '`', '\\', '\u202e', '\u2066']
cats['space'] = ['a' + w + 'b' for w in WS + NWS] + [w for w in WS + NWS] + \
                ['"' + w + '"' for w in WS + NWS] + ['//' + w for w in WS + NWS] + \
                ['/*' + w + '*/' for w in WS + NWS] + ["'" + w + "'" for w in WS + NWS]

# Hand-picked cases.
cats['hand'] = [
    '_1#', '_1"x"', "_1'a'", '_a#', '_0#', '_1x"abc"', '__#', '_#', '_"x"', "_'a'",
    '"a"r#b', '1u8#', "'a'b'c'", "'0", "'r#_", 'r#_', 'r#_a', "'a'a'", 'r#abc"x"', "r#abc'x'",
    '0b', '0b_', '0b2', '0b12', '0b1_2', '0b_1', '0b1a', '0x', '0x_', '0xg', '0x1g', '0o8',
    '0o18', '0B1', '0X1', '0O1', '00', '0_', '007', '1__', '1_u8', '1_', '0b1u8', '0o7i64',
    '0xffusize', '0xFF_u8', '0b1_', '0x_1_',
    '>>=', '<<=', '..=', '...', '....', '<-', '=>>', '&&=', '||=', '::<', '->>', '<=>',
    '(a [b {c}])', '[]', '{}', '()', 'a.b', 'a . b', 'a::b', '#[x]', '#![x]', '$a', '$crate',
    'b', 'c', 'r', 'br', 'cr', 'bb', "b'a", 'b"a', 'c"a', "''", "'''", "'\\''", "'\\\\'", '""',
    '"\\""', '"\\\\"', "b'\\''", 'b"\\""',
]

# Float literals and the reserved number forms, at their boundaries with
# integer literals, ranges, field accesses, and suffixes.
cats['float-boundary'] = [
    '1_e3', '1_e', '1_else', '0x1_g', '1_a', '1_E+5', '0b1_e', '1e_1', '1e_', '0x1_e',
    '1.e3', '1..2', '1.foo', '1._1', '1.0_', '0e', '0.', '0.0', '1.0e1_', '1e1e1',
    '1.1.1', '1.\xe9', '0b1.e', '0x1.e', '0x1..', '0o1._', '1f32', '1.0f32', '1e1f32',
    '0b1f32', '1._', '1.r#a', '1.0.0', '1.0e', '1.0e+', '1.0E-_1', '1e+_', '1.0else',
    '1.0_e5', '1.0u8',
]

# Float literals and the reserved number forms: all the short strings
# over digits, a period, an exponent letter, a sign, an underscore,
# a suffix letter, and two radix prefix letters.
cats['num5'] = list(words(['1', '0', '.', 'e', '+', '_', 'a', 'b', 'x'], 1, 5))

# The same with the other exponent letter and sign, digits that are not
# binary or octal, and the octal prefix letter.
cats['num4'] = list(words(['0', '2', '8', '.', 'E', '-', '_', 'o', 'b', 'f'], 1, 4))

# Number literals built from an integer part, a fraction, an exponent,
# and a suffix, with something right after.
NINT = ['1', '1_', '0', '00', '1__2', '0x1', '0xe', '0x', '0b1', '0b1_', '0b2', '0o7']
NFRAC = ['', '.', '.5', '.5_', '._', '._5']
NEXP = ['', 'e', 'e5', 'e+5', 'E-_5', 'E_', 'e+', 'e5_']
NSUFF = ['', 'f32', '_f32', 'e1', 'u8', '_']
NFOLL = ['', '.', '..', '.a', '.0', '#', '"x"']
cats['float'] = [i + f + e + s + t
                 for i in NINT for f in NFRAC for e in NEXP for s in NSUFF for t in NFOLL]

# Hand-picked number literals: the examples of the Reference, shapes
# from real code, and a number literal next to each kind of token.
cats['float-hand'] = [
    '3.14', '2.', '2.0f64', '1e10', '1E10', '6.02e23', '1_000.000_1', '0.5e-3f32',
    '123.0f64', '0.1f64', '0.1f32', '12E+99_f64', '123.0E+77', '1_234.0E+18f64', '5f32',
    '2.0f80', '2e5f80', '2e5e6', '2.0e5e6', '1.3e10u64',
    '0b0102', '0o1279', '0x80.0', '0b101e', '2e', '2.0e', '2em', '2.0em',
    '0x01_f32', '0x01_e3', '2.f64',
    'x.0.1', 't.0.0', 'a.1e5', 'a.0x1', 'a.1.2.3', '1.2.3.4', '1.max(2)', '1.0.max(2.0)',
    '1..=2', '1...2', '1.0..2.0', '1.0..', '..1.0', '0..0', '0...0', '0.0.',
    '1.+2', '1.-2', '1.;', '1.)', '(1.)', '[1.,2.]', '1.\n', '1.\t2', '1./2', '1.//c',
    '1./*c*/', "1.'a'", '1."a"', '1.#', '1.@', '1.\xe9', '1.\u20ac', '1.r', '1.E', '1._e',
    '1.e', '1. e5', '1 .5', '.5', '1.5e+', '1.e-1', '1e-', '1e+-1', '1e--1', '1e1+1',
    '1e1-1', '1e1.1', '1e1.e', '1e1e', '1.0f', '1f', '1e', '1E', '0E0', '0e0',
    '00.5', '0_.5', '1_.5', '1._5', '1.5_', '1.5__f64', '1e5__', '1.0e10f64',
    '0x1p3', '0x1.8p1', '0o7.', '0b1.', '0x1.', '0b1.0', '0o7e1', '0b1E', '0x1e', '0x1E+1',
    '0b1.a', '0o7..', '0x1._', '0b1u8.0', '0x1u8.', '0o7i8e',
    '1.0_f32', '1.0e1_f32', '1e1_', '1.0e_', '1.0e_1', '1e__1__', '1.__', '1.0__',
    '1.0#', '1.0"x"', "1.0'a'", '1.0f32#', '1e1"x"', "1.'a", '1.0r#a', '1.0r"a"',
]

# Characters that Unicode 17 added to XID_Start, and to XID_Continue only
# (the first of each range added since Unicode 16, and the last of the
# largest), alone, after a letter, before a digit, and in lifetimes.
# Versions of rustc whose identifier tables differ lex these differently.
U17_START = [0x88F, 0xC5C, 0xCDC, 0xA7CE, 0xA7D2, 0xA7D4, 0xA7F1, 0x10940, 0x10EC5, 0x11DB0,
             0x16EA0, 0x16EBB, 0x16FF2, 0x187F8, 0x18D09, 0x18D80, 0x1E6C0, 0x1E6E0, 0x1E6E4,
             0x1E6E7, 0x1E6F0, 0x1E6FE, 0x2B73A, 0x2CEA2, 0x323B0, 0x33479]
U17_CONTINUE = [0x1ACF, 0x1AE0, 0x10EFA, 0x11B60, 0x11DE0, 0x1E6E3, 0x1E6E6, 0x1E6EE, 0x1E6F5]
cats['unicode17'] = [p + chr(c) + s for c in U17_START + U17_CONTINUE
                     for (p, s) in [('', ''), ('a', ''), ('', '1'), ("'", ''), ("'a", '')]]

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
total = 0
for name, texts in cats.items():
    seen, uniq = set(), []
    for t in texts:
        if t not in seen:
            seen.add(t)
            uniq.append(t)
    json.dump([{'id': f'{name}:{i}', 'text': t} for i, t in enumerate(uniq)],
              open(os.path.join(out, name + '.json'), 'w', encoding='utf-8'), ensure_ascii=True)
    print(f'{name:16s} {len(uniq):6d}')
    total += len(uniq)
print(f'{"total":16s} {total:6d}')
