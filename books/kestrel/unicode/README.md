# Unicode Library

An ACL2 model of the parts of the Unicode Standard that the lexers of
programming languages need: code points, the identifier and white space
properties, normalization, and the bidirectional controls.  It is a shared
library: nothing in it is specific to one language.

The documentation is in XDOC (topic `unicode::unicode`); this file covers
what a maintainer needs: where things are, where the data comes from, how to
regenerate it, how to add a Unicode version, and how the library was
validated.

## What is here

| Book | Contents |
|------|----------|
| `code-points` | Code points and scalar values, as natural numbers (never ACL2 characters). Surrogates are code points but not scalar values. |
| `versions` | The supported versions of Unicode, as a type. |
| `xid` | `XID_Start` and `XID_Continue`. |
| `pattern-white-space` | `Pattern_White_Space`. |
| `bidi-controls` | `Bidi_Control`, and the explicit directional formatting characters with their `Bidi_Class`. |
| `hangul` | The arithmetic decomposition and composition of Hangul syllables. |
| `combining-classes` | `Canonical_Combining_Class`. |
| `decompositions` | `Decomposition_Mapping`, and the full canonical and compatibility decompositions. |
| `compositions` | `Full_Composition_Exclusion`, and the pairs that compose. |
| `normalization` | The canonical ordering and composition algorithms; `nfd`, `nfc`, `nfkd`, `nfkc`. |
| `quick-check` | The `NF*_Quick_Check` properties (used here only to cross-check normalization). |
| `utf-8` | Theorems connecting scalar values to the verified UTF-8 codec of `[books]/unicode`. |
| `range-sets`, `range-maps`, `nat-maps` | The representations of the tables, with their invariants. |
| `top` | All of the above. |
| `data/v<version>/` | **Generated** tables, one book per file of the Unicode Character Database. |
| `tests/` | Tests that run when certified, including the whole of `NormalizationTest.txt`. |
| `tools/` | The generator of the data books, and the pinned SHA-256 of its inputs. |
| `validation/` | Tools to compare the library, on every code point, with other implementations. |

Out of scope: collation, text segmentation, the bidirectional algorithm, and
confusables.  Not done yet, to be added when a use needs them: the general
category and the case mappings.

Encodings are elsewhere and are not rebuilt here: `[books]/unicode` has a
verified UTF-8 decoder and encoder, and `[books]/kestrel/unicode-light` has
utilities for UTF-8 and UTF-16 (this library uses its surrogate recognizers).

## Using it

```lisp
(include-book "kestrel/unicode/top" :dir :system)

(unicode::xid-start-p #x03BB (unicode::version-v16.0.0))        ; T
(unicode::nfc '(#x0073 #x0307 #x0323) (unicode::version-v16.0.0)) ; (#x1E69)
```

A book that needs only some properties can include only those books, e.g.
`kestrel/unicode/xid`, which loads only the `XID` tables.

All the functions are in logic mode with guards verified.  The property
functions take any natural number (and are false, or 0, beyond `#x10FFFF`);
the normalization functions take lists of code points.

Some theorems that hold in every supported version, proved by evaluation
over the tables, and so re-checked whenever a version is added:

- `xid-continue-p-when-xid-start-p`; a code point with either property is a
  scalar value.
- `xid-start-p-when-ascii`, `xid-continue-p-when-ascii`: on ASCII, the letters
  start identifiers, and the letters, digits and underscore continue them.
- `nfc-when-all-below-a0` (and the same for the other three forms):
  normalization leaves a list of code points below `#xA0`, in particular an
  ASCII one, unchanged.  So a tool that handles only ASCII identifiers
  without normalizing agrees, on those, with one that follows the Unicode
  rules.
- The normalization forms map lists of scalar values to lists of scalar
  values.
- `pattern-white-space-p-alt-def`, `bidi-control-p-alt-def`,
  `bidi-formatting-class-alt-def`: these properties are the same eleven,
  twelve and nine code points in every supported version.
- Composing the decomposition of a Hangul syllable gives the syllable back
  (checked for all 11,172 syllables).

## Versions

Every function whose result depends on the Unicode Character Database takes
the version as an argument, of type `version`.  The supported versions are
`(version-v16.0.0)` and `(version-v17.0.0)`.  There is no default version,
and nothing means "latest": adding a version never changes the result of an
existing call.  Which version a use needs is for that use to say, and it
need not be tied to a release of the language being modeled.

## The data

The books in `data/v<version>/` are written by
`tools/generate-ucd-books.py` from these files of the Unicode Character
Database (UCD) of that version, at
`https://www.unicode.org/Public/<version>/ucd/`:

| UCD file | Generated book | Tables |
|----------|----------------|--------|
| `DerivedCoreProperties.txt` | `derived-core-properties` | `XID_Start`, `XID_Continue` |
| `PropList.txt` | `prop-list` | `Pattern_White_Space`, `Bidi_Control` |
| `extracted/DerivedCombiningClass.txt` | `derived-combining-class` | `Canonical_Combining_Class` |
| `UnicodeData.txt` | `unicode-data` | `Decomposition_Mapping` (canonical and compatibility) |
| `DerivedNormalizationProps.txt` | `derived-normalization-props` | `Full_Composition_Exclusion`, `NF*_Quick_Check` |
| `extracted/DerivedBidiClass.txt` | `derived-bidi-class` | `Bidi_Class`, for the nine explicit formatting classes only |
| `NormalizationTest.txt` | `normalization-test` | The conformance test vectors |

Three more files are read only to interpret or cross-check those:
`PropertyValueAliases.txt`, `CompositionExclusions.txt`, and
`extracted/DerivedDecompositionType.txt`.

Each generated book records the URL of its source file and the SHA-256 of
the bytes that were read.  `tools/ucd-sources.json` has the same for all the
files that are read, for each version; the generator refuses to run on files
whose SHA-256 is not the one recorded there.

How the generator reads the UCD:

- **Derived properties come from the derived files**; they are not
  recomputed.  Where the same information is also computable from the
  primary files (the combining classes and decomposition types from
  `UnicodeData.txt`; `Full_Composition_Exclusion` from
  `CompositionExclusions.txt` and `UnicodeData.txt`), the generator computes
  it too, compares, and stops on any difference.
- **Defaults come from the `@missing` lines.**  A code point that a file does
  not list takes the value of the last `@missing` line that covers it.
  (`extracted/DerivedBidiClass.txt` has two dozen such lines.)  Binary
  properties have no `@missing` lines; their default is "no".
- **`First`/`Last` pairs of lines in `UnicodeData.txt` are ranges.**
- **Surrogates are code points** and get property values like any others.

What is computed in ACL2 rather than generated: the full decompositions
(by expanding the mappings, with a check that the result cannot be expanded
further) and the table of the pairs that compose (from the canonical
mappings and `Full_Composition_Exclusion`).  The Hangul syllables are
handled by the arithmetic of the standard, not by tables.

The tables are sorted lists of disjoint ranges, or sorted alists.  That
invariant is part of the recognizer of each kind of table, and every table
is checked against its recognizer, by evaluation, in the book that defines
it.

### Where the bytes came from

The UCD files are not in the repository.  The data books were first
generated, on 2026-11-13, from copies in the Unicode Consortium's repository
on GitHub (`unicode-org/unicodetools`, directory
`unicodetools/data/ucd/<version>/`).  On 2026-11-14, all the files that the
generator reads, for every supported version, were downloaded from
`www.unicode.org`, at the URLs recorded in the books: they are byte-identical
to those copies, so the recorded SHA-256 values are those of the official
files.

To repeat that check for a version:

```
python3 tools/generate-ucd-books.py 16.0.0 /tmp/ucd-16.0.0 --fetch --check
```

This downloads the files from `www.unicode.org`, fails if the SHA-256 of any
of them differs from the one in `tools/ucd-sources.json`, and then checks
that the books it would generate are the ones in the tree.

### Regenerating

```
python3 tools/generate-ucd-books.py 16.0.0 UCD_DIR [--fetch]
```

where `UCD_DIR` is laid out like `https://www.unicode.org/Public/16.0.0/ucd/`
(`--fetch` downloads into it the files that are missing).  The version must
be written in full.  The script needs only the Python standard library.

### Adding a version

For example 18.0.0:

1. Generate the tables and record the SHA-256 of the inputs:
   `python3 tools/generate-ucd-books.py 18.0.0 UCD_DIR --fetch --pin`.
2. In `versions.lisp`, add `(:v18.0.0 ())` to the type `version`, and a line
   to `version-string`.
3. In each book that selects tables by version (`xid`,
   `pattern-white-space`, `bidi-controls`, `combining-classes`,
   `decompositions`, `compositions`, `quick-check`), add the `include-book`
   of the new data book and a `:v18.0.0` line to each selector;
   `grep -n v17.0.0 *.lisp` finds every place.  In `decompositions` and
   `compositions`, also copy the block that defines and checks the computed
   tables.
4. In `tests/`, copy `normalization-test-v17.0.0.lisp` and
   `quick-check-v17.0.0.lisp`, changing the version.
5. Certify `top` and `tests/*`.  This checks the invariants of the new
   tables, re-proves for the new version the theorems listed above (if one
   fails, that is a real change in Unicode to look at), and runs the
   conformance test.
6. For the comparison with other implementations, add
   `validation/rust-oracle/v18.0.0/Cargo.toml` with the versions of the
   crates that implement Unicode 18.0.0.

Nothing else changes: no definition, and no theorem statement.

## Validation

Nothing here is a proof that the functions implement the Unicode Standard;
there is no formal specification to prove that against.  The evidence is:

### Tests that run when the books are certified (`tests/`)

- `normalization-test-v<version>`: **all of `NormalizationTest.txt`**, for
  each version: all the invariants for NFC, NFD, NFKC and NFKD on every line
  of every part (19,965 lines for 16.0.0, 20,034 for 17.0.0), and the
  requirement that every code point not listed in Part 1 is unchanged by the
  four forms, checked for all the code points, assigned or not.
- `quick-check-v<version>`: for every code point, the `NF*_Quick_Check`
  properties and `Full_Composition_Exclusion`, which are read from
  `DerivedNormalizationProps.txt`, agree with the normalization functions,
  which are computed from other files.
- `properties`: examples.

Each of the two exhaustive tests takes about a minute per version.

### Comparison with independent implementations (`validation/`)

The results of the library on **every code point** (not samples) were
compared with implementations of the *same* version of Unicode.
`validation/dump.lisp` writes, for each of the 1,114,112 code points, its
`XID_Start`, `XID_Continue`, `Pattern_White_Space`, `Bidi_Control`,
explicit formatting class, `Canonical_Combining_Class`,
`Decomposition_Mapping`, and the NFD, NFC, NFKD and NFKC forms of the code
point alone; the oracles write the same from other implementations, and
`validation/compare.py` compares the files.  A second file, with 97,080
pairs of code points (every first of a composing pair with every second of a
composing pair, Hangul included), compares composition and the NFC form of
each pair.

Run on 2026-11-13, with ACL2 at commit `3ccb342c8` (SBCL 2.6.1):

| | Unicode 16.0.0 | Unicode 17.0.0 |
|---|---|---|
| `XID_Start`, `XID_Continue` | `unicode-xid` 0.2.6; `unicode-ident` 1.0.18; `regex-syntax` 0.8.5; rustc's lexer (`ra-ap-rustc_lexer` 0.145.0); Python 3.14.6; Python `regex` 2025.9.18 | `unicode-ident` 1.0.22; rustc's lexer (`ra-ap-rustc_lexer` 0.146.0); Python 3.15.0b4; Python `regex` 2026.1.15 |
| `Pattern_White_Space` | `regex-syntax`; rustc's lexer; Python `regex` | rustc's lexer; Python `regex` |
| `Bidi_Control` | `regex-syntax`; Python `regex` | Python `regex` |
| Explicit formatting classes | Python | Python |
| `Canonical_Combining_Class` | `unicode-normalization` 0.1.24; Python | `unicode-normalization` 0.1.25; Python |
| `Decomposition_Mapping` | Python | Python |
| NFD, NFC, NFKD, NFKC of each code point | `unicode-normalization`; Python | `unicode-normalization`; Python |
| Composition and NFC of 97,080 pairs | `unicode-normalization`; Python | `unicode-normalization`; Python |
| **Differences** | **none** | **none** |

Notes:

- The crates for 17.0.0 are the versions in the `Cargo.lock` of rustc 1.97.0.
  There is no release of `unicode-xid` or `regex-syntax` for 17.0.0.
- The Rust oracle cannot say anything about the 2,048 surrogates, which are
  not Rust `char`s; Python covers them.
- Each oracle checks that it implements the requested version and stops
  otherwise.  The Python `regex` module does not say which version its
  tables are for; the oracle infers it from two code points (see
  `XID_START_PROBES` in `validation/python-oracle.py`).
- Python's `unicodedata.decomposition` returns the full decomposition of a
  Hangul syllable, where the `Decomposition_Mapping` of the standard is a
  pair; for the Hangul syllables that column is compared with NFD instead.
- As a control, comparing the 16.0.0 output of the library with the 17.0.0
  oracle reports 4,647 code points that differ in `XID_Start`.

To repeat this (it needs `acl2` and `cargo`, and for the Python part an
interpreter with the right version of Unicode):

```
cert.pl validation/dump
validation/run.sh 16.0.0 /tmp/unicode-validation python3.14
validation/run.sh 17.0.0 /tmp/unicode-validation python3.15
```

## Performance

Lookups stop early in the sorted tables, so they are fast for small code
points (ASCII in particular) and linear in the size of the table for large
ones; the largest tables have a few thousand entries.  That is adequate for
lexing; faster structures can be put behind the same functions if needed.
The normalization functions are meant for identifiers and the like: they are
not tail recursive, and reordering a run of *n* combining marks takes time
quadratic in *n*.

## License

The books and tools are under the 3-clause BSD license of ACL2.  The tables
in `data/` are derived from the Unicode Character Database, which is
Copyright © Unicode, Inc. and is distributed under the Unicode License V3
(`Unicode-3.0`), a permissive license that requires its notice to accompany
copies of the data; the notice is in the file `LICENSE-UNICODE`.
