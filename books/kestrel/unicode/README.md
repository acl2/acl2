# Unicode Library

An ACL2 model of the parts of the Unicode Standard that the lexers of
programming languages need: code points, the identifier and white space
properties, normalization, and the bidirectional controls.  It is a shared
library: nothing in it is specific to one language.

The documentation is in XDOC (topic `unicode::unicode`); this file covers
what a maintainer needs: where things are, where the data comes from, how to
regenerate it, how to add a Unicode version, and how the library was
validated.

## Abbreviations

- NFD, NFC, NFKD, NFKC: Normalization Forms D, C, KD and KC (UAX #15,
  Table 1).  D is for the two decomposed forms and C for the two composed
  forms; K stands for compatibility, because C already stands for
  composition.
- `XID_Start`, `XID_Continue`: `ID` is short for identifier.  UAX #31
  derives these two properties from `ID_Start` and `ID_Continue` with the
  modifications of its Section 5.1, which are there so that normalizing an
  identifier gives an identifier.  The letter X marks the properties that
  have those modifications; the Unicode documents do not say what it stands
  for.  An XID identifier is a code point with `XID_Start` followed by code
  points with `XID_Continue`.
- UAX: Unicode Standard Annex.  UAX #15 is Unicode Normalization Forms,
  UAX #31 is Unicode Identifiers and Syntax.
- UCD: Unicode Character Database.

## What is here

| Book | Contents |
|------|----------|
| `code-points` | Code points and scalar values, as natural numbers (never ACL2 characters). Surrogates are code points but not scalar values. |
| `versions` | The supported versions of Unicode, as a type. |
| `xid` | `XID_Start` and `XID_Continue`, and the XID identifiers (the default identifiers of UAX #31). |
| `pattern-white-space` | `Pattern_White_Space`. |
| `bidi-controls` | `Bidi_Control`, and the explicit directional formatting characters with their `Bidi_Class`. |
| `hangul` | The arithmetic decomposition and composition of Hangul syllables. |
| `combining-classes` | `Canonical_Combining_Class`. |
| `decompositions` | `Decomposition_Mapping`, and the full canonical and compatibility decompositions. |
| `compositions` | `Full_Composition_Exclusion`, and the pairs that compose. |
| `normalization` | The canonical ordering and composition algorithms; `nfd`, `nfc`, `nfkd`, `nfkc`; `nfd-memberp`, `nfc-memberp`, `nfkd-memberp`, `nfkc-memberp`. |
| `identifier-closure` | The proof that the four normalization forms take identifiers to identifiers. |
| `quick-check` | The `NF*_Quick_Check` properties (used here only to cross-check normalization). |
| `utf-8` | Theorems connecting scalar values to the verified UTF-8 codec of `[books]/unicode`. |
| `ranges` | The fixtypes of ranges of code points and of lists of ranges, which represent the binary properties. |
| `maps` | The fixtypes of the tree maps from code points to values, which represent the other properties. |
| `top` | All of the above, and the overview topics of the documentation. |
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

All the functions are in logic mode with guards verified.  Their arguments
and results have fixtypes: code points, scalar values, lists of those,
precomposed Hangul syllables, versions, ranges, and maps.  The property
functions take a code point; the normalization functions take a list of
code points.

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
  `bidi-explicit-formatting-class-alt-def`: these properties are the same
  eleven, twelve and nine code points in every supported version.
- Composing the decomposition of a Hangul syllable gives the syllable back
  (checked for all 11,172 syllables).  The Hangul functions take a
  `hangul-syllable`, which is a fixtype, so their theorems have no
  hypotheses.
- `composition-of-decomposition-mapping` and
  `decomposition-mapping-of-composition`: composing two code points and
  taking the canonical decomposition mapping of a code point are inverses
  of each other, on the pairs that compose and on the primary composites
  and precomposed Hangul syllables.
- `undecomposable-listp-of-nfd`, `canonically-ordered-p-of-nfd`: the result
  of `nfd` is fully decomposed and in canonical order; the same for `nfkd`.
- `nfd-when-undecomposable-listp-and-canonically-ordered-p`, and the same
  for `nfkd`: a list that is fully decomposed and in canonical order is its
  own decomposed form.
- `nfd-of-nfd`, `nfkd-of-nfkd`, `nfd-of-nfkd`: normalizing a second time to
  a decomposed form changes nothing.
- `nfc-of-nfd`, `nfkc-of-nfkd`, `nfc-of-nfkd`: composing after decomposing
  again is the same as composing.
- `decomposition-when-decomposition-mapping`: the decomposition of a code
  point is the decomposition of its decomposition mapping, which is how the
  standard defines the full decompositions.
- `decomposition-of-composition`: the decomposition of the code point that
  two code points compose to is the decomposition of the first one followed
  by the decomposition of the second one.
- `canonical-order-of-decompose-of-canonical-compose`: canonical composition
  can be undone.  If a list is fully decomposed and canonically ordered,
  decomposing its canonical composition and putting the result in canonical
  order gives the list back.
- `nfd-of-nfc`, `nfkd-of-nfkc`, `nfd-of-nfkc`: decomposing a composed form
  gives the decomposed form.
- `nfc-of-nfc`, `nfkc-of-nfkc`, `nfc-of-nfkc`: normalizing a second time to
  a composed form changes nothing.
- `nfd-memberp`, `nfc-memberp`, `nfkd-memberp`, `nfkc-memberp` say that a
  list is in the form (`isNFD` and so on in UAX #15), that is, that the form
  leaves it unchanged.  `nfc-memberp-of-nfc` (and the same for the other
  three): the form of a list is in that form.  `nfd-memberp-of-nfkd`,
  `nfc-memberp-of-nfkc`: the NFKD form of a list is in NFD, and the NFKC
  form is in NFC.  `nfd-memberp-when-nfkd-memberp`,
  `nfc-memberp-when-nfkc-memberp`: so a list that is in NFKD is in NFD, and
  a list that is in NFKC is in NFC.
- `decompose-of-canonical-decompose`: decomposing a list canonically first
  makes no difference to its decomposition.
- `canonical-order-of-decompose-of-canonical-order`: putting a list in
  canonical order before decomposing it does not change the canonical order
  of its decomposition.
- `nfkd-of-nfd`, `nfkd-of-nfc`, `nfkc-of-nfd`, `nfkc-of-nfc`: normalizing to
  a canonical form first makes no difference to the compatibility forms.
  With these, all sixteen ways of applying one form after another are
  covered: the form applied last says whether the result is composed, and
  the result is a compatibility form if either of the two is.
- `xid-identifier-p-of-nfc` (and the same for the other three forms):
  normalizing an XID identifier gives an XID identifier, that is, a
  code point with `XID_Start` followed by code points with `XID_Continue`.
  This is the closure under normalization of UAX #31, Section 5.1.3.  For
  `nfd` and `nfc` the theorems are equalities: a list is an identifier
  exactly when its form is.  The same theorems hold for
  `xid-continue-listp`, the lists of code points with `XID_Continue`.
- `canonical-combining-class-when-xid-start-p`: a code point with
  `XID_Start` is a starter.

### Including only what you need

Each of these books can be included on its own; none of them needs `top`.
Including one brings in the books in its row, with the tables of every
supported version, and nothing else of this library.

| To get | Include | Books of this library that it loads | Tables that it loads |
|--------|---------|-------------------------------------|----------------------|
| `code-point-p`, `scalar-value-p`, and the types of their lists | `code-points` | | |
| `xid-start-p`, `xid-continue-p`, `xid-identifier-p` | `xid` | `code-points`, `versions`, `ranges` | `derived-core-properties` |
| `pattern-white-space-p` | `pattern-white-space` | `code-points`, `versions`, `ranges` | `prop-list` |
| `bidi-control-p`, `bidi-explicit-formatting-p`, `bidi-explicit-formatting-class` | `bidi-controls` | `code-points`, `versions`, `ranges`, `maps` | `prop-list`, `derived-bidi-class` |
| `nfd`, `nfc`, `nfkd`, `nfkc`, and `nfd-memberp` and the other three | `normalization` | `code-points`, `versions`, `ranges`, `maps`, `hangul`, `combining-classes`, `decompositions`, `compositions` | `unicode-data`, `derived-combining-class`, `derived-normalization-props` |
| The theorems that normalizing an identifier gives an identifier | `identifier-closure` | `xid`, `normalization`, and the books that those load | the tables of `xid` and of `normalization` |
| `nfc-quick-check` and the other three | `quick-check` | `code-points`, `versions`, `ranges` | `derived-normalization-props` |
| Theorems that what the UTF-8 decoder of `[books]/unicode` returns are scalar values | `utf-8` | `code-points` | none (it loads that decoder) |

A front end for a language whose identifiers follow UAX #31 typically needs
`xid`; `normalization` if it normalizes or compares identifiers, and then
`identifier-closure` to know that what it normalizes is still an identifier;
`pattern-white-space` and `bidi-controls` if its white space or the
characters it rejects are defined by those properties; and `utf-8` if it
decodes its input with `[books]/unicode`.

- **`top`** is all of the above, and the documentation.  Neither `top` nor
  any book in the table loads the tests or the test vectors: only the books
  in `tests/` do.
- **Cost.**  All of them need `centaur/fty/top`, which is most of what it
  costs to include the small ones.  `normalization` costs the most: it has
  the largest tables, and it loads the compatibility decompositions even if
  only NFC is used.
- **Effect on the including book.**  The settings that these books certify
  under (`controlled-configuration`) are local to them.  What they leave
  enabled are the definitions and the theorems about the functions of this
  library.
- **Packages.**  A book in another package can call these functions with
  the package prefix, e.g. `unicode::xid-start-p`, once it has included the
  book; nothing else is needed.  To import symbols of this library into
  another package, put
  `(include-book "kestrel/unicode/portcullis" :dir :system)` before the
  `defpkg` in that package's `package.lsp`.
- **Versions.**  A front end should pick its version of Unicode in one
  place: a function from its own configuration (the edition of the
  language, the release of the compiler being modeled) to a `version`,
  whose result it passes down.
- **Types.**  The functions take code points (`code-point-p`) and lists of
  them (`code-point-listp`), and the normalization functions return a
  `scalar-value-listp` when given one.  A front end with its own type of
  scalar values needs a theorem that its values are scalar values of this
  library, and the converse to get results back; `scalar-value-p-alt-def`
  (a scalar value is a natural number below `#xD800`, or from `#xE000` to
  `#x10FFFF`) makes both easy to prove.
- **Small sets.**  `Pattern_White_Space` and the bidirectional controls are
  a few code points, the same in all the supported versions.  A front end
  that lists them in its own grammar or lexer can keep its list and prove
  it equal to the property, for any version, from
  `pattern-white-space-p-alt-def`, `bidi-control-p-alt-def` and
  `bidi-explicit-formatting-p-alt-def`.

## Versions

Every function whose result depends on the Unicode Character Database takes
the version as an argument, of type `version`.  The supported versions are
`(version-v16.0.0)`, `(version-v17.0.0)` and `(version-v18.0.0)`.  There is
no default version,
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

The tables are fixtypes.  A binary property is a list of ranges of code
points (`fty::defprod range`, `fty::deflist range-list`); the generated
books build these lists with the constructor of ranges.  The other tables
are tree maps (`fty::deftreemap`) from code points to values, or, for
composition, from pairs of code points (`fty::defprod code-point-pair`) to
scalar values.  Every table that is not built with typed constructors is
checked against the recognizer of its type, by evaluation, in the book
that defines it.  The conformance test vectors are typed too: a line of
`NormalizationTest.txt` is a `normalization-test-line`, a product with one
field per column (`tests/normalization-test-types`), and the generated
books build the lines with its constructor.

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

For example 19.0.0 (this is how 18.0.0 was added):

1. Generate the tables and record the SHA-256 of the inputs:
   `python3 tools/generate-ucd-books.py 19.0.0 UCD_DIR --fetch --pin`.
2. In `versions.lisp`, add `(:v19.0.0 ())` to the type `version`, and a line
   to `version-string`.
3. In each book that selects tables by version (`xid`,
   `pattern-white-space`, `bidi-controls`, `combining-classes`,
   `decompositions`, `compositions`, `quick-check`), add the `include-book`
   of the new data book and a `:v19.0.0` line to each selector;
   `grep -n v18.0.0 *.lisp` finds every place.  In `decompositions` and
   `compositions`, also copy the block that defines and checks the computed
   tables.
4. In `tests/`, copy `normalization-test-v18.0.0.lisp` and
   `quick-check-v18.0.0.lisp`, changing the version.
5. Certify `top` and `tests/*`.  This checks the invariants of the new
   tables, re-proves for the new version the theorems listed above (if one
   fails, that is a real change in Unicode to look at), and runs the
   conformance test.
6. For the comparison with other implementations, add
   `validation/rust-oracle/v19.0.0/Cargo.toml` with the versions of the
   crates that implement Unicode 19.0.0.

Nothing else changes: no definition, and no theorem statement.

## Validation

Nothing here is a proof that the functions implement the Unicode Standard;
there is no formal specification to prove that against.  The evidence is:

### Tests that run when the books are certified (`tests/`)

- `normalization-test-v<version>`: **all of `NormalizationTest.txt`**, for
  each version: all the invariants for NFC, NFD, NFKC and NFKD on every line
  of every part (19,965 lines for 16.0.0, 20,034 for 17.0.0, 20,171 for
  18.0.0), and the
  requirement that every code point not listed in Part 1 is unchanged by the
  four forms, checked for all the code points, assigned or not.
- `quick-check-v<version>`: for every code point, the `NF*_Quick_Check`
  properties and `Full_Composition_Exclusion`, which are read from
  `DerivedNormalizationProps.txt`, agree with the normalization functions,
  which are computed from other files.
- `properties`: examples.

The conformance test takes about ten seconds per version, and the
quick-check test about twenty.

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
- Unicode 18.0.0 was compared in the same way, on 2026-11-14, with
  `unicode-ident` 1.0.27, `unicode-normalization` 0.1.26 and rustc's lexer
  (`ra-ap-rustc_lexer` 0.184.0), with no differences.  No Python with
  Unicode 18.0.0 was available; so for 18.0.0 `Bidi_Control`, the explicit
  formatting classes and `Decomposition_Mapping` have not been compared
  with another implementation (the first two are proved to be the same as
  in the other versions).

To repeat this (it needs `acl2` and `cargo`, and for the Python part an
interpreter with the right version of Unicode):

```
cert.pl validation/dump
validation/run.sh 16.0.0 /tmp/unicode-validation python3.14
validation/run.sh 17.0.0 /tmp/unicode-validation python3.15
validation/run.sh 18.0.0 /tmp/unicode-validation
```

## Performance

Lookups in the maps (combining classes, decompositions, compositions) take
time logarithmic in the size of the map.  Membership in a list of ranges
(the binary properties, such as `XID_Start`) takes time linear in the
number of ranges, which is a few hundred for the largest properties.
The normalization functions are meant for identifiers and the like: they are
not tail recursive, and reordering a run of *n* combining marks takes time
quadratic in *n*.

## License

The books and tools are under the 3-clause BSD license of ACL2.  The tables
in `data/` are derived from the Unicode Character Database, which is
Copyright © Unicode, Inc. and is distributed under the Unicode License V3
(`Unicode-3.0`), a permissive license that requires its notice to accompany
copies of the data; the notice is in the file `LICENSE-UNICODE`.
