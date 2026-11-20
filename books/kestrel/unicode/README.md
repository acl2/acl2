# Unicode Library

An ACL2 model of the parts of the Unicode Standard that the lexers of
programming languages need: code points, the identifier and white space
properties, normalization, scripts, the bidirectional classes and controls,
and the properties that say which characters are safe in identifiers.  It
is a shared library: nothing in it is specific to one language.

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
- The values of `General_Category` have long names and two-letter
  abbreviations (UAX #44, Table 12): `Lu` is `Uppercase_Letter`, `Mn` is
  `Nonspacing_Mark`, `Cn` is `Unassigned`, and so on.  The constructors of
  the type `general-category` use the long names; the documentation of the
  type lists all thirty with their abbreviations, and
  `general-category-abbreviation` returns the abbreviation.
- `ID_Start`, `ID_Continue`: the properties of the code points that can
  start, and continue, an identifier in the default syntax of UAX #31.
  `Other_ID_Start` and `Other_ID_Continue` are the short lists of code
  points that have them although their `General_Category` would not give
  them.  `ID_Compat_Math_Start` and `ID_Compat_Math_Continue` (`Compat` is
  short for compatibility) are the characters that the mathematical
  notation profile of UAX #31 adds.
- A script has a long name and a four-letter code, which is its code in
  ISO 15924: `Latn` is `Latin`, `Zyyy` is `Common`, `Zinh` is `Inherited`,
  `Zzzz` is `Unknown`.  The constructors of the type `script` use the long
  names; `script-code` returns the code.
- The values of `Bidi_Class` have long names and abbreviations of one to
  three letters (UAX #9, Table 4): `L` is `Left_To_Right`, `R` is
  `Right_To_Left`, `AL` is `Arabic_Letter`, `NSM` is `Nonspacing_Mark`, and
  so on.  The documentation of the type `bidi-class` lists all
  twenty-three.
- UAX: Unicode Standard Annex.  UAX #9 is the Unicode Bidirectional
  Algorithm, UAX #15 is Unicode Normalization Forms, UAX #24 is Unicode
  Script Property, UAX #31 is Unicode Identifiers and Syntax, UAX #44 is
  the Unicode Character Database.  UTS: Unicode Technical Standard.
  UTS #39 is Unicode Security Mechanisms, and UTS #51 is Unicode Emoji.
- UCD: Unicode Character Database.

## What is here

| Book | Contents |
|------|----------|
| `code-points` | Code points and scalar values, as natural numbers (never ACL2 characters). Surrogates are code points but not scalar values. |
| `versions` | The supported versions of Unicode, as a type, and the order in which they were released (`version<=`). |
| `general-category` | `General_Category`: `code-point-general-category`, the ranges of the code points that have a value (`general-category-ranges`), and `assigned-p`. |
| `general-category-changes` | The code points whose `General_Category` is not the same in two versions (`general-category-changes`), and those of them that are assigned in the first version (`general-category-changes-of-assigned`), as lists of ranges; the proof that in the supported versions the `General_Category` of an assigned code point is the same in every later version, with one exception, U+0295. |
| `xid` | `XID_Start` and `XID_Continue`, and the XID identifiers (the default identifiers of UAX #31); the two optional characters for the start of an identifier, `$` and `_`. |
| `id` | `ID_Start`, `ID_Continue`, `Other_ID_Start` and `Other_ID_Continue`; the exact difference between the `ID` and the `XID` properties (23 and 19 code points); a code point that has `ID_Start` or `ID_Continue` has it in every later version. |
| `id-compat-math` | `ID_Compat_Math_Start` and `ID_Compat_Math_Continue`, the characters of the mathematical notation profile of UAX #31. |
| `scripts` | `Script` (`code-point-script`) and `Script_Extensions` (`code-point-script-extensions`), with the ranges of the code points of a script and of those whose script extensions contain it; the proof that the script extensions contain the script, unless it is `Common` or `Inherited`. |
| `identifier-status` | `Identifier_Status` (`identifier-allowed-p`) and `Identifier_Type` (`code-point-identifier-types`) of UTS #39, with the proof that a code point is allowed exactly when all its types are `Inclusion` or `Recommended`. |
| `identifier-status-normalization` | The proof that NFKC changes no allowed code point, and changes every code point that has the type `Not_NFKC`. |
| `pattern-white-space` | `Pattern_White_Space`. |
| `pattern-syntax` | `Pattern_Syntax`. |
| `bidi-controls` | `Bidi_Control`, and the explicit directional formatting characters with their `Bidi_Class`. |
| `bidi-class` | `Bidi_Class` in full (`code-point-bidi-class`), and the proof that it agrees with the table of the explicit formatting classes of `bidi-controls`. |
| `emoji` | `Emoji`, `Emoji_Presentation`, `Emoji_Modifier`, `Emoji_Modifier_Base`, `Emoji_Component`, `Extended_Pictographic` and `Regional_Indicator`, with how they contain each other. |
| `decimal-digits` | The decimal digits and their values (`decimal-digit-value`), with the proof that the digits of a system are ten consecutive code points with the values 0 to 9. |
| `blocks` | `Block` (`code-point-block`), with the proof that a block is one range and that a block of a version is the same block in every later version. |
| `default-ignorable` | `Default_Ignorable_Code_Point`. |
| `variation-selectors` | `Variation_Selector`. |
| `join-controls` | `Join_Control`: the zero width joiner and non-joiner. |
| `noncharacters` | `Noncharacter_Code_Point`, with the proof that the tables are the 66 code points that the standard describes. |
| `deprecated` | `Deprecated`. |
| `prepended-concatenation-marks` | `Prepended_Concatenation_Mark`. |
| `property-relations` | Theorems that relate properties to each other: a code point that is not a starter is a mark; variation selectors are nonspacing marks; bidirectional controls, join controls and variation selectors are default ignorable; noncharacters are unassigned; `Pattern_Syntax` is disjoint from `Pattern_White_Space`, and both are disjoint from `XID_Continue`; `ID_Start` and `ID_Continue` are what UAX #31 derives them from; the script is `Unknown` exactly for the unassigned, private-use and surrogate code points; the decimal digits are the code points of category `Nd`; what the identifier types say about other properties; and more. |
| `hangul` | The arithmetic decomposition and composition of Hangul syllables. |
| `combining-classes` | `Canonical_Combining_Class`. |
| `decompositions` | `Decomposition_Mapping`, and the full canonical and compatibility decompositions. |
| `compositions` | `Full_Composition_Exclusion`, and the pairs that compose. |
| `normalization` | The canonical ordering and composition algorithms; `nfd`, `nfc`, `nfkd`, `nfkc`; `nfd-memberp`, `nfc-memberp`, `nfkd-memberp`, `nfkc-memberp`; `canonical-equivalent-p`, `compatibility-equivalent-p`. |
| `composing-pairs` | The code points that compose with a code point after them (`composes-with-following-p`) and those that compose with a code point before them (`composes-with-previous-p`); the type of sets of code points. |
| `normalization-inert` | `normalization-inert-p`: a starter with no decomposition that composes with nothing.  The proof that each of the four forms normalizes separately what is before and what is after such a code point, and leaves it as it is.  Which ASCII code points are inert; `Pattern_White_Space` code points are. |
| `normalization-members` | Which code points can occur in a normalization form of a list: for an inert ASCII code point, exactly when it occurs in NFD and in NFC; and the proof that NFC brings in no ASCII code point, with three exceptions. |
| `stream-safe` | The Stream-Safe Text Format (`stream-safe-p`) and the Stream-Safe Text Process (`stream-safe-process`) of UAX #15, with the proof that the process gives text in the format and leaves text in the format unchanged, and that normalizing does not change whether text is in the format. |
| `normalization-across-versions` | The proof that the four normalization forms of a list of code points that are assigned in a version are the same in every later version (the normalization stability of the Unicode Standard), and so are the combining class and the decompositions of an assigned code point, and what two assigned code points compose to.  The same for the Stream-Safe Text Format and Process, and for the quick check properties. |
| `identifier-closure` | The proof that the four normalization forms take identifiers to identifiers, also when the identifier starts with `$` or `_`; a canonical equivalent of an identifier is an identifier. |
| `quick-check` | The `NF*_Quick_Check` properties (the normalization functions do not use them). |
| `quick-check-theorems` | The proof that the quick check is exact for NFD and NFKD, and that the code points that NFC and NFKC change are those whose quick check value is No. |
| `utf-8` | Theorems connecting scalar values to the verified UTF-8 codec of `[books]/unicode`. |
| `ranges` | The fixtypes of ranges of code points and of lists of ranges, which represent the binary properties. |
| `range-operations` | Union, intersection, difference and complement of sets of code points given as lists of ranges, each with the theorem that says which code points are in the result; the normal form of a list of ranges; the list of the code points of a list of ranges. |
| `maps` | The fixtypes of the tree maps from code points to values, which represent the properties with a default value: combining classes, decompositions, the classes of the explicit formatting characters, and the values of the decimal digits. |
| `runs` | The macro `defruns`, which introduces, for a property with many values, the fixtype of runs of code points with the same value, the lookup, the ranges of a value (or, when the values are sets, of the code points whose set has an element), and the theorems that relate them. |
| `general-category-tables` | The fixtype of the thirty values of `General_Category`, the list of the thirty values (`general-category-values`), and the runs of that property. |
| `script-tables` | The fixtype of the scripts, defined from one table of their codes and names (`*script-table*`); the runs of `Script` and of `Script_Extensions`. |
| `bidi-class-tables` | The fixtype of the twenty-three values of `Bidi_Class`, with the predicates for the strong, weak, neutral and explicit formatting classes; the runs of that property. |
| `block-tables` | The runs of `Block`, whose values are the names of the blocks, as strings. |
| `identifier-type-tables` | The fixtype of the twelve values of `Identifier_Type`, and the runs of that property, whose values are lists of types. |
| `coverage` | Documentation only: what the library models of each Unicode specification, what it does not, and for which programming languages that is enough. |
| `top` | All of the above, and the overview topics of the documentation. |
| `data/v<version>/` | **Generated** tables, one book per file of the Unicode Character Database, and two books from the data files of UTS #39. |
| `tests/` | Tests that run when certified, including the whole of `NormalizationTest.txt`. |
| `tools/` | The generator of the data books, and the pinned SHA-256 of its inputs. |
| `validation/` | Tools to compare the library, on every code point, with other implementations. |

What is not modeled is listed, specification by specification, in the
documentation topic `unicode-coverage` (book `coverage`).  Among other
things: character names, case mappings, the bidirectional algorithm, text
segmentation, confusables and the detection of mixed scripts of UTS #39,
emoji sequences, and collation.  That topic is also the only place where
the library names programming languages: it says, for C, Java, Python,
Rust, Scheme and Remora, whether the library has all that their lexical
rules take from Unicode.

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
- `canonical-equivalent-p` and `compatibility-equivalent-p` say that two
  lists are canonical equivalents (definition D70 of the Unicode Standard:
  they have the same NFD form) and compatibility equivalents (D67: the same
  NFKD form).  Each is reflexive, symmetric and transitive.
  `canonical-equivalent-p-of-nfc-arg1` (and `-arg2`, and the same for
  `nfd`; for compatibility equivalence, the same for all four forms): a
  form of a list can take the place of the list.
  `canonical-equivalent-p-in-terms-of-nfc`: two lists are canonical
  equivalents exactly when they have the same NFC form;
  `compatibility-equivalent-p-in-terms-of-nfkc`: the same for the NFKC
  form.  `compatibility-equivalent-p-when-canonical-equivalent-p`:
  canonical equivalents are compatibility equivalents.
- `xid-identifier-p-when-canonical-equivalent-p`: two canonical equivalents
  are both XID identifiers, or neither is.  The same holds for
  `xid-continue-listp`.
- `optional-start-p` says that a code point is the dollar sign or the
  underscore, the two optional characters for the start of an identifier
  in UAX #31, Table 3.  `nfc-of-cons-when-optional-start-p` (and the same
  for the other three forms): the form of such a code point followed by a
  list is that code point followed by the form of the list.  So an
  identifier that starts with `$` or `_` and goes on with code points with
  `XID_Continue` normalizes to one of the same kind.
  `nfc-memberp-of-cons-when-optional-start-p` (and the same for the other
  three): such a list is in the form exactly when the rest of it is.
- `nfd-memberp-alt-def`, `nfkd-memberp-alt-def`: a list is in NFD, or in
  NFKD, exactly when it is fully decomposed and in canonical order.
- `nfd-quick-check-yes-p-alt-def`, `nfkd-quick-check-yes-p-alt-def`: the
  `NFD_Quick_Check` (or `NFKD_Quick_Check`) of a code point is Yes exactly
  when the code point is its own canonical (or compatibility)
  decomposition.  `nfd-memberp-in-terms-of-quick-check`,
  `nfkd-memberp-in-terms-of-quick-check`: so a list is in NFD (or NFKD)
  exactly when every code point has the value Yes and the list is in
  canonical order, which is what the quick check of UAX #15, Section 9,
  tests.  For these two forms, which have no Maybe values, the quick check
  is exact.  (The same for NFC and NFKC is not done yet.)
- `nfc-changes-p-in-terms-of-quick-check`,
  `nfkc-changes-p-in-terms-of-quick-check`: NFC (or NFKC) changes a code
  point, taken alone, exactly when its `NFC_Quick_Check` (or
  `NFKC_Quick_Check`) is No.  So "the characters that NFKC changes" and
  "the characters whose `NFKC_Quick_Check` is No" are the same set.
- `composition-when-not-composes-with-following-p`,
  `composition-when-not-composes-with-previous-p`: two code points do not
  compose if the first one is not the first code point of any pair that
  composes, or the second one is not the second code point of any.
  `composes-with-following-p-when-ascii`: the ASCII code points that compose
  with a code point after them are the letters other than `Q` and `q`, and
  `<`, `=`, `>`.  `not-composes-with-previous-p-when-below-300`.
- `normalization-inert-p` says that a code point is a starter, has no
  decomposition, and composes neither with a code point after it nor with
  one before it.  `nfc-of-append-of-cons-when-normalization-inert-p` (and
  the same for the other three forms): the form of a list, then an inert
  code point, then another list, is the form of the first list, then the
  code point, then the form of the second list.  So if the delimiters of a
  language are inert, normalizing its text is the same as normalizing each
  piece between delimiters.
  `nfc-memberp-of-append-of-cons-when-normalization-inert-p` (and the same
  for the other three): such a list is in the form exactly when the first
  list is and the second list is.  `normalization-inert-p-when-ascii`: an
  ASCII code point is inert unless it is a letter other than `Q` and `q`,
  or one of `<`, `=`, `>`.
  `normalization-inert-p-when-pattern-white-space-p`.  These generalize the
  theorems about `$` and `_` above.
- `canonical-order-of-append-of-cons-when-starter-p`: canonical ordering
  does not move code points past a starter.
- `member-equal-of-canonical-order`: the canonical order of a list has the
  same code points as the list.
  `member-equal-of-nfd-when-member-equal-of-nfc`: a code point with no
  canonical decomposition that occurs in NFC occurs in NFD (composition
  does not make such a code point).
  `member-equal-of-nfc-when-normalization-inert-p`: an inert code point
  occurs in NFC exactly when it occurs in NFD; the same for NFKC and NFKD.
- `member-equal-of-nfd-when-inert-ascii`,
  `member-equal-of-nfc-when-inert-ascii`: an inert ASCII code point occurs
  in NFD (or NFC) of a list exactly when it occurs in the list, or it is the
  semicolon and U+037E GREEK QUESTION MARK occurs in the list, or it is the
  grave accent and U+1FEF GREEK VARIA occurs in the list.  So the canonical
  forms neither bring in nor take away the ASCII digits, the space, or the
  ASCII punctuation other than `<`, `=`, `>`, with those two exceptions.
- `member-equal-of-nfc-when-ascii`: NFC brings in no ASCII code point, with
  three exceptions.  If an ASCII code point, inert or not, occurs in NFC of
  a list, then it occurs in the list, or it is the semicolon and U+037E
  occurs in the list, or it is the grave accent and U+1FEF occurs in the
  list, or it is the letter `K` and U+212A KELVIN SIGN occurs in the list.
  So an ASCII letter, or `<`, `=` or `>`, that comes out of the
  decomposition of a code point always composes again.  (The converse
  fails for those: a letter followed by a mark that it composes with is not
  in the NFC form.  There is no such theorem for NFKD and NFKC.)
- `stream-safe-p-of-stream-safe-process`: the Stream-Safe Text Process of
  UAX #15, Section 13, gives text in Stream-Safe Text Format, that is, text
  whose NFKD form has no more than 30 non-starters in a row.
  `stream-safe-process-when-stream-safe-p`: the process leaves such text
  unchanged.  `stream-safe-p-in-terms-of-decompose`: the format can be
  checked on the compatibility decomposition, before it is put in canonical
  order.  `stream-safe-p-of-nfc` (and the same for the other three forms):
  putting text in a normalization form does not change whether it is in
  the format.  `nfd-memberp-of-stream-safe-process`,
  `nfkd-memberp-of-stream-safe-process`: the process keeps text that is in
  NFD, or in NFKD, in that form.  (UAX #15 says the same of NFC and NFKC;
  that is not proved.)

Theorems about two versions.  `(version<= ver1 ver2)` says that `ver1` is
`ver2` or was released before it.  The Unicode Standard promises some of
these in its
[stability policies](https://unicode.org/policies/stability_policy.html);
here they are theorems about the supported versions, proved by evaluation
on the tables of each pair of versions, and so re-checked whenever a
version is added.  They are disabled by default, because the earlier
version is in their hypotheses only.

- `assigned-p-of-later-version`: a code point that is assigned in a version
  is assigned in every later version.  `assigned-listp` says that every
  code point of a list is assigned.
- `xid-start-p-of-later-version`, `xid-continue-p-of-later-version`,
  `xid-identifier-p-of-later-version`: a code point that has `XID_Start` or
  `XID_Continue` keeps it, and an XID identifier stays one.
- `nfc-of-later-version` (and the same for the other three forms): if every
  code point of a list is assigned in a version, the form of the list is
  the same in every later version.  This is the normalization stability of
  the standard.  So are `nfc-memberp-of-later-version` (and the other
  three), `canonical-equivalent-p-of-later-version` and
  `compatibility-equivalent-p-of-later-version`: such a list is in a form,
  and two such lists are equivalent, in the later version exactly when
  they are in the earlier one.  The hypothesis is needed: U+1ACF COMBINING
  DOUBLE CARON is not assigned in 16.0.0, and the NFC form of the letter
  `a`, U+1ACF and U+0323 COMBINING DOT BELOW is not the same in 16.0.0 and
  in 17.0.0 (a test in `tests/properties` shows it).
- `canonical-combining-class-of-later-version`,
  `decomposition-of-later-version`, `composition-of-later-version`: the
  combining class and the decompositions of an assigned code point, and
  what two assigned code points compose to, are the same in every later
  version.  `assigned-listp-of-nfc` (and the other three forms): the forms
  of a list of assigned code points consist of assigned code points.
- `pattern-white-space-p-same-in-all-versions`,
  `pattern-syntax-p-same-in-all-versions`,
  `noncharacter-p-same-in-all-versions`: these properties have the same
  code points in every version, as the standard promises.
  `bidi-control-p-same-in-all-versions`,
  `join-control-p-same-in-all-versions`,
  `variation-selector-p-same-in-all-versions`,
  `deprecated-p-same-in-all-versions`,
  `default-ignorable-p-same-in-all-versions`,
  `prepended-concatenation-mark-p-same-in-all-versions`: so do these, in the
  supported versions; the standard does not promise it.
- The `General_Category` of an assigned character can change.
  `code-point-in-general-category-changes`: a code point is in the ranges
  of `(general-category-changes ver1 ver2)` exactly when its
  `General_Category` is not the same in the two versions;
  `general-category-changes-of-assigned` leaves out the code points that
  are not assigned in the first version.
  `code-point-general-category-of-later-version`: in the supported
  versions, the `General_Category` of an assigned code point is the same in
  every later version, unless the code point is U+0295 LATIN LETTER
  PHARYNGEAL VOICED FRICATIVE, which went from `Ll` to `Lo` in 17.0.0.
  The code points of `Control`, `Private_Use` and `Surrogate` are the same
  in every version, as the standard promises
  (`general-category-control-ranges-same-in-all-versions` and two more).

Operations on lists of ranges, for a model that defines its own sets of
code points from the properties, or that compares a property between two
versions:

- `ranges-union`, `ranges-intersection`, `ranges-difference`,
  `ranges-complement`, each with a theorem such as
  `code-point-in-ranges-p-of-ranges-union`: a code point is in the ranges
  of the union exactly when it is in the ranges of one of the two lists.
  These theorems have no hypotheses.  The results are in a normal form
  (`ranges-normalized-p`): no empty range, increasing order, and at least
  one code point between two ranges; `ranges-normalize` puts any list in
  that form.  A list in normal form has no code point exactly when it is
  `nil`, so that two sets are disjoint, or one is within the other, can be
  tested by evaluation
  (`code-point-in-ranges-p-when-ranges-difference-is-empty`).
- `range-list-code-points` is the list of the code points of a list of
  ranges, in order; its length is `range-list-size`, and it has no
  duplicates when the list is in normal form.
- For example, `(ranges-difference (xid-start-ranges (version-v17.0.0))
  (xid-start-ranges (version-v16.0.0)))` is the list of the 4,647 code
  points that got `XID_Start` in 17.0.0.

The properties with many values are tables of runs (`runs`, `defruns`).
For each, one function gives the value of a code point and another the
ranges of the code points that have a value, and a theorem says that the
two agree: `code-point-in-general-category-ranges`,
`code-point-in-script-ranges`, `code-point-in-bidi-class-ranges`,
`code-point-in-block-ranges`; and, for the properties whose values are
sets, `code-point-in-script-extensions-ranges` and
`code-point-in-identifier-type-ranges`: a code point is in the ranges of
an element exactly when the element is in its set.  So a fact about every
code point is proved by evaluation on a few thousand ranges; most of the
theorems below are proved that way.

About identifiers:

- `id-start-p-in-terms-of-general-category`,
  `id-continue-p-in-terms-of-general-category`: `ID_Start` and
  `ID_Continue`, which the library reads from `DerivedCoreProperties.txt`,
  are what UAX #31, Table 2, derives them from: the letters and letter
  numbers (and, to continue, the marks, the decimal digits and the
  connector punctuation), with `Other_ID_Start` and `Other_ID_Continue`,
  without `Pattern_Syntax` and `Pattern_White_Space`.
- `id-start-p-in-terms-of-xid-start-p`,
  `id-continue-p-in-terms-of-xid-continue-p`: a code point has `ID_Start`
  exactly when it has `XID_Start` or is one of 23 code points, which
  `id-start-not-xid-start-ranges` lists; the same for `ID_Continue`, with
  19 code points.  The lists are the same in every supported version.
- `id-start-p-of-later-version`, `id-continue-p-of-later-version`: these
  two properties only grow, as the standard promises.
- `not-id-continue-p-when-id-compat-math-continue-p`: the characters of
  the mathematical notation profile are not characters of the default
  identifiers.
- `identifier-allowed-p-in-terms-of-types`: the `Identifier_Status` of a
  code point is `Allowed` exactly when each of its `Identifier_Type`s is
  `Inclusion` or `Recommended`.  The two properties come from two files.
- `not-nfkc-changes-p-when-identifier-allowed-p`,
  `nfkc-of-list-when-identifier-allowed-p`: NFKC changes no allowed code
  point.  `nfkc-changes-p-when-identifier-type-not-nfkc`: NFKC changes
  every code point that has the type `Not_NFKC`.  (The converse fails for
  seven code points, which are `Deprecated` or `Default_Ignorable`.)
- `identifier-type-not-character-in-terms-of-general-category`,
  `identifier-type-deprecated-in-terms-of-deprecated-p`,
  `default-ignorable-p-when-identifier-type-default-ignorable`,
  `not-xid-continue-p-when-identifier-type-not-xid`: the identifier types
  are what UTS #39, Table 1, says they are, in terms of the other
  properties.

About scripts, bidirectional classes, emoji, digits and blocks:

- `member-equal-of-code-point-script-and-script-extensions`: the script
  extensions of a code point contain its script, unless the script is
  `Common` or `Inherited`.  `consp-of-code-point-script-extensions`: they
  are never empty.
- `script-unknown-in-terms-of-general-category`: the script of a code
  point is `Unknown` exactly when the code point is unassigned, private
  use or a surrogate.
- `bidi-explicit-formatting-class-in-terms-of-bidi-class`: the full table
  of `Bidi_Class` agrees with the small table of the nine explicit
  formatting classes that `bidi-controls` has.
  `general-category-when-bidi-class-nonspacing-mark`: a code point of
  class `NSM` is a nonspacing or an enclosing mark.
- `emoji-p-when-emoji-presentation-p` (and the same for the modifiers,
  the modifier bases and the regional indicators);
  `extended-pictographic-p-or-emoji-component-p-when-emoji-p`: an emoji is
  a pictograph or an emoji component.  `emoji-modifier-p-alt-def`,
  `regional-indicator-p-alt-def`, `emoji-component-ranges-alt-def`: these
  three are the same code points in every supported version.
- `decimal-digit-value-of-decimal-digit-zero-plus`: the decimal digits of a
  system are ten consecutive code points with the values 0 to 9; so
  `decimal-digit-zero`, the code point of a digit less its value, tells the
  systems of digits apart.  `decimal-digit-p-in-terms-of-general-category`:
  the decimal digits are the code points of category `Nd`.
- `len-of-block-ranges-upper-bound`: a block is one range.
  `block-ranges-of-later-version`: a block of a version is the same block
  in every later version.

And about two versions, besides the theorems listed further up:
`stream-safe-p-of-later-version`, `stream-safe-process-of-later-version`
(text of assigned characters stays in Stream-Safe Text Format, and the
process gives the same result), and `nfc-quick-check-of-later-version`
(and the other three: the quick check values of an assigned code point
stay the same).

### Including only what you need

Each of these books can be included on its own; none of them needs `top`.
Including one brings in the books in its row, with the tables of every
supported version, and nothing else of this library.

| To get | Include | Books of this library that it loads | Tables that it loads |
|--------|---------|-------------------------------------|----------------------|
| `code-point-p`, `scalar-value-p`, and the types of their lists | `code-points` | | |
| `xid-start-p`, `xid-continue-p`, `xid-identifier-p`, `optional-start-p` | `xid` | `code-points`, `versions`, `ranges` | `derived-core-properties` |
| `id-start-p`, `id-continue-p`, `other-id-start-p`, `other-id-continue-p` | `id` | `xid`, and the books that it loads | `derived-core-properties`, `prop-list` |
| `id-compat-math-start-p`, `id-compat-math-continue-p` | `id-compat-math` | `id`, and the books that it loads | the same |
| `code-point-script`, `script-ranges`, `code-point-script-extensions`, `script-extensions-ranges`; the type `script` | `scripts` | `code-points`, `versions`, `ranges`, `runs`, `script-tables` | `scripts`, `script-extensions` |
| `code-point-bidi-class`, `bidi-class-ranges`; the type `bidi-class` and its predicates such as `bidi-class-right-to-left-p` | `bidi-class` | `bidi-controls`, `runs`, `bidi-class-tables`, and the books that those load | `derived-bidi-class`, `prop-list` |
| `code-point-block`, `block-ranges`, `block-names` | `blocks` | `code-points`, `versions`, `ranges`, `runs`, `block-tables` | `blocks` |
| `emoji-p`, `emoji-presentation-p`, `emoji-modifier-p`, `emoji-modifier-base-p`, `emoji-component-p`, `extended-pictographic-p`, `regional-indicator-p` | `emoji` | `code-points`, `versions`, `ranges` | `emoji-data`, `prop-list` |
| `decimal-digit-value`, `decimal-digit-p`, `decimal-digit-zero` | `decimal-digits` | `code-points`, `versions`, `ranges`, `maps` | `unicode-data` |
| `identifier-allowed-p`, `code-point-identifier-types`, `identifier-type-ranges`; the type `identifier-type` | `identifier-status` | `code-points`, `versions`, `ranges`, `runs`, `identifier-type-tables` | `identifier-status`, `identifier-type` |
| The theorems that relate the identifier status and types to NFKC | `identifier-status-normalization` | `property-relations`, `quick-check-theorems`, and the books that those load | the tables of those books |
| `code-point-general-category`, `general-category-ranges`, `assigned-p`; the type `general-category` and its predicates such as `general-category-letter-p` | `general-category` | `code-points`, `versions`, `ranges`, `general-category-tables` | `derived-general-category` |
| `general-category-changes`, `general-category-changes-of-assigned`, and the theorem that the `General_Category` of an assigned code point stays the same, with one exception | `general-category-changes` | `general-category`, `range-operations`, and the books that those load | `derived-general-category` |
| `ranges-union`, `ranges-intersection`, `ranges-difference`, `ranges-complement`, `ranges-normalize`, `range-list-code-points` | `range-operations` | `code-points`, `ranges` | none |
| `pattern-white-space-p` | `pattern-white-space` | `code-points`, `versions`, `ranges` | `prop-list` |
| `pattern-syntax-p` | `pattern-syntax` | `code-points`, `versions`, `ranges` | `prop-list` |
| `default-ignorable-p` | `default-ignorable` | `code-points`, `versions`, `ranges` | `derived-core-properties` |
| `variation-selector-p`, `join-control-p`, `noncharacter-p`, `deprecated-p`, `prepended-concatenation-mark-p` | `variation-selectors`, `join-controls`, `noncharacters`, `deprecated`, `prepended-concatenation-marks` (one book each) | `code-points`, `versions`, `ranges` | `prop-list` |
| `bidi-control-p`, `bidi-explicit-formatting-p`, `bidi-explicit-formatting-class` | `bidi-controls` | `code-points`, `versions`, `ranges`, `maps` | `prop-list`, `derived-bidi-class` |
| `nfd`, `nfc`, `nfkd`, `nfkc`; `nfd-memberp` and the other three; `canonical-equivalent-p`, `compatibility-equivalent-p` | `normalization` | `code-points`, `versions`, `ranges`, `maps`, `hangul`, `combining-classes`, `decompositions`, `compositions` | `unicode-data`, `derived-combining-class`, `derived-normalization-props` |
| `composes-with-following-p`, `composes-with-previous-p`; the type `code-point-set` | `composing-pairs` | `compositions`, and the books that it loads | `unicode-data`, `derived-normalization-props` |
| `normalization-inert-p`, and the theorems about normalization around an inert code point | `normalization-inert` | `composing-pairs`, `normalization`, `pattern-white-space`, and the books that those load | the tables of `normalization`, and `prop-list` |
| The theorems about the code points that occur in a normalization form | `normalization-members` | `normalization-inert`, and the books that it loads | the same |
| `stream-safe-p`, `stream-safe-process` | `stream-safe` | `normalization`, and the books that it loads | the tables of `normalization` |
| The theorems that the normalization forms of assigned code points are the same in every later version, and the same for Stream-Safe text and for the quick check properties | `normalization-across-versions` | `normalization`, `stream-safe`, `quick-check`, `general-category`, and the books that those load | the tables of `normalization`, and `derived-general-category` |
| The theorems that normalizing an identifier gives an identifier | `identifier-closure` | `xid`, `normalization`, and the books that those load | the tables of `xid` and of `normalization` |
| `nfc-quick-check` and the other three | `quick-check` | `code-points`, `versions`, `ranges` | `derived-normalization-props` |
| The theorems that the quick check is exact for NFD and NFKD, and `nfc-changes-p`, `nfkc-changes-p` | `quick-check-theorems` | `quick-check`, `normalization`, and the books that those load | the tables of `normalization` |
| Theorems that what the UTF-8 decoder of `[books]/unicode` returns are scalar values | `utf-8` | `code-points` | none (it loads that decoder) |
| Theorems that relate properties to each other | `property-relations` | the books of all the properties that it relates, which are most of the library except normalization | the tables of those books |

A front end for a language whose identifiers follow UAX #31 typically needs
`xid`; `normalization` if it normalizes or compares identifiers, and then
`identifier-closure` to know that what it normalizes is still an identifier,
and `normalization-inert` to know that normalization does not reach across
its delimiters;
`pattern-white-space` and `bidi-controls` if its white space or the
characters it rejects are defined by those properties; and `utf-8` if it
decodes its input with `[books]/unicode`.  A front end for a language that
defines its identifiers or its white space by general categories needs
`general-category`.  The predicates on values, such as
`general-category-letter-p`, apply to the result of
`code-point-general-category`; a set of code points given by a list of
categories can also be had as lists of ranges, with
`general-category-ranges`, and the theorem
`code-point-in-general-category-ranges` says that the two agree.

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
- **Small sets.**  `Pattern_White_Space`, the bidirectional controls, the
  join controls, the variation selectors and the noncharacters are a few
  code points or a few ranges, the same in all the supported versions.  A
  front end that lists them in its own grammar or lexer can keep its list
  and prove it equal to the property, for any version, from
  `pattern-white-space-p-alt-def`, `bidi-control-p-alt-def`,
  `bidi-explicit-formatting-p-alt-def`, `join-control-p-alt-def`,
  `variation-selector-p-alt-def` and `noncharacter-p-alt-def`.
- **Speed of `General_Category`.**  `code-point-general-category` goes
  through the list of runs, about 4,100 of them, until it finds the run of
  the code point; `general-category-ranges` goes through the whole list at
  each call.  That is enough for proofs and for tests.  A faster lookup,
  proved equal to this one, is not there yet.

## Versions

Every function whose result depends on the Unicode Character Database takes
the version as an argument, of type `version`.  The supported versions are
`(version-v16.0.0)`, `(version-v17.0.0)` and `(version-v18.0.0)`.  There is
no default version,
and nothing means "latest": adding a version never changes the result of an
existing call.  Which version a use needs is for that use to say, and it
need not be tied to a release of the language being modeled.

`(version<= ver1 ver2)` says that `ver1` is `ver2` or was released before
it.  A model that moves from a version to a later one can use the theorems
about two versions, listed under "Using it": what is assigned stays
assigned, an identifier stays an identifier, and the normalization forms of
text whose characters are all assigned stay the same.  What can change is
the `General_Category` of an existing character;
`general-category-changes-of-assigned` lists those changes for any two
versions.  The documentation topic `versions` has the whole list.

## The data

The books in `data/v<version>/` are written by
`tools/generate-ucd-books.py` from these files of the Unicode Character
Database (UCD) of that version, at
`https://www.unicode.org/Public/<version>/ucd/`, and from two data files
of UTS #39:

| UCD file | Generated book | Tables |
|----------|----------------|--------|
| `DerivedCoreProperties.txt` | `derived-core-properties` | `XID_Start`, `XID_Continue`, `Default_Ignorable_Code_Point`, `ID_Start`, `ID_Continue` |
| `PropList.txt` | `prop-list` | `Pattern_White_Space`, `Bidi_Control`, `Join_Control`, `Variation_Selector`, `Noncharacter_Code_Point`, `Deprecated`, `Prepended_Concatenation_Mark`, `Pattern_Syntax`, `Other_ID_Start`, `Other_ID_Continue`, `ID_Compat_Math_Start`, `ID_Compat_Math_Continue`, `Regional_Indicator` |
| `extracted/DerivedGeneralCategory.txt` | `derived-general-category` | `General_Category` |
| `extracted/DerivedCombiningClass.txt` | `derived-combining-class` | `Canonical_Combining_Class` |
| `UnicodeData.txt` | `unicode-data` | `Decomposition_Mapping` (canonical and compatibility); the values of the decimal digits |
| `DerivedNormalizationProps.txt` | `derived-normalization-props` | `Full_Composition_Exclusion`, `NF*_Quick_Check` |
| `extracted/DerivedBidiClass.txt` | `derived-bidi-class` | `Bidi_Class`: a map for the nine explicit formatting classes, and the runs of the whole property |
| `Scripts.txt` | `scripts` | `Script` |
| `ScriptExtensions.txt` | `script-extensions` | `Script_Extensions` |
| `Blocks.txt` | `blocks` | `Block` |
| `emoji/emoji-data.txt` | `emoji-data` | `Emoji`, `Emoji_Presentation`, `Emoji_Modifier`, `Emoji_Modifier_Base`, `Emoji_Component`, `Extended_Pictographic` |
| `IdentifierStatus.txt` of UTS #39 | `identifier-status` | `Identifier_Status` |
| `IdentifierType.txt` of UTS #39 | `identifier-type` | `Identifier_Type` |
| `NormalizationTest.txt` | `normalization-test` | The conformance test vectors |

Three more files are read only to interpret or cross-check those:
`PropertyValueAliases.txt`, `CompositionExclusions.txt`, and
`extracted/DerivedDecompositionType.txt`.

The two files of UTS #39 are not in the `ucd/` directory, and they moved:
they are at `https://www.unicode.org/Public/security/16.0.0/` for 16.0.0,
and at `https://www.unicode.org/Public/<version>/security/` from 17.0.0 on.
The generator knows both places (`canonical_url`), and expects the two
files in the subdirectory `security/` of the directory it is given.

Each generated book records the URL of its source file and the SHA-256 of
the bytes that were read.  `tools/ucd-sources.json` has the same for all the
files that are read, for each version; the generator refuses to run on files
whose SHA-256 is not the one recorded there.

How the generator reads the UCD:

- **Derived properties come from the derived files**; they are not
  recomputed.  Where the same information is also computable from the
  primary files (the combining classes, decomposition types and general
  categories from `UnicodeData.txt`; `Full_Composition_Exclusion` from
  `CompositionExclusions.txt` and `UnicodeData.txt`), the generator computes
  it too, compares, and stops on any difference.
- **Defaults come from the `@missing` lines.**  A code point that a file does
  not list takes the value of the last `@missing` line that covers it.
  (`extracted/DerivedBidiClass.txt` has two dozen such lines.)  Binary
  properties have no `@missing` lines; their default is "no".  The default
  of `Script_Extensions` is written `<script>`: the set of the one script
  that `Scripts.txt` gives to the code point.
- **The properties with many values are written as runs that cover every
  code point**, the defaults included: `Unknown` for the script,
  `No_Block` for the block, `Not_Character` for the identifier type.
- **The scripts are checked against the type.**  The book `scripts` of a
  version asserts that every script of `PropertyValueAliases.txt`, with
  its code and its long name, is an entry of `*script-table*`.
- **`First`/`Last` pairs of lines in `UnicodeData.txt` are ranges.**
- **Surrogates are code points** and get property values like any others.

What is computed in ACL2 rather than generated: the full decompositions
(by expanding the mappings, with a check that the result cannot be expanded
further) and the table of the pairs that compose (from the canonical
mappings and `Full_Composition_Exclusion`).  The Hangul syllables are
handled by the arithmetic of the standard, not by tables.

The tables are fixtypes.  A binary property is a list of ranges of code
points (`fty::defprod range`, `fty::deflist range-list`); the generated
books build these lists with the constructor of ranges.  `General_Category`
is a list of runs (`fty::defprod general-category-run`: a first code point,
a last code point, and the value they all have, which is of the type
`fty::deftagsum general-category`); the runs are in order and cover every
code point exactly once, which each generated book checks by evaluation.
A generated book writes each run as a triple, such as `(#x0041 #x005A "Lu")`,
inside the macro `general-category-run-table`, which expands to one call of
the constructor of runs per triple, with the constructor of the value that
the two-letter abbreviation stands for; so these lists too are built with
the typed constructors, and the files are a third of the size that they
would have with the calls written out.  `Script`, `Script_Extensions`,
`Bidi_Class`, `Block` and `Identifier_Type` are lists of runs in the same
way; the macro `defruns` (book `runs`) introduces the type of the runs and
the functions on them for each, and each has its own macro to write the
runs compactly.  The values of `Script_Extensions` and of
`Identifier_Type` are lists, which stand for sets.  The other
tables are tree maps (`fty::deftreemap`) from code points to values, or,
for composition, from pairs of code points (`fty::defprod code-point-pair`)
to scalar values; and the sets of the code points that are the first, or
the second, of a pair that composes are tree sets (`fty::deftreeset
code-point-set`).  Every table that is not built with typed constructors is
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

The six files that were added later (`Scripts.txt`,
`ScriptExtensions.txt`, `Blocks.txt`, `emoji/emoji-data.txt`, and the two
files of UTS #39) were downloaded from `www.unicode.org` on 2026-11-19,
for each version.

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

where `UCD_DIR` is laid out like `https://www.unicode.org/Public/16.0.0/ucd/`,
with the two files of UTS #39 in its subdirectory `security/`
(`--fetch` downloads into it the files that are missing).  The version must
be written in full.  The script needs only the Python standard library.

### Adding a version

For example 19.0.0 (this is how 18.0.0 was added):

1. Generate the tables and record the SHA-256 of the inputs:
   `python3 tools/generate-ucd-books.py 19.0.0 UCD_DIR --fetch --pin`.
2. In `versions.lisp`, add `(:v19.0.0 ())` to the type `version`, a line
   to `version-string` and to `version-rank`, and a line to the statement
   and to the hint of the theorem `version-fix-in-terms-of-version-case`.
3. In `script-tables.lisp`, add to `*script-table*` the scripts that the
   new version adds, with their codes and long names as in
   `PropertyValueAliases.txt`.  (If one is missing, the generated book
   `scripts` of the new version does not certify, and says which.)
4. In each book that selects tables by version (`general-category`, `xid`,
   `id`, `id-compat-math`, `scripts`, `bidi-class`, `blocks`, `emoji`,
   `decimal-digits`, `identifier-status`,
   `pattern-white-space`, `pattern-syntax`, `bidi-controls`,
   `default-ignorable`, `variation-selectors`, `join-controls`,
   `noncharacters`, `deprecated`, `prepended-concatenation-marks`,
   `combining-classes`, `decompositions`, `compositions`, `composing-pairs`,
   `quick-check`),
   add the `include-book`
   of the new data book and a `:v19.0.0` line to each selector;
   `grep -n v18.0.0 *.lisp` finds every place.  In `decompositions`,
   `compositions` and `composing-pairs`, also copy the block that defines
   and checks the computed tables.
5. In `tests/`, copy `normalization-test-v18.0.0.lisp` and
   `quick-check-v18.0.0.lisp`, changing the version.
6. Certify `top` and `tests/*`.  This checks the invariants of the new
   tables, re-proves for the new version the theorems listed above (if one
   fails, that is a real change in Unicode to look at), and runs the
   conformance test.  The theorems about two versions are re-proved for
   the new version with each of the others.  Some theorems can fail
   without anything being wrong, because they say more than the standard
   promises:
   - `code-point-general-category-of-later-version` names the characters
     whose `General_Category` has changed.  If the new version changes
     another one, evaluate
     `(general-category-changes-of-assigned (version-v18.0.0)
     (version-v19.0.0))` and add what it lists to the statement of the
     theorem and to the range list in the lemma before it.
   - The six theorems that end with `-same-in-all-versions` and that the
     standard does not promise (bidirectional controls, join controls,
     variation selectors, deprecated characters, default ignorable code
     points, prepended concatenation marks) fail if the new version adds a
     code point to the property.  Then the theorem has to go, or to become
     a theorem that the property only grows, like those for `XID_Start`.
     The same goes for the theorems that list the code points of
     `Other_ID_Start`, `Other_ID_Continue`, `ID_Compat_Math_Start`,
     `ID_Compat_Math_Continue`, `Emoji_Modifier`, `Emoji_Component` and
     `Regional_Indicator` (names ending in `alt-def`), and for the two
     lists of the code points that have an `ID` property and not the `XID`
     one.
   - `nfc-quick-check-of-later-version` and
     `nfkc-quick-check-of-later-version` fail if the new version gives the
     value Maybe to a code point that had the value Yes, which the
     stability of normalization allows.
   - `block-ranges-of-later-version` fails if the new version changes a
     block; the stability policies do not cover blocks.
   - The theorems of `property-relations` are facts about the data, some
     of which the specifications state and some not.  If one fails, that
     is a change in Unicode to look at, as before.

   A failure of any of the others (assigned code points, `XID_Start`,
   `XID_Continue`, `ID_Start`, `ID_Continue`, normalization, Stream-Safe
   text, the quick check for NFD and NFKD,
   `Pattern_White_Space`, `Pattern_Syntax`,
   noncharacters, the three fixed values of `General_Category`) would mean
   that the new version breaks a stability policy of the standard, or that
   a table is wrong.
7. For the comparison with other implementations, add
   `validation/rust-oracle/v19.0.0/Cargo.toml` with the versions of the
   crates that implement Unicode 19.0.0.

Nothing else changes: no definition other than the table of the scripts,
and no theorem statement other than those just listed.

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
- `properties`: examples.  Among them, the number of code points that each
  version adds, computed from the tables of `General_Category` with the
  operations on lists of ranges: 4,803 for 17.0.0 and 13,007 for 18.0.0.
  These agree with the counts of the code points whose `Age` is 17.0 and
  18.0 in the file `DerivedAge.txt` of the Unicode Character Database,
  which the library does not read (counted with a script on 2026-11-19).

The conformance test takes about ten seconds per version, and the
quick-check test about twenty.

### Comparison with independent implementations (`validation/`)

The results of the library on **every code point** (not samples) were
compared with implementations of the *same* version of Unicode.
`validation/dump.lisp` writes, for each of the 1,114,112 code points, its
`XID_Start`, `XID_Continue`, `Pattern_White_Space`, `Bidi_Control`,
explicit formatting class, `Canonical_Combining_Class`,
`Decomposition_Mapping`, the NFD, NFC, NFKD and NFKC forms of the code
point alone, its `General_Category`, and whether it has each of
`Default_Ignorable_Code_Point`, `Variation_Selector`, `Join_Control`,
`Noncharacter_Code_Point`, `Deprecated`, `Prepended_Concatenation_Mark` and
`Pattern_Syntax`; the oracles write the same from other implementations,
and `validation/compare.py` compares the files.  A second file, with 97,080
pairs of code points (every first of a composing pair with every second of a
composing pair, Hangul included), compares composition and the NFC form of
each pair.  A third file compares the Stream-Safe Text Process on sequences
of code points: see below.

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

The properties added on 2026-11-19 were compared on that day, for every
code point, and the earlier comparisons were run again:

- `General_Category`: with `unicode-properties` 0.1.3 for 16.0.0, 0.1.4 for
  17.0.0 and 0.1.5 for 18.0.0 (the versions that rustc's lexer is built
  with, which checks that they are for the same version of Unicode as
  `unicode-ident`); and with Python 3.14.6 for 16.0.0 and Python 3.15.0b4
  for 17.0.0, which also cover the surrogates.  No differences.
- `Default_Ignorable_Code_Point`, `Variation_Selector`, `Join_Control`,
  `Noncharacter_Code_Point`, `Deprecated`, `Prepended_Concatenation_Mark`
  and `Pattern_Syntax`: with `regex-syntax` 0.8.5, for 16.0.0.  No
  differences.  There is no release of `regex-syntax` for the later
  versions, and the Python `regex` module was not installed for this run.
  But each of these seven tables is the same in 16.0.0, 17.0.0 and 18.0.0,
  as evaluating `(equal (deprecated-ranges (version-v16.0.0))
  (deprecated-ranges (version-v17.0.0)))` and the like shows, so the
  comparison for 16.0.0 covers the three versions.
- The generator also checks `General_Category` of every code point, as
  read from `extracted/DerivedGeneralCategory.txt`, against field 2 of
  `UnicodeData.txt`.

The Stream-Safe Text Process was compared, on the same day, with the
`stream_safe` iterator of `unicode-normalization` (0.1.24, 0.1.25 and 0.1.26
for the three versions).  `validation/dump.lisp` writes what
`stream-safe-process` gives for three sequences for each code point whose
compatibility decomposition has a non-starter (the code point 35 times; 29
combining acute accents, the code point, and 3 more accents; and the code
point 16 times between two letters, and once more), and for five other
sequences: 6,275 sequences for 16.0.0, 6,377 for 17.0.0 and 6,479 for
18.0.0.  The process inserts U+034F in 1,885 of the sequences for 16.0.0.
No differences.  The other definitions and theorems
added on that day (`composing-pairs`, `normalization-inert`,
`normalization-members`) are statements about the normalization functions,
proved in the library; nothing new is compared for them.

The properties of identifiers, scripts, bidirectional classes, emoji and
digits, which were added on 2026-11-20, were compared on that day, for
every code point (`validation/dump.lisp` writes sixteen more columns),
and the earlier comparisons of every code point were run again.  No
differences:

- `Script` and `Script_Extensions`: with `unicode-script` 0.5.7 for
  16.0.0, 0.5.8 for 17.0.0 and 0.5.9 for 18.0.0.  (The crate has no code
  for the script `Unknown`; the oracle writes `Zzzz` for it.)
- `Bidi_Class`: with `unicode-bidi` 0.3.18 for 16.0.0, on the 292,531
  assigned code points that are not surrogates; with Python 3.14.6 for
  16.0.0, on the 294,579 assigned code points (Python 3.14 has no value
  for the others); and with Python 3.15.0b4 for 17.0.0, on every code
  point: that Python gives the unassigned code points the default values
  of the standard.  The unassigned code points are not compared with
  `unicode-bidi`, which does not follow the defaults of
  `extracted/DerivedBidiClass.txt` everywhere: it has L for the 3,835
  unassigned code points whose default is BN, and R for 135 of the 293
  whose default is AL.  There is no release of `unicode-bidi` for the
  later versions, so for 18.0.0 `Bidi_Class` was not compared with another
  implementation.  The generator checks, for the three versions, the
  `Bidi_Class` of every code point that `UnicodeData.txt` lists against
  field 4 of that file.
- `Identifier_Status`: with `unicode-security` 0.1.2 for 16.0.0 and 0.1.3
  for 18.0.0.  There is no release of it for 17.0.0, whose table differs
  from that of 18.0.0 in one code point.
- `Emoji`, `Emoji_Presentation`, `Emoji_Modifier`, `Emoji_Modifier_Base`
  and `Emoji_Component`: with the emoji status of `unicode-properties`
  (0.1.3, 0.1.4 and 0.1.5 for the three versions), which is one of nine
  values according to which of these five properties a code point has
  (the table `EMOJI_STATUS` of `validation/compare.py`).
- `ID_Start`, `ID_Continue`, the five emoji properties just listed,
  `Extended_Pictographic` and `Regional_Indicator`: with `regex-syntax`
  0.8.5, for 16.0.0.  For the later versions, `ID_Start` and `ID_Continue`
  are proved to be what UAX #31 derives from `General_Category`, which is
  compared, and to differ from `XID_Start` and `XID_Continue`, which are
  compared, in the same code points as in 16.0.0; `Regional_Indicator` is
  proved to be the same code points; `Extended_Pictographic` of 17.0.0 and
  18.0.0 was not compared with another implementation.
- The values of the decimal digits: with `unicodedata.decimal` of Python
  3.14.6 for 16.0.0 and of Python 3.15.0b4 for 17.0.0.  For 18.0.0 they
  were not compared; the library proves, for each version, that the
  decimal digits are the code points of category `Nd`, and that they come
  in runs of ten with the values 0 to 9.
- As a control, comparing the 17.0.0 output of the library with the
  18.0.0 oracle reports 13,007 code points that differ in `Script`, 9 in
  emoji status, and 1 in `Identifier_Status`.

Not compared with another implementation, in any version: `Block`,
`Identifier_Type`, `Other_ID_Start`, `Other_ID_Continue`,
`ID_Compat_Math_Start` and `ID_Compat_Math_Continue`.  What the library
has about them is the data files and the theorems: the last four are
proved to be short lists of code points, which the documentation shows;
the identifier types are proved to agree with the identifier status,
which is compared; nothing checks the blocks beyond the checks of the
generator.

To repeat this (it needs `acl2` and `cargo`, and for the Python part an
interpreter with the right version of Unicode):

```
cert.pl validation/dump
validation/run.sh 16.0.0 /tmp/unicode-validation python3.14
validation/run.sh 17.0.0 /tmp/unicode-validation python3.15
validation/run.sh 18.0.0 /tmp/unicode-validation
```

## Documentation topics

The documentation is in XDOC, under the topic `unicode::unicode`.  Most of
its topics are written next to the definitions that they document.  The
macros that define types also generate topics, and for a type with many
values those are many topics that say nothing: `fty::deftagsum` generates
three for each value, which have only the name of the value in them.

The rule of this library: when one form generates more than 50
documentation topics, and they say nothing that one written topic could
not say, the form goes inside `xdoc::without-xdoc` (book `xdoc/alter`),
and one topic is written for it.  Three types are over the line:

| Type | Values | Generated topics, turned off |
|---|---|---|
| `script` | 179 | 543 |
| `general-category` | 30 | 96 |
| `bidi-class` | 23 | 75 |

The written topic of each of these types lists the values, says how the
constructors are named, and names the recognizer, the fixer, the
equivalence, the `-kind` function and the `-case` macro of the type.
Those are the ones that `fty::deftagsum` always introduces, and they are
used in the same way; they only have no topics of their own, so their
names are not links in the documentation of the functions that use them.
For `script`, the list of the values in the topic is generated from
`*script-table*`, and has the constructor of each value.

The rule is about topics without content.  It does not turn off topics
that show a definition: the functions that `defruns` introduces for each
table of runs (17 topics for each of six properties) keep theirs, because
the macro writes their definitions, and their topics are where those and
their theorems can be read.  The smaller types of the same kind
(`identifier-type`, with 12 values and 42 topics, and the ones with fewer
values) are under the line and keep the generated topics.

With this, the library has about 700 topics.

## Performance

Lookups in the maps (combining classes, decompositions, compositions) take
time logarithmic in the size of the map, and so do membership tests in the
sets of code points (the code points that compose with others).
Membership in a list of ranges
(the binary properties, such as `XID_Start`) takes time linear in the
number of ranges, which is a few hundred for the largest properties.
A lookup of `General_Category` takes time linear in the number of runs,
which is about 4,100; the same goes for `Script` (about 1,700 runs),
`Script_Extensions` (1,900), `Bidi_Class` (1,300), `Block` (400) and
`Identifier_Type` (2,400 in 16.0.0, and 5,200 in the later versions).
The value of a decimal digit is a lookup in a tree map.
The operations on lists of ranges take time proportional to the product of
the lengths of the two lists; `general-category-changes`, which uses them
on the ranges of each of the thirty values, takes well under a second.
The normalization functions are meant for identifiers and the like: they are
not tail recursive, and reordering a run of *n* combining marks takes time
quadratic in *n*.

Certifying all the 103 books from scratch, the tests and the generated
tables included, took about three and a half minutes with two jobs
(`cert.pl -j 2`, SBCL).  The slowest books are `quick-check-theorems` (31
seconds), `script-tables` (29 seconds: the type of the scripts is a tagged
sum with 179 cases) and `normalization-across-versions` (22 seconds).

## License

The books and tools are under the 3-clause BSD license of ACL2.  The tables
in `data/` are derived from the Unicode Character Database, which is
Copyright © Unicode, Inc. and is distributed under the Unicode License V3
(`Unicode-3.0`), a permissive license that requires its notice to accompany
copies of the data; the notice is in the file `LICENSE-UNICODE`.
