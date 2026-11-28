# Unicode Library

An ACL2 model of the parts of the Unicode Standard that the lexers of
programming languages need: code points, the identifier and white space
properties, normalization, scripts, the bidirectional classes and controls,
the bidirectional algorithm, the properties that say which characters are
safe in identifiers, the detection of strings that look alike or that
mix scripts, and the names of the characters with their aliases.  It is a
shared library: nothing in it is specific to one language.

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
- A prototype is the sequence of characters that stands for what a
  character looks like, in the data of UTS #39; a skeleton is what a
  string becomes when its characters are replaced by their prototypes.
  Two strings are confusable when they have the same skeleton.  The
  specification writes `internalSkeleton` for the skeleton that does not
  look at the order of display, and `bidiSkeleton` for the one that does.
- `Hanb`, `Hntl`, `Jpan` and `Kore` are the codes, in ISO 15924, of four
  writing systems that use several scripts: Han with Bopomofo,
  traditional Han with Latin, Japanese and Korean.  They are not values
  of the `Script` property; UTS #39 adds them to the sets of scripts that
  it compares.
- An embedding level, or level, is the number that the Unicode
  Bidirectional Algorithm gives to each character: text at an even level
  is displayed from left to right, text at an odd level from right to
  left.  The rules of the algorithm have short names in UAX #9: `P1` to
  `P3` (paragraphs), `X1` to `X10` (explicit formatting characters), `W1`
  to `W7` (weak types, that is, numbers), `N0` to `N2` (neutral types,
  that is, brackets, spaces and punctuation), `I1` and `I2` (implicit
  levels), `L1` to `L4` (lines and reordering).  `sos` and `eos` are the
  directions assumed before the start and after the end of a sequence of
  characters.  An isolate is a stretch of text that the characters
  `LRI`, `RLI` or `FSI` open and `PDI` closes, and that the text around
  it treats as one neutral character.
- UAX: Unicode Standard Annex.  UAX #9 is the Unicode Bidirectional
  Algorithm, UAX #15 is Unicode Normalization Forms, UAX #24 is Unicode
  Script Property, UAX #31 is Unicode Identifiers and Syntax, UAX #44 is
  the Unicode Character Database.  UTS: Unicode Technical Standard.
  UTS #39 is Unicode Security Mechanisms, UTS #51 is Unicode Emoji, and
  UTS #55 is Unicode Source Code Handling.
- A chunk of an identifier is one of the words that its letter case and
  its punctuation make visible: `dromedaryCamel` has the chunks
  `dromedary` and `Camel`, and `snake_case` has `snake`, `_` and `case`
  (UTS #55, Section 5.1.2.1).
- A Hangul syllable is a character of the Korean alphabet, Hangul, that
  stands for a whole syllable.  It is made of two or three letters, which
  are called jamo: a leading consonant, a vowel and, in some syllables, a
  trailing consonant.  The Unicode Standard writes L, V and T for the
  three.  `Jamo_Short_Name` is the property that gives each of those
  letters a short name in Latin letters, such as `G` or `WI`.
- NR1 to NR4 are the numbers of the four rules of the Unicode Standard,
  Section 4.8, that say what the name of a code point is.  UAX44-LM2 is
  the number of the rule of UAX #44, Section 5.9.2, for the loose matching
  of names: the rule that says which differences between two strings do
  not count when the strings are compared as names.
- UCD: Unicode Character Database.

## What is here

| Book | Contents |
|------|----------|
| `code-points` | Code points and scalar values, as natural numbers (never ACL2 characters). Surrogates are code points but not scalar values.  The types of their lists, and of lists of lists of code points. |
| `versions` | The supported versions of Unicode, as a type, and the order in which they were released (`version<=`). |
| `general-category` | `General_Category`: `code-point-general-category`, the ranges of the code points that have a value (`general-category-ranges`), and `assigned-p`. |
| `general-category-changes` | The code points whose `General_Category` is not the same in two versions (`general-category-changes`), and those of them that are assigned in the first version (`general-category-changes-of-assigned`), as lists of ranges; the proof that in the supported versions the `General_Category` of an assigned code point is the same in every later version, with one exception, U+0295. |
| `xid` | `XID_Start` and `XID_Continue`, and the XID identifiers (the default identifiers of UAX #31); the two optional characters for the start of an identifier, `$` and `_`. |
| `id` | `ID_Start`, `ID_Continue`, `Other_ID_Start` and `Other_ID_Continue`; the exact difference between the `ID` and the `XID` properties (23 and 19 code points); a code point that has `ID_Start` or `ID_Continue` has it in every later version. |
| `id-compat-math` | `ID_Compat_Math_Start` and `ID_Compat_Math_Continue`, the characters of the mathematical notation profile of UAX #31. |
| `scripts` | `Script` (`code-point-script`) and `Script_Extensions` (`code-point-script-extensions`), with the ranges of the code points of a script and of those whose script extensions contain it; the proof that the script extensions contain the script, unless it is `Common` or `Inherited`. |
| `identifier-status` | `Identifier_Status` (`identifier-allowed-p`) and `Identifier_Type` (`code-point-identifier-types`) of UTS #39, with the proof that a code point is allowed exactly when all its types are `Inclusion` or `Recommended`. |
| `identifier-status-normalization` | The proof that NFKC changes no allowed code point, and changes every code point that has the type `Not_NFKC`. |
| `confusables` | The prototypes of confusable characters (`prototype`), from the data of UTS #39, with the proof that each code point of a prototype is its own prototype. |
| `skeleton` | The internal skeleton of a string (`internal-skeleton`): NFD, removal of the default ignorable code points, prototypes, NFD.  The proof that taking it twice is the same as taking it once in 18.0.0, and in 16.0.0 and 17.0.0 except for thirteen code points.  The skeleton (`skeleton`) and the confusable strings (`confusable-p`), for the lists that have no code point that starts right-to-left text; this book does not load the bidirectional algorithm. |
| `bidi-skeleton` | The bidirectional skeleton of a string, for every list of code points and each direction of the paragraph (`bidi-skeleton`), and the strings that are confusable for a direction (`bidi-confusable-p`).  The proof that `skeleton` and `confusable-p` agree with them on the lists that satisfy their guard. |
| `confusable-kinds` | The three classes of confusable strings: single-script, mixed-script and whole-script confusables. |
| `mixed-scripts` | Mixed-script detection: the augmented script set of a code point, the resolved script set of a list (`resolved-script-set`), and whether a list is single-script (`single-script-p`). |
| `mixed-numbers` | Mixed-number detection: whether a list has decimal digits of more than one system (`mixed-number-systems-p`). |
| `identifier-chunks` | The identifier word boundaries of UTS #55 (`identifier-word-boundary-p`) and the chunks of an identifier (`identifier-chunks`), with the proofs that the chunks put together are the identifier and that no chunk is empty. |
| `pattern-white-space` | `Pattern_White_Space`. |
| `white-space` | `White_Space` (`white-space-p`): the spaces and line separators of ordinary text, which is another set than `Pattern_White_Space`. |
| `pattern-syntax` | `Pattern_Syntax`. |
| `bidi-controls` | `Bidi_Control`, and the explicit directional formatting characters with their `Bidi_Class`. |
| `bidi-class` | `Bidi_Class` in full (`code-point-bidi-class`), and the proof that it agrees with the table of the explicit formatting classes of `bidi-controls`. |
| `bidi-brackets` | `Bidi_Paired_Bracket_Type` and `Bidi_Paired_Bracket` (`code-point-bidi-bracket`), with the proof that each paired bracket is the partner of its partner. |
| `bidi-mirroring` | `Bidi_Mirroring_Glyph` (`code-point-bidi-mirroring-glyph`), with the proofs that the mirroring glyph of a mirroring glyph is the first code point, that the partner of a paired bracket is its mirroring glyph, and that a mirroring glyph is a scalar value. |
| `bidirectional-algorithm` | The Unicode Bidirectional Algorithm of UAX #9: the resolved levels of a list of code points (`bidi-levels`), the order in which it is displayed (`bidi-display-order`), and the whole text as it is displayed (`bidi-display`).  It loads the seven books of the rules and the five books of theorems, below. |
| `bidi-characters` | What the algorithm looks at in a character (the type `bidi-char`), the direction of a paragraph, and rules P2 and P3.  The proof that every paired bracket has the class `ON`. |
| `bidi-explicit-levels` | Rules X1 to X8: the levels and the overrides that the explicit formatting characters give. |
| `bidi-weak-types` | Rules W1 to W7. |
| `bidi-neutral-types` | The bracket pairs of UAX #9 (BD16) and rules N0 to N2. |
| `bidi-resolved-levels` | Rules X9 and X10 (the isolating run sequences), I1, I2 and L1: the resolved levels of a paragraph (`bidi-paragraph-levels`). |
| `bidi-reordering` | Rules P1 and L2, and the functions `bidi-levels` and `bidi-display-order` on lists of code points. |
| `bidi-display` | The whole text as it is displayed, with the characters that rule X9 removes (UAX #9, Section 5.2), rule L3 and rule L4: the characters in the order of display with their levels (`bidi-arrange`), and the code points after mirroring (`bidi-display`).  The proofs that the text is only rearranged before rule L4, and that it keeps its length. |
| `bidi-rearrangement` | The proof that the order of display is a permutation of the positions of the characters that have a level. |
| `right-to-left-free` | The code points that can make text be displayed from right to left (`right-to-left-code-point-p`), and the lists that have none (`right-to-left-free-p`).  It loads only `bidi-class`. |
| `bidi-left-to-right` | The proofs that a list that satisfies `right-to-left-free-p`, in a paragraph that is not set from right to left, gets only even levels and is displayed as it is stored.  And the proof that a paragraph in which no level is odd is displayed as it is stored, whatever the levels are. |
| `bidi-confinement` | Confinement: a clean cut of a text (`bidi-clean-cut-p`), a text cut into segments whose cuts are all clean (`bidi-confined-p`), and the proofs that such a text is displayed segment by segment and that the two parts of a paragraph joined at a clean cut are each put in the order that they have with their own levels.  Conditions on the segments, on the bidirectional classes and the bracket pairs only, under which a plain text is confined (`bidi-guarded-segments-p`, `bidi-plain-p`). |
| `bidi-guarded-theorem` | The proof that those conditions are enough: a plain text whose segments are guarded is confined (`bidi-confined-p-when-bidi-guarded-segments-p`). |
| `bidi-self-contained` | Two more conditions, on the bracket pairs of the text, under which each segment of a plain text is displayed as it is alone (`bidi-self-contained-segments-p`), and the proof: in a paragraph from left to right, the levels are those of each segment alone, and the display is the display of each segment, one after the other. |
| `bidi-guarded-plain`, `bidi-guarded-weak`, `bidi-guarded-brackets`, `bidi-guarded-neutral` | The steps of those two proofs, which `bidi-guarded-theorem` and `bidi-self-contained` include locally: a plain text is one isolating run sequence, at any paragraph embedding level, and what rule L1 does in it; the invariant of the first proof and rules W1 to W7; facts about the bracket pairs; rules N0 to N2, I1 and I2; and, for the second proof, that each rule does in a stretch of a text what it does to the stretch alone.  Their definitions are for the proofs only; they have comments and no documentation topics, and `top` does not load them. |
| `bidi-rule` | The Bidi Rule for a label of a domain name (RFC 5893, Section 2, which UTS #46 applies with its option `CheckBidi`), as it is written: `bidi-rule-p` for a label and `bidi-rule-domain-name-p` for a domain name.  And two rules derived from it, which are of this library and not of a specification: a strict one (`bidi-rule-strict-p`), and a wide one for names that may begin or end with punctuation (`bidi-rule-wide-p`).  The predicates look only at `Bidi_Class` and `Bidi_Paired_Bracket_Type`, and the book does not load the algorithm.  With the proofs that the two ways in which the RFC says what a right-to-left label is agree under the rule, that a left-to-right label or name has no right-to-left character, and that the wide rule extends the strict one.  That the wide rule keeps two names from being displayed alike in a paragraph from left to right, and that the strict rule does in paragraphs of any direction, are proved in the books of the next rows. |
| `bidi-rule-display` | How a name that satisfies the wide rule is displayed in a paragraph from left to right, computed without the rules of the algorithm (`bidi-name-display`): the name has three parts, the middle one goes from its first right-to-left letter to its last letter, digit or closing bracket of a pair with a letter or digit inside, and its clusters (a character with the marks after it) are displayed from right to left except that each number keeps its order.  And the way back from a display to the name (`bidi-name-read`), with the proof that it undoes the first function for every name that satisfies the wide rule, so that this display is different for different names.  The book also has the levels of such a name, computed in the same way (`bidi-name-levels`).  It loads the rules of the algorithm up to the bracket pairs, not the rest. |
| `bidi-rule-display-weak` | The classes that rules W1 to W7 give to the characters of a name that satisfies the wide rule and has a right-to-left letter or an Arabic digit, in a paragraph from left to right, computed cluster by cluster without those rules (`bidi-clusters-weak-classes`), and the proof that the rules give them.  They give the same classes in a paragraph from right to left when the name does not start with a mark; that is proved too. |
| `bidi-rule-display-levels` | The proof that the algorithm gives such a name the levels of `bidi-name-levels`: rule N0 on the bracket pairs, rules N1 and N2, the implicit levels and rule L1, after the weak rules of the row above.  It uses a theorem of `bidi-guarded-brackets`: no two bracket pairs cross.  And the proof that in a paragraph from right to left such a name, when it does not start with a mark, gets the levels of `bidi-middle-levels` for the whole name: no character has level 0. |
| `bidi-rule-display-order` | The proof that, with those levels, rules L2 to L4 give the display of `bidi-name-display`. |
| `bidi-mark-class` | A fact about the data for that proof, checked for each version by computing with lists of ranges: a code point whose class is not `L` is a combining mark for rule L3 exactly when its class is `NSM`. |
| `bidi-rule-left-to-right-label` | The proof that a left-to-right label that satisfies the strict rule gets level 2 for each of its characters in a paragraph from right to left. |
| `bidi-rule-display-theorem` | The theorems that the rows above lead to.  In a paragraph from left to right, the algorithm displays a name that satisfies the wide rule as `bidi-name-display` says, and no two such names are displayed alike.  In a paragraph of any direction, the algorithm displays a label that satisfies the strict rule as `bidi-name-display` says, and no two such labels are displayed alike. |
| `emoji` | `Emoji`, `Emoji_Presentation`, `Emoji_Modifier`, `Emoji_Modifier_Base`, `Emoji_Component`, `Extended_Pictographic` and `Regional_Indicator`, with how they contain each other. |
| `decimal-digits` | The decimal digits and their values (`decimal-digit-value`), with the proof that the digits of a system are ten consecutive code points with the values 0 to 9. |
| `blocks` | `Block` (`code-point-block`), with the proof that a block is one range and that a block of a version is the same block in every later version. |
| `names` | `Name` (`code-point-name`): the names that are listed one by one, the names of the Hangul syllables, which are made from `Jamo_Short_Name`, and the names that end in the code point.  The code point with a given name (`name-code-point`).  The loose matching of names of UAX #44 (`name-loose-key`, `loose-name-code-point`).  The proofs that the two functions between code points and names undo each other, that no two names match loosely, that a name is made of capital letters, digits, spaces and hyphens, that the code points without a name are those whose `General_Category` is `Cc`, `Cs`, `Co` or `Cn`, and that a name is the same in every later version. |
| `name-aliases` | `Name_Alias` (`code-point-name-aliases`): the aliases of the names, each with its type, which is one of correction, control, alternate, figment and abbreviation.  The code point of which a string is an alias (`name-alias-code-point`), or the name or an alias (`name-or-alias-code-point`), and the same by loose matching (`loose-name-alias-code-point`, `loose-name-or-alias-code-point`).  The proofs that an alias gives its code point back, that no alias matches a name or another alias loosely, that an alias is written like a name, and that an alias of a version is an alias in every later version. |
| `code-point-types` | The seven basic types of code points of the Unicode Standard (`code-point-basic-type`): graphic, format, control, private-use, surrogate, noncharacter and reserved; and the code points of a type as a list of ranges (`basic-type-ranges`).  The proofs of which code points are the control codes, the private-use code points, the surrogates and the noncharacters, and that a code point that is not reserved has the same type in every later version. |
| `code-point-labels` | The labels of the code points that have no name, such as `control-0009` (`code-point-label`); a name or a label for every code point (`code-point-name-or-label`); and the code point that has a label (`label-code-point`, `loose-label-code-point`).  The proofs that every code point has a name or a label and not both, that a label gives its code point back, that no label matches a name or an alias loosely, and that no two code points have the same name or label. |
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
| `maps` | The fixtypes of the tree maps from code points to values, which represent the properties with a default value: combining classes, decompositions, the classes of the explicit formatting characters, the values of the decimal digits, and the prototypes of confusable characters. |
| `runs` | The macro `defruns`, which introduces, for a property with many values, the fixtype of runs of code points with the same value, the lookup, the ranges of a value (or, when the values are sets, of the code points whose set has an element), and the theorems that relate them. |
| `general-category-tables` | The fixtype of the thirty values of `General_Category`, the list of the thirty values (`general-category-values`), and the runs of that property. |
| `script-tables` | The fixtype of the scripts, defined from one table of their codes and names (`*script-table*`); the runs of `Script` and of `Script_Extensions`. |
| `bidi-class-tables` | The fixtype of the twenty-three values of `Bidi_Class`, with the predicates for the strong, weak, neutral and explicit formatting classes; the runs of that property. |
| `block-tables` | The runs of `Block`, whose values are the names of the blocks, as strings. |
| `identifier-type-tables` | The fixtype of the twelve values of `Identifier_Type`, and the runs of that property, whose values are lists of types. |
| `name-tables` | The fixtypes of the tables of the names: the tree maps from code points to names, the patterns of the names that end in the code point, and the tree maps from the keys of loose matching to code points.  The fixtypes of the aliases of the names, of their types, and of the tree maps from code points to lists of aliases. |
| `coverage` | Documentation only: what the library models of each Unicode specification, what it does not, and for which programming languages that is enough. |
| `top` | All of the above, and the overview topics of the documentation. |
| `data/v<version>/` | **Generated** tables, one book per file of the Unicode Character Database, and three books from the data files of UTS #39. |
| `data/bidi/` | **Generated**: the two conformance files of the bidirectional algorithm, which are the same for all the supported versions. |
| `data/names/` | **Generated**: the names of the Hangul syllables as `DerivedName.txt` lists them, which are the same for all the supported versions.  Only a test loads it. |
| `tests/` | Tests that run when certified, including the whole of `NormalizationTest.txt`, `BidiTest.txt` and `BidiCharacterTest.txt`. |
| `tools/` | The generator of the data books, and the pinned SHA-256 of its inputs. |
| `validation/` | Tools to compare the library, on every code point, with other implementations, and to compare the displayed text of random strings with ICU. |

What is not modeled is listed, specification by specification, in the
documentation topic `unicode-coverage` (book `coverage`).  Among other
things: case mappings, text segmentation, emoji sequences, the names
of sequences of characters, and collation.  That topic is also the
only place where the library names programming languages: it says, for C,
Java, Python, Rust, Scheme and Remora, whether the library has all that
their lexical rules take from Unicode.

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
- `white-space-p-alt-def`: `White_Space` is the same twenty-five code
  points in every supported version.
  `white-space-p-when-pattern-white-space-p`: a code point with
  `Pattern_White_Space` has `White_Space`, unless it is U+200E or U+200F.
  `white-space-p-in-terms-of-general-category`: the code points with
  `White_Space` are those whose `General_Category` is `Zs`, `Zl` or `Zp`,
  with U+0009 to U+000D and U+0085.
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
- `code-point-bidi-bracket-of-partner-when-open`,
  `code-point-bidi-bracket-of-partner-when-close`: the partner of an
  opening paired bracket is a closing paired bracket whose partner is the
  first one, and the other way round.
  `code-point-bidi-mirroring-glyph-of-code-point-bidi-mirroring-glyph`:
  the mirroring glyph of a mirroring glyph is the first code point.
  `code-point-bidi-mirroring-glyph-when-bracket`: the partner of a paired
  bracket is its mirroring glyph.
  `scalar-value-p-of-code-point-bidi-mirroring-glyph`: a mirroring glyph
  is not a surrogate.
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

About confusable strings and mixed scripts (UTS #39):

- `own-prototype-listp-of-prototype`,
  `replace-by-prototypes-of-replace-by-prototypes`: each code point of a
  prototype is its own prototype, so replacing code points by their
  prototypes a second time changes nothing.
- `internal-skeleton-of-nfc`, `internal-skeleton-of-nfd`,
  `internal-skeleton-when-canonical-equivalent-p`: a list, its NFC form
  and its NFD form have the same internal skeleton, and so do canonical
  equivalents.  `nfd-memberp-of-internal-skeleton`: the internal skeleton
  is in NFD.
- `internal-skeleton-of-internal-skeleton-from-v18.0.0`: from Unicode
  18.0.0 on, the internal skeleton of the internal skeleton of a list is
  the internal skeleton of the list, as the specification says.
- `internal-skeleton-of-internal-skeleton`: in every version, that holds
  for a list that has none of the code points of
  `internal-skeleton-unstable-code-points`, of which there are thirteen in
  16.0.0 and 17.0.0 and none in 18.0.0.
  `internal-skeleton-of-internal-skeleton-when-unstable`: it fails for
  each of the thirteen.  So in 16.0.0 and 17.0.0 the data does not do what
  the specification says of it; the documentation topic
  `skeleton-idempotence` has an example.
- `confusable-p-reflexive`, `confusable-p-symmetric`,
  `confusable-p-transitive`: being confusable is an equivalence relation.

About the chunks of an identifier (UTS #55):

- `flatten-of-identifier-chunks`: the chunks of a list, put together in
  order, are the list.  `not-member-equal-of-nil-and-identifier-chunks`:
  no chunk is empty.  `consp-of-identifier-chunks`: a list has a chunk
  exactly when it is not empty.
- `script-extensions-of-titlecase-letter`: the `Script_Extensions` of a
  titlecase letter is its `Script` alone.  The specification writes
  `\p{Grek}` for the Greek titlecase letters, which could be read as
  either property; by this theorem the two readings are the same.
  `confusable-p-when-canonical-equivalent-p`: canonical equivalents are
  confusable.
- `confusable-p-in-terms-of-kinds`,
  `not-mixed-script-confusable-p-when-single-script-confusable-p`,
  `mixed-script-confusable-p-when-whole-script-confusable-p`: confusable
  strings are single-script confusables or mixed-script confusables, not
  both, and whole-script confusables are mixed-script confusables.
- `resolved-script-set-of-append`: the resolved script set of two lists
  put together is the intersection of their resolved script sets.
  `mixed-script-p-of-append-when-mixed-script-p-left` (and `-right`): a
  list with a mixed-script part is mixed-script.
  `not-script-set-empty-p-of-code-point-augmented-script-set`: a single
  code point is never mixed-script.

About the Unicode Bidirectional Algorithm.  What says that the
definitions are right is the conformance tests (see "Validation"); these
theorems are about what the algorithm does:

- `perm-of-bidi-display-order` (and `perm-of-bidi-order-of-levels`,
  `perm-of-bidi-paragraph-order`): the order of display is a permutation
  of the positions of the characters that have a level, and
  `no-duplicatesp-equal-of-bidi-positions-with-level`: no position is
  there twice.  So each such character is displayed exactly once.  The
  relation is `perm` of `kestrel/lists-light/perm`.
- `perm-of-bidi-arrange`: the code points of the text in the order of
  display, with every character kept, after rules L2 and L3, are a
  permutation of the code points of the text.  `len-of-bidi-display`:
  rule L4 then replaces code points in place, so the displayed text has
  the length of the text.  `scalar-value-listp-of-bidi-display`: a list of
  scalar values is displayed as a list of scalar values.
- `bidi-levels-even-p-of-bidi-levels-when-right-to-left-free-p`,
  `bidi-display-order-when-right-to-left-free-p`,
  `bidi-display-when-right-to-left-free-p`: a list that satisfies
  `right-to-left-free-p` (no code point of class `R`, `AL`, `AN`, `RLE`,
  `RLO` or `RLI`), in a paragraph from left to right or whose direction is
  that of its first strong character, gets only even levels; its order of
  display is the stored order; and `bidi-display` returns it unchanged.
  The condition looks only at the `Bidi_Class` of each code point.  A list
  of code points below U+0590, where the Hebrew block starts, satisfies
  it (`right-to-left-free-p-when-all-below-590`).
- `perm-of-take-of-bidi-arrange-paragraph-when-bidi-clean-cut-p`: in a
  paragraph from left to right, if the character before a place of the
  text or the character after it has level 0 (a clean cut,
  `bidi-clean-cut-p`), then the characters displayed to the left of that
  place are the characters stored before it, in another order.  So rules
  L2 and L3 move no character across a clean cut.
- `perm-of-take-of-bidi-arrange-paragraph-when-bidi-confined-p`: a text
  cut into segments is confined (`bidi-confined-p`) when the cuts between
  its segments are all clean.  A confined text is displayed segment by
  segment: for every k, the display begins with the characters of the
  first k segments, in another order.
- `bidi-confined-p-when-bidi-guarded-segments-p`: a plain text whose
  segments are guarded (`bidi-plain-p`, `bidi-guarded-segments-p`) is
  confined.  A plain text has no paragraph separator, no explicit
  directional formatting character and no character that rule X9
  removes.  The predicate states three conditions on each segment that
  has a character of class `R`, `AL` or `AN`: after it, the first
  character of class `L`, `R`, `AL`, `EN` or `AN` is of class `L`; the
  character right after it is not of class `ET` or `NSM`; and no bracket
  pair opens inside it and closes after it.  They look only at the
  `Bidi_Class` of each code point and at the bracket pairs, so they can
  be checked without running the algorithm.  The proof follows the
  algorithm rule by rule; each condition is needed (see "Tests").
  `perm-of-take-of-bidi-arrange-paragraph-when-bidi-guarded-segments-p`
  puts this together with the theorem before: such a text is displayed
  segment by segment.
- `bidi-arrange-with-levels-of-append-when-bidi-clean-cut-p`: the two
  parts of a paragraph joined at a clean cut are each put in the order of
  display that they have with their own levels.  Rules L2 and L3 do in
  each part what they would do if the part were a paragraph with the same
  levels (`bidi-arrange-with-levels` is the order of display of some code
  points with given levels).
- `bidi-paragraph-all-levels-when-bidi-self-contained-segments-p` and
  `bidi-display-when-bidi-self-contained-segments-p`: in a plain text
  whose segments are self-contained (`bidi-self-contained-segments-p`),
  in a paragraph from left to right, each segment is displayed as it is
  alone.  Each character has the level that it has when its segment is a
  paragraph from left to right of its own
  (`bidi-levels-of-each-segment`), and `bidi-display` of the text is
  `bidi-display` of the first segment, followed by that of the second
  segment, and so on (`bidi-display-of-each-segment`).  The segments are
  self-contained if they are guarded and two more conditions hold.  No
  bracket pair of the text closes inside a segment that has a character
  of class `R`, `AL` or `AN` after opening before that segment
  (`bidi-bracket-pairs-opened-p`).  And the search for the bracket pairs
  of the text does not give up (`bidi-bracket-pairs-overflow-p`), which
  it does when it meets an opening bracket while 63 opening brackets
  already wait for their closing brackets (UAX #9, BD16); the text then
  has no bracket pair, while a segment alone could have some.  Both
  conditions can be checked without running the algorithm, and each is
  needed (see "Tests").
- `code-point-bidi-class-when-code-point-bidi-bracket`: every paired
  bracket has the class `ON`, as `BidiBrackets.txt` says the stability
  policy guarantees; checked on every code point, for each version.

About the Bidi Rule (RFC 5893, Section 2) and the two rules derived from
it:

- `bidi-right-to-left-label-p-when-bidi-rule-p`: the RFC says in two ways
  which labels are right-to-left labels, by the first character (in the
  first condition of the rule) and by the characters of the whole label
  (in its terminology).  For a label that satisfies the rule the two
  agree: the label has a character of class `R`, `AL` or `AN` exactly
  when its first character is not of class `L`.
- `right-to-left-free-p-when-bidi-rule-p`,
  `right-to-left-free-p-when-bidi-rule-wide-p`: a left-to-right label
  that satisfies the Bidi Rule, and a left-to-right name that satisfies
  the wide rule, satisfy `right-to-left-free-p`.  So, by
  `bidi-display-when-right-to-left-free-p`, they are displayed as they
  are stored when the paragraph is not set from right to left.
- `bidi-rule-wide-p-when-bidi-rule-strict-p`: a label that satisfies the
  strict rule satisfies the wide rule.
- `bidi-name-read-of-bidi-name-display`: for a name that satisfies the
  wide rule, `bidi-name-read` gives the name back from what
  `bidi-name-display` gives for it.  `bidi-name-display` says how such a
  name is displayed in a paragraph from left to right without going
  through the rules of the algorithm.  The proof uses two conditions of
  the rule: no digit and no paired bracket before the first right-to-left
  letter, and not both European and Arabic digits.
- `bidi-name-display-is-one-to-one`: so two names that satisfy the wide
  rule and for which `bidi-name-display` gives the same list are the same
  name.
- `bidi-display-when-bidi-rule-wide-p`: in a paragraph from left to
  right, the Unicode Bidirectional Algorithm displays a name that
  satisfies the wide rule as `bidi-name-display` says.  The name is the
  whole paragraph.  The proof goes through the rules of the algorithm:
  `bidi-resolve-weak-types-when-bidi-rule-wide-p` for the classes after
  rules W1 to W7, `bidi-paragraph-all-levels-when-bidi-rule-wide-p` for
  the levels, and
  `bidi-mirror-chars-of-bidi-arrange-with-levels-of-bidi-name-levels`
  for rules L2 to L4 on those levels.
- `bidi-display-is-one-to-one-when-bidi-rule-wide-p`: so two names that
  satisfy the wide rule and that the algorithm displays alike, in a
  paragraph from left to right, are the same name.
- `bidi-resolve-weak-types-when-bidi-rule-wide-p-after-right-to-left`,
  `bidi-paragraph-all-levels-at-level-1-when-bidi-rule-wide-p`: in a
  paragraph from right to left, a right-to-left name that satisfies the
  wide rule and does not start with a mark gets the same classes from
  rules W1 to W7 as in a paragraph from left to right, and the levels of
  `bidi-middle-levels` for the whole name.  No character has level 0.
- `bidi-paragraph-all-levels-at-level-1-when-left-to-right-label`: in a
  paragraph from right to left, a left-to-right label that satisfies the
  strict rule gets level 2 for each of its characters.
- `bidi-mirror-chars-of-bidi-arrange-with-levels-when-even`: a paragraph
  in which no level is odd is displayed as it is stored.
- `bidi-paragraph-all-levels-at-level-1-when-bidi-rule-strict-p`: a
  right-to-left label that satisfies the strict rule gets the levels of
  `bidi-name-levels` in a paragraph from right to left, the same as in a
  paragraph from left to right.
- `bidi-display-when-bidi-rule-strict-p`: the algorithm displays a label
  that satisfies the strict rule as `bidi-name-display` says, whatever
  the direction of the paragraph: from left to right, from right to left,
  or taken from the first strong character.  The label is the whole
  paragraph.
- `bidi-display-is-one-to-one-when-bidi-rule-strict-p`: so two labels
  that satisfy the strict rule and that the algorithm displays alike are
  the same label.  The two labels can be in paragraphs of different
  directions.
- `bidi-pairs-nested-p-of-bidi-bracket-pairs`: no two of the bracket
  pairs that `bidi-bracket-pairs` finds cross, and the pairs are in the
  order of their opening brackets.  The proof above needs it for rule N0.
- `bidi-combining-mark-p-when-not-left-to-right`: a code point whose
  class is not `L` is a combining mark for rule L3 exactly when its class
  is `NSM`; checked for each version, by computing with lists of ranges.
- `code-point-bidi-class-when-code-point-bidi-mirroring-glyph`: a code
  point that has a mirroring glyph has the class `ON`; checked on every
  code point, for each version.  With it, replacing a code point by its
  mirroring glyph keeps its class, twice gives the code point back, and a
  paired bracket stays one.
- What does not hold.  The Bidi Rule as it is written does not keep two
  labels from being displayed alike: the tests have two labels with a
  character of class `ET`, and two with a character of class `BN`, that
  satisfy it and are displayed alike.  The wide rule does not in a
  paragraph from right to left: the tests have two names that satisfy it
  and are displayed alike there, one of which starts with a mark.  The
  documentation topic `bidi-rule-proof-outline` says how the proofs for the
  wide rule and for the strict rule go: a function reads a name back from
  its display, the algorithm is proved to give that display, and for the
  strict rule the display is proved to be the same in every direction.

About the bidirectional skeleton:

- `bidi-skeleton-when-right-to-left-free-p`,
  `bidi-confusable-p-when-right-to-left-free-p`: for the lists that
  satisfy `right-to-left-free-p`, and a direction that is not from right
  to left, the bidirectional skeleton is `skeleton`, which is the internal
  skeleton, and `bidi-confusable-p` is `confusable-p`.  So `skeleton` and
  `confusable-p`, whose guard is that condition, are the functions of the
  specification on their guard, and they do not need the algorithm; for
  any other list, the skeleton of the specification is `(bidi-skeleton cps
  (paragraph-direction-left-to-right) ver)`.
- `nfd-memberp-of-bidi-skeleton`, `scalar-value-listp-of-bidi-skeleton`;
  `bidi-confusable-p-reflexive`, `-symmetric`, `-transitive`.
- The specification states the condition of the first theorem with the
  classes `R` and `AL` only (UTS #39, Section 4, "a fast path").  That is
  not enough, and the tests have a counterexample for each of the four
  other classes: U+0661, a space and U+0662 (class `AN`, the Arabic-Indic
  digits) are displayed with U+0662 first; after U+202E RIGHT-TO-LEFT
  OVERRIDE (class `RLO`) the letters a, b are displayed as b, a; and after
  U+202B RIGHT-TO-LEFT EMBEDDING (class `RLE`) or U+2067 RIGHT-TO-LEFT
  ISOLATE (class `RLI`), an exclamation mark and a question mark are
  displayed with the question mark first.  None of these lists has a
  character of class `R` or `AL`, and for each the bidirectional skeleton
  is not the internal skeleton.
- The three classes of confusable strings (`confusable-kinds`) are
  defined with `confusable-p`, so only for the lists that satisfy its
  guard.
- `name-code-point-of-code-point-name`,
  `code-point-name-of-name-code-point`: the name of a code point gives the
  code point back, and the code point with a name has that name.
  `loose-name-code-point-of-code-point-name` is the first of the two for
  loose matching.
- `code-points-equal-when-names-match-loosely`: two code points whose
  names match loosely (UAX #44, rule UAX44-LM2) are the same code point.
  So no two code points have the same name
  (`code-points-equal-when-names-equal`).
- `name-char-listp-of-code-point-name`: a name is made of capital letters,
  digits, spaces and hyphens.
- `code-point-name-is-empty-in-terms-of-general-category`: the code
  points without a name are those whose `General_Category` is `Cc`, `Cs`,
  `Co` or `Cn`, that is, the control codes, the surrogates, the private
  use code points and the code points that are not assigned.
- `name-alias-code-point-when-member-of-code-point-name-aliases`: an
  alias of a code point gives the code point back.  The theorems about
  an alias of a code point are stated for a member of the list that
  `code-point-name-aliases` gives.
  `find-name-alias-of-name-alias-code-point` is the other direction: the
  code point found for a string has the string as an alias.
- `code-points-equal-when-aliases-match-loosely`: two code points that
  have aliases that match loosely are the same code point.
- `not-loose-name-code-point-when-member-of-code-point-name-aliases`,
  `not-loose-name-alias-code-point-of-code-point-name`: no alias matches
  a name loosely, and no name matches an alias.  So
  `name-or-alias-code-point` and `loose-name-or-alias-code-point` give
  the code point back from its name and from each of its aliases
  (`name-or-alias-code-point-of-code-point-name`,
  `name-or-alias-code-point-when-member-of-code-point-name-aliases`, and
  the two for loose matching).
- `name-char-listp-of-name-alias->name-when-member`: an alias is made of
  capital letters, digits, spaces and hyphens.
- `code-point-basic-type-is-control`,
  `code-point-basic-type-is-private-use`,
  `code-point-basic-type-is-surrogate`,
  `code-point-basic-type-is-noncharacter`: the control codes are U+0000
  to U+001F and U+007F to U+009F; the private-use code points are
  U+E000 to U+F8FF, U+F0000 to U+FFFFD and U+100000 to U+10FFFD; the
  surrogates are those of `surrogate-p`; the noncharacters are those of
  `noncharacter-p`.  `assigned-p-in-terms-of-basic-type`: a code point is
  assigned exactly when it is neither a noncharacter nor reserved.
  `code-point-in-basic-type-ranges`: the ranges of a type are the code
  points that have the type.
- `code-point-label-is-empty`: the label of a code point is the empty
  string exactly when its name is not, so every code point has a name or
  a label and not both.
  `code-point-name-is-empty-in-terms-of-basic-type`,
  `code-point-label-is-empty-in-terms-of-basic-type`: the code points
  with a name are the graphic and format ones.
- `label-code-point-of-code-point-label`,
  `code-point-label-of-label-code-point`: the label of a code point gives
  the code point back, and the code point with a label has that label.
- `not-loose-name-code-point-of-code-point-label`,
  `not-loose-name-alias-code-point-of-code-point-label`,
  `not-loose-label-code-point-of-code-point-name`,
  `not-loose-label-code-point-when-member-of-code-point-name-aliases`: no
  label matches a name or an alias loosely, and no name or alias matches
  a label.
- `code-points-equal-when-names-or-labels-match-loosely`: two code
  points for which `code-point-name-or-label` gives strings that match
  loosely are the same code point.

And about two versions, besides the theorems listed further up:
`stream-safe-p-of-later-version`, `stream-safe-process-of-later-version`
(text of assigned characters stays in Stream-Safe Text Format, and the
process gives the same result), `nfc-quick-check-of-later-version`
(and the other three: the quick check values of an assigned code point
stay the same), `code-point-name-of-later-version` (a code point that
has a name has the same name in every later version),
`code-point-name-aliases-of-later-version` (an alias of a code point is
an alias of it in every later version),
`code-point-basic-type-of-later-version` (a code point that is not
reserved has the same basic type in every later version), and
`code-point-label-of-later-version` (such a code point has the same
label, or no label, in every later version).

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
| `code-point-name`, `name-code-point`, `loose-name-code-point`, `name-loose-key`, `jamo-short-name`, `hangul-syllable-name` | `names` | `name-tables`, `hangul`, `general-category`, and the books that those load | `derived-name`, `jamo`, `derived-general-category` |
| `code-point-name-aliases`, `name-alias-code-point`, `name-or-alias-code-point`, `loose-name-or-alias-code-point`, `find-name-alias`; the types `name-alias` and `name-alias-type` | `name-aliases` | `names`, and the books that it loads | `name-aliases`, and the tables of `names` |
| `code-point-basic-type`, `basic-type-ranges`; the type `basic-type` | `code-point-types` | `general-category`, `noncharacters`, `range-operations`, and the books that those load | `derived-general-category`, `prop-list` |
| `code-point-label`, `code-point-name-or-label`, `label-code-point`, `loose-label-code-point` | `code-point-labels` | `name-aliases`, `code-point-types`, and the books that those load | the tables of `name-aliases` and of `code-point-types` |
| `emoji-p`, `emoji-presentation-p`, `emoji-modifier-p`, `emoji-modifier-base-p`, `emoji-component-p`, `extended-pictographic-p`, `regional-indicator-p` | `emoji` | `code-points`, `versions`, `ranges` | `emoji-data`, `prop-list` |
| `decimal-digit-value`, `decimal-digit-p`, `decimal-digit-zero` | `decimal-digits` | `code-points`, `versions`, `ranges`, `maps` | `unicode-data` |
| `identifier-allowed-p`, `code-point-identifier-types`, `identifier-type-ranges`; the type `identifier-type` | `identifier-status` | `code-points`, `versions`, `ranges`, `runs`, `identifier-type-tables` | `identifier-status`, `identifier-type` |
| The theorems that relate the identifier status and types to NFKC | `identifier-status-normalization` | `property-relations`, `quick-check-theorems`, and the books that those load | the tables of those books |
| `prototype`, `replace-by-prototypes` | `confusables` | `versions`, `maps` | `confusables` |
| `internal-skeleton`, `skeleton`, `confusable-p` | `skeleton` | `confusables`, `normalization`, `default-ignorable`, `right-to-left-free`, and the books that those load | the tables of those books |
| `bidi-skeleton`, `bidi-confusable-p` | `bidi-skeleton` | `skeleton`, `bidi-left-to-right`, and the books that those load | the tables of those books |
| `right-to-left-free-p`, `right-to-left-code-point-p` | `right-to-left-free` | `bidi-class`, and the books that it loads | `derived-bidi-class` |
| `bidi-rule-p`, `bidi-rule-domain-name-p`, `bidi-right-to-left-label-p`, `bidi-domain-name-p`, `bidi-rule-strict-p`, `bidi-rule-wide-p` | `bidi-rule` | `bidi-class`, `bidi-brackets`, `right-to-left-free`, and the books that those load | `derived-bidi-class`, `bidi-brackets` |
| `bidi-name-display`, `bidi-name-read`, `bidi-clusters`, `bidi-name-levels` | `bidi-rule-display` | `bidi-rule`, `bidi-mirroring`, `bidi-neutral-types`, and the books that those load | the tables of those books |
| `bidi-clusters-weak-classes`, `bidi-cluster-weak-class` | `bidi-rule-display-weak` | `bidi-rule-display`, `bidi-weak-types`, and the books that those load | the tables of those books |
| the theorems `bidi-display-when-bidi-rule-wide-p` and `bidi-display-is-one-to-one-when-bidi-rule-wide-p`, and the same two for `bidi-rule-strict-p` | `bidi-rule-display-theorem` | `bidi-rule-display-order`, `bidi-rule-display-levels`, `bidi-rule-left-to-right-label`, and the books that those load, which are the whole algorithm | the tables of those books |
| `single-script-confusable-p`, `mixed-script-confusable-p`, `whole-script-confusable-p` | `confusable-kinds` | `skeleton`, `mixed-scripts`, and the books that those load | the tables of those books |
| `code-point-augmented-script-set`, `resolved-script-set`, `single-script-p`, `mixed-script-p`; the types `writing-system` and `script-set` | `mixed-scripts` | `scripts`, and the books that it loads | `scripts`, `script-extensions` |
| `decimal-digit-zeros`, `mixed-number-systems-p` | `mixed-numbers` | `decimal-digits`, and the books that it loads | `unicode-data` |
| `identifier-word-boundary-p`, `identifier-chunks` | `identifier-chunks` | `general-category`, `scripts`, `range-operations`, and the books that those load | `derived-general-category`, `scripts`, `script-extensions` |
| `code-point-general-category`, `general-category-ranges`, `assigned-p`; the type `general-category` and its predicates such as `general-category-letter-p` | `general-category` | `code-points`, `versions`, `ranges`, `general-category-tables` | `derived-general-category` |
| `general-category-changes`, `general-category-changes-of-assigned`, and the theorem that the `General_Category` of an assigned code point stays the same, with one exception | `general-category-changes` | `general-category`, `range-operations`, and the books that those load | `derived-general-category` |
| `ranges-union`, `ranges-intersection`, `ranges-difference`, `ranges-complement`, `ranges-normalize`, `range-list-code-points` | `range-operations` | `code-points`, `ranges` | none |
| `pattern-white-space-p` | `pattern-white-space` | `code-points`, `versions`, `ranges` | `prop-list` |
| `white-space-p` | `white-space` | `code-points`, `versions`, `ranges` | `prop-list` |
| `pattern-syntax-p` | `pattern-syntax` | `code-points`, `versions`, `ranges` | `prop-list` |
| `default-ignorable-p` | `default-ignorable` | `code-points`, `versions`, `ranges` | `derived-core-properties` |
| `variation-selector-p`, `join-control-p`, `noncharacter-p`, `deprecated-p`, `prepended-concatenation-mark-p` | `variation-selectors`, `join-controls`, `noncharacters`, `deprecated`, `prepended-concatenation-marks` (one book each) | `code-points`, `versions`, `ranges` | `prop-list` |
| `bidi-control-p`, `bidi-explicit-formatting-p`, `bidi-explicit-formatting-class` | `bidi-controls` | `code-points`, `versions`, `ranges`, `maps` | `prop-list`, `derived-bidi-class` |
| `code-point-bidi-bracket`; the type `bidi-bracket` | `bidi-brackets` | `versions`, `maps` | `bidi-brackets` |
| `code-point-bidi-mirroring-glyph` | `bidi-mirroring` | `bidi-brackets`, and the books that it loads | `bidi-brackets`, `bidi-mirroring` |
| `bidi-levels`, `bidi-display-order`, `bidi-display`, `bidi-arrange`, `bidi-paragraph-levels`, `bidi-paragraph-embedding-level`; the types `bidi-char`, `paragraph-direction` and `bidi-shown-char`; `bidi-confined-p`, `bidi-guarded-segments-p`, `bidi-self-contained-segments-p`; the theorems about the algorithm | `bidirectional-algorithm` | `bidi-display` and the six other books of the rules, `bidi-rearrangement`, `right-to-left-free`, `bidi-left-to-right`, `bidi-confinement`, `bidi-guarded-theorem`, `bidi-self-contained`, `bidi-class`, `bidi-brackets`, `bidi-mirroring`, `decompositions`, `general-category`, `kestrel/lists-light/perm`, `std/lists/flatten`, and the books that those load | `derived-bidi-class`, `bidi-brackets`, `bidi-mirroring`, `unicode-data`, `derived-general-category` |
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
has escape sequences that denote a character by its name needs `names`,
or `name-aliases` if an alias can be written for the name.
A front end for a language that
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
  costs to include the small ones.  `names` and `normalization` cost the
  most.  `names` has the largest tables: about 35,000 names for each
  version, and as many keys for the way back from a name to its code
  point.  `normalization` loads the compatibility decompositions even if
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
  `defpkg` in that package's `package.lsp`.  To work on the books of this
  directory, start ACL2 in it: the file `acl2-customization.lsp` defines
  the package and makes it the current one.
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
`https://www.unicode.org/Public/<version>/ucd/`, and from three data files
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
| `confusables.txt` of UTS #39 | `confusables` | the prototypes of confusable characters |
| `BidiBrackets.txt` | `bidi-brackets` | `Bidi_Paired_Bracket_Type` with `Bidi_Paired_Bracket` |
| `BidiMirroring.txt` | `bidi-mirroring` | `Bidi_Mirroring_Glyph` |
| `extracted/DerivedName.txt` | `derived-name` | `Name`: the names that are listed one by one, and a pattern for each range of the names that end in the code point.  The book of 16.0.0 has every listed name; the book of a later version has the names that the version adds |
| `Jamo.txt` | `jamo` | `Jamo_Short_Name` |
| `NameAliases.txt` | `name-aliases` | `Name_Alias`: for each code point that has aliases, the list of them, each with its type, in the order of the file |
| `extracted/DerivedName.txt` | `hangul-syllable-names`, in `data/names/` | The names of the Hangul syllables, once for all versions, for a test |
| `BidiTest.txt` | `bidi-test`, in `data/bidi/` | The conformance test vectors on bidirectional classes, once for all versions |
| `BidiCharacterTest.txt` | `bidi-character-test`, in `data/bidi/` | The conformance test vectors on code points, once for all versions |
| `NormalizationTest.txt` | `normalization-test` | The conformance test vectors |

Three more files are read only to interpret or cross-check those:
`PropertyValueAliases.txt`, `CompositionExclusions.txt`, and
`extracted/DerivedDecompositionType.txt`.

The three files of UTS #39 are not in the `ucd/` directory, and they
moved: they are at `https://www.unicode.org/Public/security/16.0.0/` for
16.0.0, and at `https://www.unicode.org/Public/<version>/security/` from
17.0.0 on.  The generator knows both places (`canonical_url`), and expects
the three files in the subdirectory `security/` of the directory it is
given.

For `confusables.txt` the generator checks that the number of entries is
the one in the last line of the file, that no code point is listed twice
or is its own prototype, and that no code point of a prototype is listed.

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
- **The names are read from `extracted/DerivedName.txt`**, which has all
  of them: the names that are listed one by one, a pattern such as
  `CJK UNIFIED IDEOGRAPH-*` for each range of the names that end in the
  code point, and the names of the Hangul syllables.  The generator checks
  the listed names against field 1 of `UnicodeData.txt`.  It checks that
  the names of the Hangul syllables are the ones that rule NR1 of the
  standard makes from `Jamo.txt`, and leaves them out of the tables of the
  versions: the library computes them by that rule.  They are written
  once, in `data/names/`, for the test that the rule in ACL2 gives them.
- **The names of a version are written as what it adds to the version
  before it.**  The book `derived-name` of 16.0.0 has the whole table; the
  book of a later version includes the book of the version before it and
  has only the names that the version adds.  The generator reads the
  earlier names back from the generated books, and stops if the new
  version changes or removes a name, or takes a code point out of a range
  with a pattern.  So the versions are generated from the earliest up.
- **The conformance test of normalization of a version is written as
  what it changes in the version before it.**  The book
  `normalization-test` of 16.0.0 has all the lines of
  `NormalizationTest.txt`, and takes 2.4 MB.  The book of a later version
  includes the book of the version before it, and writes each part of the
  file as a list of edits of the lines of the same part of that version:
  edits that keep the next lines, that drop the next lines, and that add
  lines.  Its constant has the same value as if the lines were all written
  out.  The books of 17.0.0 and 18.0.0 add 69 and 137 lines and drop none,
  and take 22 KB and 29 KB.  The generator reads the earlier lines back
  from the generated books, and checks that the edits it writes give the
  lines of the file.
- **The aliases of the names are read from `NameAliases.txt`**, and
  written in full for each version.  A code point can have several; they
  are kept in the order of the file.  The generator checks that each is
  written like a name, has one of the five types, is listed once, and is
  not a listed name.
- **Surrogates are code points** and get property values like any others.

What is computed in ACL2 rather than generated: the full decompositions
(by expanding the mappings, with a check that the result cannot be expanded
further), the table of the pairs that compose (from the canonical
mappings and `Full_Composition_Exclusion`), and the tables from the keys
of loose matching to code points (from the tables of the names and of
their aliases, when `names` and `name-aliases` are certified).  The
Hangul syllables are
handled by the arithmetic of the standard, not by tables, and so are
their names.

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
tables are tree maps (`fty::deftmap`) from code points to values, or,
for composition, from pairs of code points (`fty::defprod code-point-pair`)
to scalar values; and the sets of the code points that are the first, or
the second, of a pair that composes are tree sets (`fty::deftset
code-point-set`).  Every table that is not built with typed constructors is
checked against the recognizer of its type, by evaluation, in the book
that defines it.  The listed names are a tree map from code points to
strings (`fty::deftmap name-map`), and the patterns are a list of
products of a range and a prefix (`fty::defprod name-pattern`).
An alias is a product of a string and a type (`fty::defprod name-alias`,
`fty::deftagsum name-alias-type`), and the table of the aliases is a
tree map from code points to lists of aliases; the generated books
build the aliases with the typed constructors.
The conformance test vectors are typed too: a line of
`NormalizationTest.txt` is a `normalization-test-line`, a product with one
field per column (`tests/normalization-test-types`), and the generated
books build the lines with its constructor.  An edit of a list of lines
is a `normalization-test-edit` (`fty::deftagsum`, with the kinds `:keep`,
`:drop` and `:add`), and the function `normalization-test-apply-edits`
applies a list of edits to a list of lines.

### Where the bytes came from

The UCD files are not in the repository.  The data books are generated
from the files of `www.unicode.org`, at the URLs recorded in the books, and
`tools/ucd-sources.json` has the SHA-256 of each file.  For every
supported version, `Scripts.txt`, `ScriptExtensions.txt`, `Blocks.txt`,
`emoji/emoji-data.txt` and two files of UTS #39 were downloaded on
2026-11-19; `confusables.txt`, `BidiBrackets.txt`, `BidiMirroring.txt`,
`BidiTest.txt` and `BidiCharacterTest.txt` on 2026-11-20;
`extracted/DerivedName.txt`, `Jamo.txt` and `NameAliases.txt` on
2026-11-26; and the other files on 2026-11-14.

To check the files and the books of a version:

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
with the three files of UTS #39 in its subdirectory `security/`
(`--fetch` downloads into it the files that are missing).  The version must
be written in full.  The script needs only the Python standard library.
To regenerate the books of several versions, run it for the earliest
version first: the book of the names of a version, and the book of its
conformance test of normalization, are written from the books of the
versions before it.

### Adding a version

For example 19.0.0:

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
   `decimal-digits`, `identifier-status`, `confusables`,
   `pattern-white-space`, `white-space`, `pattern-syntax`,
   `bidi-controls`, `bidi-brackets`, `bidi-mirroring`,
   `default-ignorable`, `variation-selectors`, `join-controls`,
   `noncharacters`, `deprecated`, `prepended-concatenation-marks`,
   `combining-classes`, `decompositions`, `compositions`, `composing-pairs`,
   `quick-check`, `names`, `name-aliases`),
   add the `include-book`
   of the new data book and a `:v19.0.0` line to each selector;
   `grep -n v18.0.0 *.lisp` finds every place.  In `decompositions`,
   `compositions` and `composing-pairs`, also copy the block that defines
   and checks the computed tables.  In `skeleton`, add a `:v19.0.0 nil`
   line to `internal-skeleton-unstable-code-points`.  In `names`, also
   copy the constant `*name-keys-v18.0.0*` with its two assertions, and
   add the new version to the local function `name-stable-ok` and to the
   local lemma `code-point-name-in-terms-of-version-case`.  In
   `name-aliases`, do the same with `*name-alias-keys-v18.0.0*`,
   `aliases-stable-ok` and
   `code-point-name-aliases-in-terms-of-version-case`; the assertion on
   the size of the new constant has the number of aliases of the new
   version.  In `code-point-types`, add the new version to the local lemma
   `basic-type-ranges-in-terms-of-version-case`.
5. Read Section 5.1 of the revision of UTS #39 for the new version.  If
   the rules for the augmented script set have changed, as they did in
   the revision for 18.0.0, change `augment-script-extensions` in
   `mixed-scripts`, with a condition on the version.
6. In `tests/`, copy `normalization-test-v18.0.0.lisp` and
   `quick-check-v18.0.0.lisp`, changing the version, and add to
   `bidi-character-test.lisp` the assertion for the new version, and to
   `names.lisp`, `name-aliases.lisp` and `code-point-types.lisp` the
   tests of the new version that count code points or aliases.
   Then run the generator with `--check` for each of the older versions.
   If it says that a book of `data/bidi/` differs, the new version has
   changed a test case of `BidiTest.txt` or `BidiCharacterTest.txt`:
   the two books then have to be written per version (the functions
   `book_bidi_test` and `book_bidi_character_test` of the generator),
   and the revision of UAX #9 for the new version has to be read for
   the rule that changed.  Read its list of modifications in any case:
   the algorithm of this library is the one of revisions 50 to 52.
7. Certify `top` and `tests/*`.  This checks the invariants of the new
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
   - The check of the tables in the section `skeleton-idempotence` of
     `skeleton` fails if the internal skeleton of some code point of the
     new version is not its own internal skeleton.  UTS #39 says that
     there is none, and there was none in 18.0.0, but there were thirteen
     in 16.0.0 and in 17.0.0.  To find them, evaluate, for each code point
     that has a prototype, whether the internal skeleton of its internal
     skeleton is its internal skeleton; put those that fail in the new
     line of `internal-skeleton-unstable-code-points`.  Then
     `internal-skeleton-of-internal-skeleton-from-v18.0.0` has to be
     restated for 18.0.0 alone.
   - `code-point-basic-type-of-later-version` fails if the new version
     makes a graphic character a format character, or the reverse, by
     changing its `General_Category`; the stability policies allow that.
     `code-point-label-of-later-version` follows from it.
   - The theorems of `property-relations` are facts about the data, some
     of which the specifications state and some not.  If one fails, that
     is a change in Unicode to look at, as before.

   A failure of any of the others (assigned code points, `XID_Start`,
   `XID_Continue`, `ID_Start`, `ID_Continue`, normalization, Stream-Safe
   text, the quick check for NFD and NFKD, the names of the characters
   and their aliases, the labels,
   `Pattern_White_Space`, `Pattern_Syntax`,
   noncharacters, the three fixed values of `General_Category`) would mean
   that the new version breaks a stability policy of the standard, or that
   a table is wrong.
8. For the comparison with other implementations, add
   `validation/rust-oracle/v19.0.0/Cargo.toml` with the versions of the
   crates that implement Unicode 19.0.0.

Nothing else changes: no definition other than the table of the scripts
and, if the specification changed it, the rule of the augmented script
sets; and no theorem statement other than those just listed.

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

- `bidi-test`: **all of `BidiTest.txt`**, the conformance test of the
  bidirectional algorithm on bidirectional classes: 490,846 lines, each in
  the one, two or three paragraph directions that it asks for, which
  makes 770,241 tests of the resolved levels and of the order of display.
  The file covers every sequence of up to four classes, and some longer
  ones.  It has no code points, and it is the same for the three
  versions, so it is run once.
- `bidi-character-test`: **all of `BidiCharacterTest.txt`**, the
  conformance test on code points, which is the one that has paired
  brackets: 91,707 lines, each checked for the paragraph embedding level,
  the resolved levels and the order of display, in each of the three
  versions.
- `bidi-confinement`: the theorem that a plain text whose segments are
  guarded is confined, checked by running the algorithm on every text of
  one to four characters over sixteen characters (one for each of the
  twelve bidirectional classes that a plain text can have, and two kinds
  of paired brackets), with every way of cutting the text: 435,434 cases
  with guarded segments at length four, all confined.  Lengths one to
  three are run for the three versions and length four for 17.0.0; the
  sixteen characters have the same properties in the three.  Then
  examples: for each of the conditions, a text that fails it and is not
  confined; and a confined text one of whose segments is not displayed as
  it would be alone.  The same check at length five, 12,592,378 cases
  with guarded segments and none that is not confined, was run once, on
  2026-11-23, outside the certified books.
- `bidi-self-contained`: the two theorems about a plain text whose
  segments are self-contained, checked by running the algorithm on the
  same texts, with the same ways of cutting them, as `bidi-confinement`:
  434,252 cases with self-contained segments at length four (1,182 fewer
  than with guarded segments), and in each of them the levels and the
  display of the text are those of the segments alone.  Lengths one to
  three are run for the three versions and length four for 17.0.0.  Then
  examples: a text whose segments are self-contained; and, for each of
  the two conditions added to those on guarded segments, a text that
  fails only that one and has a segment that is not displayed as it is
  alone (for the second, 63 opening parentheses come first).  The same
  check at length five, 12,521,266 cases with self-contained segments and
  none that differs, was run once, on 2026-11-24, outside the certified
  books.
- `bidi-rule`: examples of the Bidi Rule (labels that satisfy it, labels
  that fail each of its six conditions, domain names); the two pairs of
  labels that satisfy the rule and are displayed alike, one with a
  character of class `ET` and one with a character of class `BN`;
  examples of the wide rule, and for each of its conditions two names
  that are displayed alike and that the condition keeps apart.  Then the
  search.  It takes every list of up to five characters from a small set,
  keeps the lists that are right-to-left labels satisfying a rule,
  displays each one and compares the displays.  For the strict rule the
  set has thirteen characters (two letters of class `R` and one of class
  `AL`, two digits of class `EN` and two of class `AN`, the hyphen, the
  comma, the asterisk, the two parentheses and a Hebrew point): 36,543
  labels of five characters and 3,474 shorter ones, none displayed like
  another, in a paragraph of either direction.  For the wide rule it has
  sixteen (those, the percent sign, `<` and `>`): 297,633 names of five
  characters and 20,742 shorter ones, none displayed like another in a
  paragraph from left to right.  For the Bidi Rule as it is written, with
  the percent sign added to the thirteen characters, 16 labels of five
  characters are displayed like another; with U+200C added, 36 labels of
  four characters are.  Two more searches have letters of class `L` in
  the set and compare the left-to-right labels and the right-to-left
  ones together: 10,728 labels of five characters for the strict rule,
  in each direction, and 90,351 names for the wide rule, none displayed
  like another.  The searches at six characters were run once, on
  2026-11-24, outside the certified books: 416,724 labels for the strict
  rule in each direction and 4,437,669 names for the wide rule, and with
  the letters of class `L` 85,486 labels and 816,451 names; none
  displayed like another.  The searches were written before the proofs,
  and are kept as tests of the rules and of the algorithm.
- `bidi-rule-display`: examples of the display of a name computed
  without the rules of the algorithm (`bidi-name-display`) and of the way
  back (`bidi-name-read`): numbers,
  separators after a Hebrew and after an Arabic letter, a mirrored
  character, bracket pairs with and without a digit inside, brackets that
  do not match, marks.  Examples of names that do not satisfy the wide
  rule and that the algorithm displays in another way, one for each of
  three conditions; and two names with both kinds of digits that are
  displayed alike.  Then the search: for every name of up to five
  characters that satisfies the wide rule, the display of
  `bidi-name-display` is the display of the algorithm in a paragraph from
  left to right, and the way back gives the name (the search was written
  before the proofs, and is kept as a test of the functions).  Five
  examples of the levels (`bidi-name-levels`) and of the classes after
  the weak rules (`bidi-clusters-weak-classes`), each compared with the
  algorithm.  Seven labels that satisfy the strict rule, four
  right-to-left and three left-to-right, each displayed in a paragraph
  from left to right, in one from right to left and in one that takes its
  direction from the label, with its levels in a paragraph from right to
  left; and a name that satisfies the wide rule only, with its levels
  and its display in a paragraph from right to left.  The search goes
  through the 318,375 right-to-left
  names over the sixteen characters of the search for the wide rule,
  through the 101,423 names of both kinds over the twelve characters
  with letters of class `L`, and through 41,262 right-to-left names over
  eleven characters with two kinds of brackets; none fails.  The same
  checks at six characters were run once, on 2026-11-25, outside the
  certified books: 4,437,669, 816,451 and 394,108 names, and none fails.

- `names`: examples of the three kinds of names, of the code points
  without a name, of loose matching, with the examples of UAX #44, and
  of the functions from a name to its code point.  Then, for each
  version, three checks on whole sets of code points.  The rule for the
  names of the Hangul syllables gives the 11,172 names that
  `DerivedName.txt` lists for them.  The number of code points with a name
  is 154,998 for 16.0.0, 159,801 for 17.0.0 and 172,808 for 18.0.0: the
  listed names, the Hangul syllables, and the ranges of the names that
  end in the code point, with no code point counted twice.  And the
  characters that loose matching ignores as white space are, among the
  first 256 code points, those that have `White_Space`.
- `name-aliases`: examples of the aliases of code points, with their
  types, and of the functions from an alias, or from a name or an alias,
  to its code point, exactly and by loose matching.  Then, for each
  version, the number of aliases of each type: 35 corrections in 16.0.0
  and 39 in the other two, 84 of type control, 1 alternate, 3 of type
  figment and 354 abbreviations.
- `code-point-types`: examples of each basic type, and, for each
  version, the number of code points of each type, counted on the
  ranges: 65 control codes, 137,468 private-use code points, 2,048
  surrogates, 66 noncharacters and 172 format characters in every
  version; 154,826 graphic characters in 16.0.0, 159,629 in 17.0.0 and
  172,636 in 18.0.0; and the rest reserved.
- `code-point-labels`: examples of the labels of the five types that have
  them, of the name or label of a code point, and of the functions from
  a label to its code point; among them the strings that are not labels
  because of the number of their digits or of their type, and the two
  aliases, `PRIVATE USE-1` and `PRIVATE USE-2`, whose keys for loose
  matching look like those of labels.

The conformance test of normalization takes about ten seconds per
version, and the quick-check test about twenty.  The two conformance
tests of the bidirectional algorithm take about two seconds and about
ten seconds, the confinement test about ten seconds, the test of
self-contained segments about fifteen, the test of the Bidi Rule about
forty and the test of the display of names about thirty.

The two conformance files of the bidirectional algorithm have the same
test cases in Unicode 16.0.0, 17.0.0 and 18.0.0; only their comments
differ.  So the generator writes them once, in `data/bidi/`, in a compact
form: the lines with the same expected results are grouped, and each
bidirectional class or code point is one character of a string.  The
two books take 3.2 MB.  The rules of UAX #9 are also the same in the
three versions (revisions 50, 51 and 52 of UAX #9 differ in their
explanations), so the algorithm is defined once, and a version comes in
only through the properties of the code points.

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

`General_Category` and seven binary properties were compared on
2026-11-19, for every code point, and the comparisons above were run again
on that day:

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

The Stream-Safe Text Process was compared, on 2026-11-19, with the
`stream_safe` iterator of `unicode-normalization` (0.1.24, 0.1.25 and 0.1.26
for the three versions).  `validation/dump.lisp` writes what
`stream-safe-process` gives for three sequences for each code point whose
compatibility decomposition has a non-starter (the code point 35 times; 29
combining acute accents, the code point, and 3 more accents; and the code
point 16 times between two letters, and once more), and for five other
sequences: 6,275 sequences for 16.0.0, 6,377 for 17.0.0 and 6,479 for
18.0.0.  The process inserts U+034F in 1,885 of the sequences for 16.0.0.
No differences.  The definitions and theorems of `composing-pairs`,
`normalization-inert` and `normalization-members` are statements about the
normalization functions, proved in the library; nothing is compared for
them.

The properties of identifiers, scripts, bidirectional classes, emoji and
digits were compared on 2026-11-20, for every code point
(`validation/dump.lisp` writes sixteen more columns), and the comparisons
above of every code point were run again on that day.  No differences:

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

`White_Space` was compared on 2026-11-20, for every code point but the
surrogates (`validation/dump.lisp` writes one more column for it), with
`char::is_whitespace` of the Rust standard library in the oracle of each
version, and for 16.0.0 also with `regex-syntax`; the comparisons above
of every code point were run again.  No differences.  The standard
library has its own tables, for the version of Unicode of the toolchain
that builds the oracle (rustc 1.97.0); the property is the same in
the three supported versions.

The skeletons and the script sets of UTS #39 were compared on 2026-11-20,
for every code point (`validation/dump.lisp` writes four more columns for
them), and the comparisons above of every code point were run again.  No
differences:

- The internal skeleton of each code point alone, and of each code point
  between the letter a and two combining marks that are not in canonical
  order: with `unicode-security` 0.1.3 for 18.0.0; and, for 16.0.0 and
  17.0.0, with a second implementation of the four steps, in
  `validation/python-oracle.py`, which takes NFD from Python (3.14.6 and
  3.15.0b4) and reads the prototypes and the default ignorable code
  points from the files `confusables.txt` and `DerivedCoreProperties.txt`
  themselves, not from the generated tables.  The same author wrote that
  second implementation, so it is weaker evidence than a crate.
- `unicode-security` 0.1.2, for 16.0.0, has an earlier definition of the
  skeleton, without the removal of the default ignorable code points.
  The library does not have that function; the dump computes it from
  `nfd` and `replace-by-prototypes` (the column `skelk`), and it agrees
  with the crate on every code point.
- The augmented script set of each code point: with `unicode-security`
  0.1.2 for 16.0.0 and 0.1.3 for 18.0.0.  The crate does not have the
  writing system `Hntl`, which UTS #39 has from 18.0.0 on; the comparison
  leaves it out of the sets of the library.  So the rule for `Hntl` was
  not compared with another implementation; the tests have its examples
  from Table 1a of UTS #39.  For an unassigned code point the crate has
  the empty set where the library, following the definition, has the set
  of the one script `Unknown`; the oracle writes `Zzzz` for it.
- The crate for 16.0.0 and the second implementation give, like the
  library, U+0064, U+007A, U+030C as the skeleton of U+01C6 and U+0306 as
  the skeleton of U+030C: the internal skeleton of 16.0.0 and 17.0.0 is
  not idempotent in them either.
- As a control, comparing the 17.0.0 output of the library with the
  18.0.0 oracle reports 2,529 code points that differ in the skeleton and
  13,010 in the augmented script set.

The guard of `skeleton` rests on a fact about the Unicode Bidirectional
Algorithm: a text with no character of class `R`, `AL`, `AN`, `RLE`, `RLO`
or `RLI` is displayed, in a paragraph from left to right, in the order in
which it is stored.  That is a theorem of the library
(`bidi-display-order-when-right-to-left-free-p`).  It was also tested, on
2026-11-20, with `unicode-bidi` 0.3.18 (Unicode 16.0.0), by
`oracle 16.0.0 display-order`, which `validation/run.sh` runs:

- All 67,368,420 strings of one to six characters over twenty characters
  of sixteen of the seventeen other classes are displayed in the order in
  which they are stored.  (The seventeenth class is `B`, the paragraph
  separators, which only cut a text into paragraphs.)  Explicit formatting
  characters are left out of the comparison of the two orders, because
  the skeleton removes them.
- For each of the six classes, some string of up to four characters that
  has one character of the class is displayed in another order: the test
  prints one for each.

So that implementation of the algorithm agrees with the theorem on those
strings.

The text as it is displayed with every character kept (`bidi-display`,
which the bidirectional skeleton uses) depends on things that UAX #9 and
UTS #39 leave open and that the conformance files do not test: the place
of the characters that rule X9 removes, and what rule L3 does exactly.
The documentation topic `bidi-displayed-text` states what the library
does.  It was compared on 2026-11-23 with ICU 74.2, by the script
`validation/icu-display.py` and the book `validation/compare-display`.
That ICU has Unicode 15.1.0, so the strings are made of 35 characters whose
properties have not changed since: characters of all the bidirectional
classes but `B`, among them paired brackets, other mirrored characters,
two combining marks and the formatting characters.  The strings are
random, of one to eight characters, each in a paragraph from left to
right, from right to left, or with the direction of its first strong
character.  ICU is asked for the levels and for the reordered text, with
the options that keep combining marks with their base characters and
that replace mirrored characters, which are rules L3 and L4.  The results
are the same for the three supported versions:

- Of 30,000 strings with none of the characters that rule X9 removes,
  29,948 are displayed in the same way by ICU and by `bidi-display`.  For
  the other 52, ICU does not give the levels that this library gives,
  which are the levels of the conformance files.
- Of 20,000 strings that can have those characters, 16,573 are displayed
  in the same way, and for 64 the levels of ICU are not those of this
  library.  The other 3,363 are displayed in the same way once each
  character that rule X9 removes takes the level of the character after
  it, as ICU does, instead of the level of the character before it, as
  UAX #9, Section 5.2, describes and as `bidi-display` does.  The rule
  says that the place of those characters is not specified.
- No string differs for another reason.

Two examples of the levels of ICU 74.2 that are not those of the
conformance files.  For U+2067, U+05B0, U+003E, U+0009 in a paragraph
from right to left, it gives 1 1 1 1, and `BidiTest.txt` has 1 3 3 1 for
the classes of these characters (`RLI NSM ON S`); the order of display is
the same, but the combining mark is next to another character at its
level.  For line 86 of `BidiCharacterTest.txt`, `05D0 0028 05D1 0029
0331` in a paragraph from left to right, it gives 1 1 1 1 0, and the file
has 1 1 1 1 1.

Rule L3 does not speak of combining marks at a right-to-left level with
no base character next to them.  ICU puts them back in the stored order,
like the marks that have a base, and `bidi-move-marks` does too.  Two
differences are left as they are.  One is the place of the
characters that rule X9 removes, above.  The other is a text of several
paragraphs, which the comparison does not cover: ICU orders the whole
text as one line, so that two paragraphs from right to left come out
with the second one first, and `bidi-display` displays each paragraph by
itself and puts them one after the other.  Neither matters for the
skeleton of an identifier.

To repeat the comparison with ICU (it needs `acl2`, `python3` and the
shared library `libicuuc`):

```
cert.pl validation/compare-display
validation/icu-display.py 11 30000 8 kept > /tmp/icu-kept.lsp
validation/icu-display.py 7 20000 8 > /tmp/icu-all.lsp
```

and then, in ACL2, for each version:

```
(include-book "validation/compare-display")
(in-package "UNICODE")
(compare-display (version-v16.0.0) "/tmp/icu-kept.lsp" state)
(compare-display (version-v16.0.0) "/tmp/icu-all.lsp" state)
```

The two labels of the tests that satisfy the Bidi Rule and are displayed
alike, U+05D0, `1`, `-`, `%`, `1` and U+05D0, `%`, `1`, `-`, `1`, were
given to other implementations once, on 2026-11-24, also with `$`, `#`,
U+00B0, U+20AC and U+066A, which are of class `ET` too, in place of the
percent sign.  The scripts are not in the library.

- The two checks of the Bidi Rule alone that were tried accept both
  labels with each of the six characters: `check_bidi` of the Python
  package `idna` 3.20, and the Go package
  `golang.org/x/text/secure/bidirule` (v0.31.0).
- Strict IDNA2008 rejects both: `encode` of the Python package `idna`
  says that the character is not allowed.  Of the 77 code points of class
  `ET` in its tables (Unicode 15.1.0), none is permitted in a label.
- Five implementations of UTS #46 accept both labels, as two different
  names, when the character is U+00B0, U+20AC or U+066A: the URL parser
  of Node 22.23.4, the npm package `tr46` 7.0.0, the Go package
  `golang.org/x/net/idna` (v0.47.0, its three profiles), the Rust crates
  `idna` 1.1.0 and `url` 2.5.9, and ICU 74.2 through `idn_to_ascii` of
  PHP with the check of the Bidi Rule on.  With U+20AC the two names
  become `xn--1-1-ppe6945a` and `xn--1-1-ppe4945a`.
- Four implementations of the algorithm display the two labels alike, in
  a paragraph of either direction, and as `bidi-display` does: the Python
  package `python-bidi` 0.6.12, the Rust crate `unicode-bidi` 0.3.18, the
  npm package `bidi-js` 1.1.0, and the class `java.text.Bidi` of JDK 21.

The names were compared on 2026-11-26, for every code point
(`validation/dump.lisp` writes one more column, with what
`code-point-name` gives), with `unicodedata.name` of Python, and the
comparisons above of every code point were run again on that day.  No
differences:

- With Python 3.15.0b4, for 17.0.0: on the 1,114,112 code points.
- With Python 3.14.6, for 16.0.0: on 1,107,967 code points.  The other
  6,145 are the Tangut ideographs of that version, U+17000 to U+187F7 and
  U+18D00 to U+18D08.  `unicodedata.name` of that Python has no name for
  them, although its `unicodedata.lookup` finds U+17000 by the name
  `TANGUT IDEOGRAPH-17000` (CPython issue 80667).  The oracle writes
  "cannot say" for a code point that has no name in Python and whose
  `General_Category`, in Python, is not `Cc`, `Cs`, `Co` or `Cn`, and
  reports how many there are.
- For 18.0.0 the names were not compared with another implementation.
  The generator checks, for each version, every listed name against
  field 1 of `UnicodeData.txt`, and the names of the Hangul syllables
  against the rule; and the library proves that a name of 17.0.0 is the
  same in 18.0.0.
- `name-code-point` and the loose matching were not compared with another
  implementation.  The first is proved to be the inverse of
  `code-point-name`; for the second the tests have the examples of
  UAX #44.

The aliases of the names and the labels were compared on 2026-11-27,
for every code point (`validation/dump.lisp` writes two more columns),
and the comparisons above of every code point were run again on that
day.  No differences:

- The aliases, with Python 3.14.6 for 16.0.0 and Python 3.15.0b4 for
  17.0.0.  Python has no function from a code point to its aliases, so
  the oracle takes the aliases and their types from `NameAliases.txt`
  and keeps, for each code point, those for which `unicodedata.lookup`
  gives that code point.  It kept all of them: 477 and 481.  For 18.0.0
  the aliases were not compared with another implementation; they are
  the same as those of 17.0.0.
- The labels, for the three versions, with the comments of
  `extracted/DerivedGeneralCategory.txt`, which give the label of the
  first and of the last code point of each range of the code points
  whose `General_Category` is `Cc`, `Cs`, `Co` or `Cn`.  The oracle
  writes "cannot say" for the code points inside such a range, and no
  label for the code points of the other categories.  So the labels
  were compared on 1,225 code points for 16.0.0, 1,234 for 17.0.0 and
  1,229 for 18.0.0, and the absence of a label on the 154,998, 159,801
  and 172,808 code points that have a name.
- The basic types of code points were not compared with another
  implementation: they are a short definition on top of
  `General_Category` and `Noncharacter_Code_Point`, which were.

Not compared with another implementation: the bidirectional skeleton as
a whole (its two parts are, above: the displayed text and the internal
skeleton; and the tests have the worked example of UTS #39); the
resolved script set of a list, the three classes of confusable strings,
and mixed-number detection, which are short definitions on top of what is
compared; the tests have the examples of UTS #39 for each.  The chunks of
an identifier are not compared with another implementation either.  The
tests have the thirteen examples of the table of UTS #55, Section
5.1.2.1, and that is all the evidence there is that the definition is the
one the specification means.  The file
`confusablesSummary.txt` of UTS #39 is not used as a test: its groups of
look-alike strings are not the classes of strings with the same skeleton
(by the second implementation, 73 of its 3,417 groups in 17.0.0, and 31
of its 3,138 groups in 18.0.0, have members with different skeletons).

To repeat this (it needs `acl2` and `cargo`, and for the Python part an
interpreter with the right version of Unicode; `UCD_DIR` is the directory
with the files of the version, for the skeletons and the aliases of the
Python part and for the labels):

```
cert.pl validation/dump
UCD_DIR=/tmp/ucd-16.0.0 \
  validation/run.sh 16.0.0 /tmp/unicode-validation python3.14
UCD_DIR=/tmp/ucd-17.0.0 \
  validation/run.sh 17.0.0 /tmp/unicode-validation python3.15
UCD_DIR=/tmp/ucd-18.0.0 \
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
used in the same way; they only have no topics of their own.  The
exception is the recognizer, which has a topic of one line, so that a
signature such as `(code-point-script cp ver)` returning a `script-p`
links to the type.
For `script`, the list of the values in the topic is generated from
`*script-table*`, and has the constructor of each value.

The rule is about topics without content.  It does not turn off topics
that show a definition: the functions that `defruns` introduces for each
table of runs (17 topics for each of six properties) keep theirs, because
the macro writes their definitions, and their topics are where those and
their theorems can be read.  The smaller types of the same kind
(`identifier-type`, with 12 values and 42 topics, and the ones with fewer
values) are under the line and keep the generated topics.

With this, the library has about 1,420 topics.  The books of the
bidirectional algorithm have some 385 of them: their functions, and
twenty-seven small types whose generated topics, about fifteen at most for
one type, are under the line.  The book of the Bidi Rule has 29, and
the books of the display of names 39.

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
The value of a decimal digit is a lookup in a tree map, and so is the
prototype of a code point.  The name of a code point is a test for the
Hangul syllables, a search in the list of the patterns, which has about
twenty, and a lookup in a tree map; the code point with a name is a
lookup in a tree map whose keys are strings, and then the name of the
code point found, to compare.  The aliases of a code point are a lookup
in a tree map.  The basic type and the label of a code point need its
`General_Category`.  The skeleton of a list normalizes it twice.
The operations on lists of ranges take time proportional to the product of
the lengths of the two lists; `general-category-changes`, which uses them
on the ranges of each of the thirty values, takes well under a second.
The normalization functions are meant for identifiers and the like: they are
not tail recursive, and reordering a run of *n* combining marks takes time
quadratic in *n*.
The functions of the bidirectional algorithm are written to be read next
to UAX #9, not for speed: they find a character by its position by going
through the list, so a paragraph of *n* characters takes time quadratic in
*n*, and they are not tail recursive.  The 770,241 tests of `BidiTest.txt`,
on sequences of a few characters, run in about a second and a half.

Certifying all the 177 books from scratch, the tests and the generated
tables included, took about eight minutes with two jobs
(`cert.pl -j 2`, SBCL).  The slowest books, apart from the tests, take
about twenty to thirty seconds each: `quick-check-theorems`,
`script-tables` (the type of the scripts is a tagged sum with 179 cases),
`normalization-across-versions`, `names`, `bidi-rule-display-levels` and
`code-point-labels`.

## License

The books and tools are under the 3-clause BSD license of ACL2.  The tables
in `data/` are derived from the Unicode Character Database, which is
Copyright © Unicode, Inc. and is distributed under the Unicode License V3
(`Unicode-3.0`), a permissive license that requires its notice to accompany
copies of the data; the notice is in the file `LICENSE-UNICODE`.
