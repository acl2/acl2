; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "code-points")
(include-book "versions")
(include-book "ranges")
(include-book "range-operations")
(include-book "runs")
(include-book "maps")
(include-book "general-category-tables")
(include-book "general-category")
(include-book "general-category-changes")
(include-book "xid")
(include-book "id")
(include-book "id-compat-math")
(include-book "script-tables")
(include-book "scripts")
(include-book "bidi-class-tables")
(include-book "bidi-class")
(include-book "block-tables")
(include-book "blocks")
(include-book "emoji")
(include-book "decimal-digits")
(include-book "identifier-type-tables")
(include-book "identifier-status")
(include-book "pattern-white-space")
(include-book "white-space")
(include-book "pattern-syntax")
(include-book "bidi-controls")
(include-book "bidirectional-algorithm")
(include-book "default-ignorable")
(include-book "variation-selectors")
(include-book "join-controls")
(include-book "noncharacters")
(include-book "deprecated")
(include-book "prepended-concatenation-marks")
(include-book "hangul")
(include-book "combining-classes")
(include-book "decompositions")
(include-book "compositions")
(include-book "normalization")
(include-book "composing-pairs")
(include-book "normalization-inert")
(include-book "normalization-members")
(include-book "stream-safe")
(include-book "normalization-across-versions")
(include-book "identifier-closure")
(include-book "quick-check")
(include-book "quick-check-theorems")
(include-book "utf-8")
(include-book "property-relations")
(include-book "identifier-status-normalization")
(include-book "confusables")
(include-book "skeleton")
(include-book "bidi-skeleton")
(include-book "mixed-scripts")
(include-book "confusable-kinds")
(include-book "mixed-numbers")
(include-book "identifier-chunks")
(include-book "coverage")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode
  :parents (acl2::kestrel-books)
  :short "An ACL2 library for the Unicode Standard:
          code points, character properties, and normalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library models the parts of the "
    (xdoc::ahref "https://www.unicode.org/versions/latest/"
                 "Unicode Standard")
    " and of the "
    (xdoc::ahref "https://www.unicode.org/reports/tr44/"
                 "Unicode Character Database")
    " that the lexers of programming languages need.
     It is meant to be shared by the models of those languages:
     nothing in it is specific to one language.
     The one topic that names programming languages
     is @(see unicode-coverage),
     which says for which of them the library has enough.
     Currently it has:")
   (xdoc::ul
    (xdoc::li
     "Code points and scalar values:
      see @(see code-points).")
    (xdoc::li
     "The @('General_Category') property,
      which says whether a code point is a letter, a mark, a number,
      punctuation, a symbol, a separator or something else,
      and whether it is assigned at all:
      see @(see general-category-property).")
    (xdoc::li
     "The @('XID_Start') and @('XID_Continue') properties,
      where @('ID') is short for `identifier',
      and the identifiers that they define:
      see @(see xid).")
    (xdoc::li
     "The @('ID_Start') and @('ID_Continue') properties,
      from which those two are derived,
      with the exact difference between them,
      and the two properties of the mathematical notation profile:
      see @(see id-properties) and @(see id-compat-math).")
    (xdoc::li
     "The @('Script') and @('Script_Extensions') properties,
      which say which writing system a character belongs to:
      see @(see scripts).")
    (xdoc::li
     "The @('Identifier_Status') and @('Identifier_Type') properties
      of Unicode Security Mechanisms,
      which say which characters are safe to allow in identifiers,
      and why the others are not:
      see @(see identifier-status).")
    (xdoc::li
     "Confusable strings, that is, strings that look alike:
      the prototypes of characters,
      the skeleton and the bidirectional skeleton of a string,
      and the three classes of confusable strings,
      of Unicode Security Mechanisms:
      see @(see confusables), @(see confusable-detection),
      @(see bidirectional-skeleton) and @(see confusable-kinds).")
    (xdoc::li
     "Mixed-script detection and mixed-number detection,
      of the same specification:
      whether the characters of a string have a script in common,
      and whether its digits are of one system:
      see @(see mixed-script-detection)
      and @(see mixed-number-detection).")
    (xdoc::li
     "The chunks of an identifier,
      which are the words that its letter case and its punctuation
      make visible, of Unicode Source Code Handling:
      see @(see identifier-word-boundaries).")
    (xdoc::li
     "The four normalization forms, which are
      Normalization Forms D, C, KD and KC (NFD, NFC, NFKD and NFKC),
      with what they are made of:
      decompositions, combining classes, composition exclusions,
      and the algorithms for Hangul syllables:
      see @(see normalization).")
    (xdoc::li
     "Canonical equivalence and compatibility equivalence,
      which are defined by the normalization forms:
      see @(tsee canonical-equivalent-p)
      and @(tsee compatibility-equivalent-p).")
    (xdoc::li
     "The proof that normalizing an identifier gives an identifier:
      see @(see identifier-closure).")
    (xdoc::li
     "The code points that the normalization forms leave alone
      and across which they do not reach,
      which is what a language needs to know about its delimiters:
      see @(see normalization-inert-code-points);
      and where certain code points of a normalized text come from:
      see @(see normalization-members).")
    (xdoc::li
     "The Stream-Safe Text Format,
      which bounds the number of combining marks in a row,
      and the process that puts text in that format:
      see @(see stream-safe).")
    (xdoc::li
     "The quick check properties of the normalization forms,
      the proof that the quick check is exact
      for the two decomposed forms,
      and the proof that the code points that the two composed forms change
      are those whose quick check value is `no':
      see @(see quick-check) and @(see quick-check-theorems).")
    (xdoc::li
     "The @('Pattern_White_Space') property,
      which defines white space:
      see @(see pattern-white-space).")
    (xdoc::li
     "The @('White_Space') property,
      which has the spaces of ordinary text,
      and is not the same as @('Pattern_White_Space'):
      see @(see white-space).")
    (xdoc::li
     "The @('Pattern_Syntax') property,
      which defines the characters of syntax:
      see @(see pattern-syntax).")
    (xdoc::li
     "The bidirectional control characters,
      which a lexer may have to reject or report:
      see @(see bidi-controls).")
    (xdoc::li
     "The @('Bidi_Class') property,
      which says whether a character is written
      from left to right or from right to left:
      see @(see bidi-class-property).")
    (xdoc::li
     "The paired brackets and the mirroring glyphs:
      see @(see bidi-paired-brackets) and @(see bidi-mirroring).")
    (xdoc::li
     "The Unicode Bidirectional Algorithm,
      which says in what order a text is displayed
      when it has characters written from right to left,
      with the theorems that it only rearranges the text,
      that it leaves a text as it is stored
      when no character of the text can start text from right to left,
      and that it displays a text segment by segment
      when the text is cut where the levels allow it:
      see @(see bidirectional-algorithm).")
    (xdoc::li
     "The Bidi Rule of Internationalized Domain Names,
      a condition on a name with right-to-left characters,
      and two rules derived from it:
      see @(see bidi-rule).")
    (xdoc::li
     "The emoji properties and the regional indicators:
      see @(see emoji).")
    (xdoc::li
     "The decimal digits of every system of digits, with their values:
      see @(see decimal-digits).")
    (xdoc::li
     "The @('Block') property: see @(see blocks).")
    (xdoc::li
     "Six more properties of characters
      that a lexer may have to reject, report or treat specially:
      the default ignorable code points, the variation selectors,
      the join controls, the noncharacters, the deprecated characters
      and the prepended concatenation marks.
      See @(see default-ignorable), @(see variation-selectors),
      @(see join-controls), @(see noncharacters), @(see deprecated)
      and @(see prepended-concatenation-marks).")
    (xdoc::li
     "Theorems that relate these properties to each other:
      see @(see property-relations).")
    (xdoc::li
     "Theorems about what stays the same
      from a version of Unicode to a later one:
      assigned code points, identifiers,
      and the normalization forms of text whose characters are assigned;
      and the list of what does change in the @('General_Category').
      See @(see versions).")
    (xdoc::li
     "Union, intersection, difference and complement
      of sets of code points that are given as lists of ranges,
      for models that define their own sets of characters
      and for comparing a property between versions:
      see @(see range-operations)."))
   (xdoc::p
    "What the library models of each Unicode specification,
     and what it does not model,
     is listed in @(see unicode-coverage).")
   (xdoc::p
    "This library does not deal with encodings either.
     The library @(see acl2::unicode) (in @('[books]/unicode'))
     has a verified UTF-8 decoder and encoder,
     and @('[books]/kestrel/unicode-light') has
     lightweight utilities for UTF-8 and UTF-16;
     the book @('utf-8') of this library
     connects the code points here to the former.")
   (xdoc::h3 "Including parts of the library")
   (xdoc::p
    "The book @('top') has everything,
     but each part can be included on its own,
     which brings in only the books it depends on
     and the tables of its own properties:")
   (xdoc::ul
    (xdoc::li
     "@('kestrel/unicode/code-points') for the code points and scalar values.")
    (xdoc::li
     "@('kestrel/unicode/xid') for @(tsee xid-start-p),
      @(tsee xid-continue-p) and @(tsee xid-identifier-p).")
    (xdoc::li
     "@('kestrel/unicode/general-category')
      for @(tsee code-point-general-category), @(tsee assigned-p)
      and @(tsee general-category-ranges);
      @('kestrel/unicode/general-category-changes')
      for @(tsee general-category-changes)
      and the theorem that the @('General_Category')
      of an assigned code point is the same in every later version,
      with one exception.
      It loads @('general-category') and @('range-operations').")
    (xdoc::li
     "@('kestrel/unicode/range-operations')
      for @(tsee ranges-union), @(tsee ranges-intersection),
      @(tsee ranges-difference) and @(tsee ranges-complement).
      It loads no tables.")
    (xdoc::li
     "@('kestrel/unicode/id') for @(tsee id-start-p)
      and @(tsee id-continue-p), which loads @('xid');
      @('kestrel/unicode/id-compat-math')
      for @(tsee id-compat-math-start-p)
      and @(tsee id-compat-math-continue-p).")
    (xdoc::li
     "@('kestrel/unicode/scripts') for @(tsee code-point-script)
      and @(tsee code-point-script-extensions);
      @('kestrel/unicode/bidi-class')
      for @(tsee code-point-bidi-class),
      which loads @('bidi-controls');
      @('kestrel/unicode/blocks') for @(tsee code-point-block);
      @('kestrel/unicode/emoji') for @(tsee emoji-p)
      and the other emoji properties;
      @('kestrel/unicode/decimal-digits')
      for @(tsee decimal-digit-value).")
    (xdoc::li
     "@('kestrel/unicode/identifier-status')
      for @(tsee identifier-allowed-p)
      and @(tsee code-point-identifier-types);
      @('kestrel/unicode/identifier-status-normalization')
      for the theorems that relate them to Normalization Form KC,
      which loads @('normalization').")
    (xdoc::li
     "@('kestrel/unicode/confusables') for @(tsee prototype);
      @('kestrel/unicode/skeleton') for @(tsee internal-skeleton),
      @(tsee skeleton) and @(tsee confusable-p),
      which loads @('confusables'), @('normalization'),
      @('default-ignorable') and @('right-to-left-free');
      @('kestrel/unicode/bidi-skeleton') for @(tsee bidi-skeleton)
      and @(tsee bidi-confusable-p),
      which loads @('skeleton') and the books
      of the bidirectional algorithm;
      @('kestrel/unicode/mixed-scripts')
      for @(tsee resolved-script-set) and @(tsee single-script-p),
      which loads @('scripts');
      @('kestrel/unicode/confusable-kinds')
      for @(tsee whole-script-confusable-p) and the other two classes,
      which loads @('skeleton') and @('mixed-scripts');
      @('kestrel/unicode/mixed-numbers')
      for @(tsee mixed-number-systems-p),
      which loads @('decimal-digits');
      @('kestrel/unicode/identifier-chunks')
      for @(tsee identifier-chunks),
      which loads @('general-category') and @('scripts').")
    (xdoc::li
     "@('kestrel/unicode/pattern-white-space')
      for @(tsee pattern-white-space-p),
      @('kestrel/unicode/white-space')
      for @(tsee white-space-p),
      and @('kestrel/unicode/pattern-syntax')
      for @(tsee pattern-syntax-p).")
    (xdoc::li
     "@('kestrel/unicode/default-ignorable'),
      @('kestrel/unicode/variation-selectors'),
      @('kestrel/unicode/join-controls'),
      @('kestrel/unicode/noncharacters'),
      @('kestrel/unicode/deprecated') and
      @('kestrel/unicode/prepended-concatenation-marks')
      for @(tsee default-ignorable-p), @(tsee variation-selector-p),
      @(tsee join-control-p), @(tsee noncharacter-p),
      @(tsee deprecated-p) and @(tsee prepended-concatenation-mark-p).")
    (xdoc::li
     "@('kestrel/unicode/bidi-controls') for @(tsee bidi-control-p),
      @(tsee bidi-explicit-formatting-p)
      and @(tsee bidi-explicit-formatting-class).")
    (xdoc::li
     "@('kestrel/unicode/bidi-brackets')
      for @(tsee code-point-bidi-bracket),
      and @('kestrel/unicode/bidi-mirroring')
      for @(tsee code-point-bidi-mirroring-glyph),
      which loads @('bidi-brackets').")
    (xdoc::li
     "@('kestrel/unicode/bidirectional-algorithm')
      for @(tsee bidi-levels), @(tsee bidi-display-order)
      and @(tsee bidi-display),
      which loads @('bidi-class'), @('bidi-brackets'),
      @('bidi-mirroring'), @('decompositions') and @('general-category').
      The rules are in seven books that it loads,
      from @('bidi-characters') to @('bidi-display'),
      and the theorems about them
      in @('bidi-rearrangement'), @('bidi-left-to-right'),
      @('bidi-confinement'), @('bidi-guarded-theorem')
      and @('bidi-self-contained'):
      see @(see bidirectional-algorithm).
      @('kestrel/unicode/right-to-left-free')
      for @(tsee right-to-left-free-p),
      which loads only @('bidi-class').
      @('kestrel/unicode/bidi-rule')
      for @(tsee bidi-rule-p), @(tsee bidi-rule-strict-p)
      and @(tsee bidi-rule-wide-p),
      which loads @('bidi-class'), @('bidi-brackets')
      and @('right-to-left-free'), and not the algorithm.
      @('kestrel/unicode/bidi-rule-display')
      for @(tsee bidi-name-display) and @(tsee bidi-name-read),
      which loads the rules of the algorithm up to the bracket pairs
      (@('bidi-neutral-types')) and not the rest.
      @('kestrel/unicode/bidi-rule-display-theorem')
      for the theorems that the algorithm displays a name
      that satisfies @(tsee bidi-rule-wide-p)
      as @(tsee bidi-name-display) says,
      which loads the whole algorithm.")
    (xdoc::li
     "@('kestrel/unicode/normalization') for @(tsee nfd), @(tsee nfc),
      @(tsee nfkd) and @(tsee nfkc),
      for the predicates that say that a list is in one of these forms,
      such as @(tsee nfc-memberp),
      for @(tsee canonical-equivalent-p)
      and @(tsee compatibility-equivalent-p),
      and for what the forms are made of.
      This is the largest part.")
    (xdoc::li
     "@('kestrel/unicode/composing-pairs')
      for @(tsee composes-with-following-p)
      and @(tsee composes-with-previous-p);
      @('kestrel/unicode/normalization-inert')
      for @(tsee normalization-inert-p) and the theorems
      that each form normalizes separately
      what is before and what is after an inert code point;
      @('kestrel/unicode/normalization-members') for the theorems
      about the code points that occur in a form of a list;
      @('kestrel/unicode/stream-safe')
      for @(tsee stream-safe-p) and @(tsee stream-safe-process);
      and @('kestrel/unicode/normalization-across-versions')
      for the theorems that the forms of text
      whose characters are assigned in a version of Unicode
      are the same in every later version,
      which also loads @('general-category').
      Each of these loads @('normalization').")
    (xdoc::li
     "@('kestrel/unicode/identifier-closure') for the theorems
      that normalizing an identifier gives an identifier.
      It loads @('xid') and @('normalization').")
    (xdoc::li
     "@('kestrel/unicode/quick-check') for the quick check properties.")
    (xdoc::li
     "@('kestrel/unicode/quick-check-theorems') for the theorems
      that relate the quick check properties to the normalization forms.
      It loads @('quick-check') and @('normalization').")
    (xdoc::li
     "@('kestrel/unicode/utf-8') for the theorems that connect this library
      to the UTF-8 decoder of @('[books]/unicode'), which it loads.")
    (xdoc::li
     "@('kestrel/unicode/property-relations') for the theorems
      that relate properties to each other.
      It loads the books of all the properties that it relates."))
   (xdoc::p
    "A model of a language whose identifiers follow [UAX #31]
     typically needs @('xid');
     @('normalization') if it normalizes or compares identifiers,
     and then @('identifier-closure') for the theorems
     that what it normalizes is still an identifier,
     and @('normalization-inert') for the theorems
     that normalization does not reach across its delimiters;
     @('normalization-across-versions') if it is to show
     that its programs mean the same
     when the implementation moves to a later version of Unicode;
     @('general-category') if its identifiers or its white space
     are defined by general categories;
     and @('pattern-white-space'), @('bidi-controls')
     and the books of the other properties
     if its white space or the characters that it rejects
     are defined by those properties.
     None of these loads the tests.
     A book in another package can call the functions of this library
     with the package prefix once it has included the book;
     to import their names into another package,
     the file that defines that package has to include
     @('kestrel/unicode/portcullis') first.
     The property functions take code points,
     so a model that has its own type of code points or scalar values
     needs a theorem that its values are code points of this library.
     See the file @('README.md') for more.")
   (xdoc::h3 "Versions")
   (xdoc::p
    "The properties of code points depend on the version of Unicode.
     Every function of this library that depends on the version
     takes it as an explicit argument;
     there is no default version and no notion of latest version.
     See @(see versions).")
   (xdoc::h3 "Data")
   (xdoc::p
    "The tables in the @('data') directory are generated,
     by the script @('tools/generate-ucd-books.py'),
     from the files of the Unicode Character Database
     of each supported version.
     Each generated book says which file it comes from,
     with the URL of the file and the SHA-256 of its contents.
     Derived properties are read from the derived files of the database;
     they are not recomputed.
     See the file @('README.md') for how to regenerate the tables
     and how to add a version.")
   (xdoc::p
    "Three of the generated books are not from that database:
     the tables of @('Identifier_Status') and @('Identifier_Type')
     and the table of the prototypes of confusable characters
     are generated from three data files
     of Unicode Technical Standard #39,
     which are published for each version of Unicode.")
   (xdoc::p
    "The tables are lists of ranges of code points,
     tree maps from code points to values,
     or lists of runs of code points with the same value,
     with fixtypes that are checked when the books are certified:
     see @(see tables).
     A few sets of code points that are computed from the tables
     are tree sets: see @(tsee code-point-set).")
   (xdoc::h3 "Representation")
   (xdoc::p
    "Code points are natural numbers, never ACL2 characters.
     All the functions are in logic mode and guard-verified.")
   (xdoc::h3 "Validation")
   (xdoc::p
    "The books in the @('tests') directory run, when they are certified,
     the whole normalization conformance test
     of the Unicode Character Database,
     for each supported version.
     In addition, the results of the functions of this library
     on every code point have been compared with those of
     independent implementations of the same versions of Unicode:
     the Rust crates that the Rust compiler uses,
     and the Python standard library.
     The tools for that are in the @('validation') directory,
     and the file @('README.md') says how to run them
     and what was compared.")
   (xdoc::h3 "References")
   (xdoc::p
    "In the documentation of this library,
     [Unicode] refers to the core specification of the Unicode Standard,
     whose definitions are numbered D1, D2, etc.,
     and whose conformance clauses are numbered C1, C2, etc.;
     and [UAX #n] refers to the Unicode Standard Annex with that number:
     [UAX #9] is the Unicode Bidirectional Algorithm,
     [UAX #15] is Unicode Normalization Forms,
     [UAX #24] is Unicode Script Property,
     [UAX #31] is Unicode Identifiers and Syntax,
     and [UAX #44] is the Unicode Character Database.
     [UTS #n] refers to the Unicode Technical Standard with that number:
     [UTS #39] is Unicode Security Mechanisms,
     [UTS #46] is Unicode IDNA Compatibility Processing,
     [UTS #51] is Unicode Emoji
     and [UTS #55] is Unicode Source Code Handling.
     [RFC n] refers to the Request for Comments with that number,
     of the Internet Engineering Task Force:
     [RFC 5892] is The Unicode Code Points
     and Internationalized Domain Names for Applications (IDNA),
     and [RFC 5893] is Right-to-Left Scripts
     for Internationalized Domain Names for Applications (IDNA).
     [Stability] refers to the "
    (xdoc::ahref "https://unicode.org/policies/stability_policy.html"
                 "Unicode Character Encoding Stability Policies")
    ", which say what will not change in later versions of the standard;
     its policies are cited by their names."))
  :order-subtopics (code-points
                    versions
                    xid
                    id-properties
                    normalization
                    identifier-closure
                    identifier-status
                    confusables
                    confusable-detection
                    mixed-script-detection
                    mixed-number-detection
                    identifier-word-boundaries
                    scripts
                    pattern-white-space
                    white-space
                    bidi-controls
                    bidi-class-property
                    bidi-paired-brackets
                    bidi-mirroring
                    bidirectional-algorithm
                    tables))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tables
  :parents (unicode)
  :short "Representations of the tables
          of the Unicode Character Database."
  :long
  (xdoc::topstring
   (xdoc::p
    "The data of this library is in tables of three kinds:")
   (xdoc::ul
    (xdoc::li
     "Lists of ranges of code points, for the binary properties:
      see @(see ranges).")
    (xdoc::li
     "Maps from code points to values,
      for the properties that have a value
      that most code points share:
      see @(see maps).")
    (xdoc::li
     "Lists of runs of code points with the same value,
      for the properties that have no such value,
      such as @('General_Category') and @('Script'),
      and for the properties whose values are sets,
      such as @('Script_Extensions'):
      see @(see runs).
      Each of these properties has a topic
      for the type of its values and for its runs:
      @(see general-category-tables), @(see script-tables),
      @(see bidi-class-tables), @(see block-tables)
      and @(see identifier-type-tables)."))
   (xdoc::p
    "All three kinds are fixtypes:
     a range is a product of two code points,
     a run is a product of two code points and a value,
     and the maps are @(see treemap::treemap)s
     whose keys and values have fixtypes.
     Every generated table is built with the constructors of its type,
     in the book that defines it,
     and the tables that are computed from the generated ones
     are checked against the recognizers of their types.
     For each table
     there is a function that selects the table of a version of Unicode
     and that returns a value of the type.")
   (xdoc::p
    "Membership in a list of ranges takes time linear in the number of ranges,
     and so does a lookup in a list of runs.
     A lookup in a map takes time logarithmic in the size of the map.")
   (xdoc::p
    "Lists of ranges can be combined as sets of code points,
     with union, intersection, difference and complement:
     see @(see range-operations)."))
  :order-subtopics (ranges
                    range-operations
                    maps
                    runs
                    general-category-tables
                    script-tables
                    bidi-class-tables
                    block-tables
                    identifier-type-tables))
