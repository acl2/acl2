; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "xdoc/defxdoc-plus" :dir :system)

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
     Currently it has:")
   (xdoc::ul
    (xdoc::li
     "Code points and scalar values:
      see @(see code-points).")
    (xdoc::li
     "The @('XID_Start') and @('XID_Continue') properties,
      which define identifiers:
      see @(see xid).")
    (xdoc::li
     "The normalization forms NFD, NFC, NFKD and NFKC,
      with what they are made of:
      decompositions, combining classes, composition exclusions,
      and the algorithms for Hangul syllables:
      see @(see normalization).")
    (xdoc::li
     "The @('Pattern_White_Space') property,
      which defines white space:
      see @(see pattern-white-space).")
    (xdoc::li
     "The bidirectional control characters,
      which a lexer may have to reject or report:
      see @(see bidi-controls)."))
   (xdoc::p
    "It does not have the general category or the case mappings,
     which are to be added when a use needs them,
     nor collation, text segmentation, the bidirectional algorithm,
     or the confusables data, which are out of its scope.")
   (xdoc::p
    "This library does not deal with encodings either.
     The library @(see acl2::unicode) (in @('[books]/unicode'))
     has a verified UTF-8 decoder and encoder,
     and @('[books]/kestrel/unicode-light') has
     lightweight utilities for UTF-8 and UTF-16;
     the book @('utf-8') of this library
     connects the code points here to the former.")
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
    "The tables are sorted lists of ranges of code points,
     or sorted alists,
     with invariants that are checked when the books are certified:
     see @(see tables).")
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
     and [UAX #n] refers to the Unicode Standard Annex with that number:
     [UAX #9] is the Unicode Bidirectional Algorithm,
     [UAX #15] is Unicode Normalization Forms,
     [UAX #31] is Unicode Identifiers and Syntax,
     and [UAX #44] is the Unicode Character Database."))
  :order-subtopics (code-points
                    versions
                    xid
                    normalization
                    pattern-white-space
                    bidi-controls
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
     "Sets of code points, for the binary properties:
      see @(see range-sets).")
    (xdoc::li
     "Maps from code points to values that many code points share,
      for the enumerated and numeric properties:
      see @(see range-maps).")
    (xdoc::li
     "Maps from natural numbers to values:
      see @(see nat-maps)."))
   (xdoc::p
    "Each kind has a recognizer,
     which includes the invariant that the table is sorted
     and has no overlapping or duplicate entries.
     Every generated table is checked against its recognizer
     in the book that defines it,
     and the tables that are computed from the generated ones
     are checked in the same way.
     For each table, and each kind of table,
     there is a function that selects the table of a version of Unicode,
     with a theorem that says that the result satisfies the recognizer;
     the lookup functions are verified against those theorems.")
   (xdoc::p
    "Lookups are linear in the size of the table in the worst case,
     but they stop early, thanks to the sorting:
     they are fast for small code points, in particular for ASCII.
     Faster structures could replace the lists, behind the same functions,
     if a use needs them."))
  :order-subtopics (range-sets
                    range-maps
                    nat-maps))
