; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../editions")

(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ keywords
  :parents (syntax-for-tools)
  :short "Rust keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rust classifies keywords into three categories
     ["
    (xdoc::ahref "https://doc.rust-lang.org/1.87.0/reference/keywords.html"
                 "Reference: Keywords; rustc 1.87.0")
    "]:")
   (xdoc::ul
    (xdoc::li
     "Strict keywords: always keywords;
      they cannot be used as (non-raw) identifiers.
      Note that, unlike C, the boolean literals
      @('true') and @('false') are keywords.
      The 2024 edition adds @('gen') to this category.")
    (xdoc::li
     "Reserved keywords: not currently used by the language,
      but withheld from identifier use for future compatibility.")
    (xdoc::li
     "Weak keywords: contextual;
      they have special meaning only in certain positions
      (e.g. @('union') only directly before a name in an item position),
      and are ordinary identifiers everywhere else.
      Accordingly, they are lexed as identifiers,
      and it is the parser that gives them their special meaning;
      they are not included in @(see keyword-p)."))
   (xdoc::p
    "The lifetime @('\\'static') is also classified as a weak keyword
     by the Reference, but since lifetimes are a separate kind of token,
     it cannot be confused with an identifier
     and is not included in the tables here.")
   (xdoc::p
    "A raw identifier @('r#foo') allows a strict or reserved keyword
     to be used as an identifier,
     except for @('crate'), @('self'), @('super'), and @('Self');
     that exception is a lexer-level side condition,
     enforced where raw identifiers are lexed.
     The lone underscore @('_') is neither a keyword nor an identifier;
     it is its own token (see the token fixtypes).")
   (xdoc::p
    "Since editions 2021 and 2024 differ in keyword classification
     (@('gen')), the classification functions take an edition argument;
     see @(see rust::editions)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *strict-keywords-common*
  :short "Strict keywords common to the 2021 and 2024 editions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the 35 strict keywords of the 2015 edition
     plus @('async'), @('await'), and @('dyn'),
     which are strict in edition 2018 and later.
     The 2024 edition additionally has @('gen');
     see @(tsee strict-keywords)."))
  (list "as"
        "async"
        "await"
        "break"
        "const"
        "continue"
        "crate"
        "dyn"
        "else"
        "enum"
        "extern"
        "false"
        "fn"
        "for"
        "if"
        "impl"
        "in"
        "let"
        "loop"
        "match"
        "mod"
        "move"
        "mut"
        "pub"
        "ref"
        "return"
        "self"
        "Self"
        "static"
        "struct"
        "super"
        "trait"
        "true"
        "type"
        "unsafe"
        "use"
        "where"
        "while"))

(assert-event (string-listp *strict-keywords-common*))
(assert-event (equal (len *strict-keywords-common*) 38))
(assert-event (no-duplicatesp-equal *strict-keywords-common*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *reserved-keywords-common*
  :short "Reserved keywords common to the 2021 and 2024 editions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the 12 reserved keywords of the 2015 edition
     plus @('try'), which is reserved in edition 2018 and later."))
  (list "abstract"
        "become"
        "box"
        "do"
        "final"
        "macro"
        "override"
        "priv"
        "try"
        "typeof"
        "unsized"
        "virtual"
        "yield"))

(assert-event (string-listp *reserved-keywords-common*))
(assert-event (equal (len *reserved-keywords-common*) 13))
(assert-event (no-duplicatesp-equal *reserved-keywords-common*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *weak-keywords*
  :short "Weak keywords (identifier-shaped), in all supported editions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are lexed as ordinary identifiers;
     the parser recognizes them contextually.
     The weak keyword @('\\'static') is not included
     because it is a lifetime, not identifier-shaped;
     see @(see keywords)."))
  (list "macro_rules"
        "raw"
        "safe"
        "union"))

(assert-event (string-listp *weak-keywords*))
(assert-event (equal (len *weak-keywords*) 4))
(assert-event (no-duplicatesp-equal *weak-keywords*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The categories are pairwise disjoint, in both editions
; (i.e. even with the 2024 addition of "gen" to the strict keywords).

(assert-event (not (intersection-equal *strict-keywords-common*
                                       *reserved-keywords-common*)))
(assert-event (not (intersection-equal (cons "gen" *strict-keywords-common*)
                                       *reserved-keywords-common*)))
(assert-event (not (intersection-equal *weak-keywords*
                                       (append (cons "gen"
                                                     *strict-keywords-common*)
                                               *reserved-keywords-common*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strict-keywords ((edition rust::editionp))
  :returns (keywords string-listp)
  :short "Strict keywords of an edition."
  (rust::edition-case edition
                      :e2021 *strict-keywords-common*
                      :e2024 (cons "gen" *strict-keywords-common*)))

(assert-event (equal (len (strict-keywords (rust::edition-e2021))) 38))
(assert-event (equal (len (strict-keywords (rust::edition-e2024))) 39))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reserved-keywords ((edition rust::editionp))
  :returns (keywords string-listp)
  :short "Reserved keywords of an edition."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are currently the same in the 2021 and 2024 editions,
     but we keep the edition parameter
     for uniformity with @(tsee strict-keywords)."))
  (declare (ignore edition))
  *reserved-keywords-common*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define strict-keyword-p ((string stringp) (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Check if a string is a strict keyword in an edition."
  (and (member-equal (str-fix string) (strict-keywords edition)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define reserved-keyword-p ((string stringp) (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Check if a string is a reserved keyword in an edition."
  (and (member-equal (str-fix string) (reserved-keywords edition)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define weak-keyword-p ((string stringp))
  :returns (yes/no booleanp)
  :short "Check if a string is an (identifier-shaped) weak keyword."
  (and (member-equal (str-fix string) *weak-keywords*) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keyword-p ((string stringp) (edition rust::editionp))
  :returns (yes/no booleanp)
  :short "Check if a string is a strict or reserved keyword in an edition."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the words that a (non-raw) identifier must not be.
     Weak keywords are not included, since they are valid identifiers."))
  (or (strict-keyword-p string edition)
      (reserved-keyword-p string edition)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Spot checks of the edition-dependent classification.

(assert-event (strict-keyword-p "gen" (rust::edition-e2024)))
(assert-event (not (strict-keyword-p "gen" (rust::edition-e2021))))
(assert-event (strict-keyword-p "dyn" (rust::edition-e2021)))
(assert-event (strict-keyword-p "Self" (rust::edition-e2021)))
(assert-event (not (strict-keyword-p "SELF" (rust::edition-e2021))))
(assert-event (reserved-keyword-p "try" (rust::edition-e2021)))
(assert-event (keyword-p "true" (rust::edition-e2021)))
(assert-event (not (keyword-p "union" (rust::edition-e2024))))
(assert-event (weak-keyword-p "union"))
(assert-event (not (weak-keyword-p "fn")))
(assert-event (not (keyword-p "_" (rust::edition-e2024))))
