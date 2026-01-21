; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM-EARLY")

(include-book "grammar")

(include-book "../../../leo/early-version/definition/unicode")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (early-version)
  :short "Concrete syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the concrete syntax of Aleo instructions,
     by providing a declarative definition of parsing
     that makes use of the ABNF grammar."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-parsep ((ucodes leo-early::unicode-listp) (tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Grammatical parsing."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF grammar of Aleo instructions specifies
     how a sequence of Unicode characters
     can be organized into a program, more precisely a program CST.
     This is the case when the fringe of the CST
     is the Unicode character sequence.")
   (xdoc::p
    "Given a Unicode character sequence @('ucodes')
     there may be zero or one or more CSTs
     that satisfy this predicate.
     If there is zero,
     @('ucodes') is not syntactically valid Aleo instructions code.
     If there is one or more,
     @('ucodes') may be syntactically valid Aleo instructions code,
     if additional requirements are satisfied."))
  (and (cst-matchp tree "program")
       (equal (leo-early::unicode-list->codepoint-list ucodes)
              (abnf::tree->string tree)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parsep ((ucodes leo-early::unicode-listp) (tree abnf::treep))
  :returns (yes/no booleanp)
  :short "Declarative parsing specification."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we just define this as
     the grammatical parsing captured by @(tsee grammar-parsep).")
   (xdoc::p
    "If for each @('ucodes') there were always at most one @('tree')
     such that that predicate holds,
     the grammar would be unambiguous,
     and parsing requirements would be completely defined by this predicate.
     However, the grammar is currently ambiguous.
     We plan to refine the grammar,
     and/or add extra-grammatical requirements,
     to refine this specification to one
     that unambiguously defines at one tree
     for each syntactically valid sequence of Unicode characters."))
  (grammar-parsep ucodes tree)
  :hooks (:fix))
