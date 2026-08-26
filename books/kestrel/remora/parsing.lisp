; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "unicode")
(include-book "extra-grammatical-restrictions")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parsing
  :parents (concrete-syntax)
  :short "Specification of parsing for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declarative, non-executable specification.
     It relates sequences of Unicode characters to CSTs,
     putting together the grammar and the extra-grammatical restrictions.")
   (xdoc::p
    "We formulate two specifications,
     one for top-level expressions,
     and one for files.
     Both are predicates that relate
     a list of Unicode character codes with a CST:
     each predicate holds exactly when
     the CST matches the applicable grammar rule,
     its fringe is the list of Unicode character codes,
     and the CST satisfies all the extra-grammatical restrictions.")
   (xdoc::p
    "It remains to prove that this specification makes parsing unambiguous.
     That is, for each predicate,
     given two CSTs that satisfy the predicate for the same Unicode sequence,
     the two CSTs must be equal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicodes-cst-expression-p ((ucodes acl2::ustring?) (cst abnf::treep))
  :returns (yes/no booleanp)
  :short "Check whether a list of Unicode character codes
          corresponds to a top-level expression CST."
  (and (cst-matchp cst "top-exp")
       (equal ucodes (abnf::tree->string cst))
       (cst-extra-grammatical-restrictions-p cst))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicodes-cst-file-p ((ucodes acl2::ustring?) (cst abnf::treep))
  :returns (yes/no booleanp)
  :short "Check whether a list of Unicode character codes
          corresponds to a file CST."
  (and (cst-matchp cst "file")
       (equal ucodes (abnf::tree->string cst))
       (cst-extra-grammatical-restrictions-p cst))
  :guard-hints (("Goal" :in-theory (enable cst-matchp$))))
