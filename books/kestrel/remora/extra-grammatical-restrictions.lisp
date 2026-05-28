; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "grammar")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ extra-grammatical-restrictions
  :parents (concrete-syntax)
  :short "Extra-grammatical restrictions on the syntax of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF @(see grammar) captures
     most of the syntactic requirements of Remora,
     but not all of them;
     this is very commonly the case in languages.
     To provide a complete formal specification of the Remora syntax,
     we complement the grammar with extra-grammatical restrictions,
     expressed as predicates over CSTs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk cst-identifier-like-keyword-p ((cst-ident abnf::treep))
  :guard (cst-matchp cst-ident "identifier")
  :returns (yes/no booleanp)
  :short "Check if an @('identifier') CST
          has the same fringe as some @('keyword') CST."
  (exists (cst-keywd)
          (and (abnf::treep cst-keywd)
               (cst-matchp cst-keywd "keyword")
               (equal (abnf::tree->string cst-keywd)
                      (abnf::tree->string cst-ident)))))

(define-sk cst-identifiers-not-keywords-p ((cst abnf::treep))
  :returns (yes/no booleanp)
  :short "Check if a CST does not contain any @('identifier') CSTs
          that have the same fringe as some @('keyword') CSTs."
  (forall (cst-ident)
          (implies (and (set::in cst-ident (abnf::trees-in-tree cst))
                        (cst-matchp cst-ident "identifier"))
                   (not (cst-identifier-like-keyword-p cst-ident)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: add more predicates on CSTs
