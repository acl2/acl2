; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "grammar")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar-operations
  :parents (concrete-syntax)
  :short "Operations on CSTs (concrete syntax trees)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently @(tsee abnf::deftreeops) works on fixed grammars,
     while our @(see grammar) is parameterized over the dialect.
     We plan to define @(tsee abnf::deftreeops)-like operations
     on our parameterized grammar,
     maybe eventually extending that tool to work on parameterized grammars.")
   (xdoc::p
    "This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As an initial baseline, we use ABNF::DEFTREEOPS on
; one instance of our parameterized grammar.
; We plan to generalize this.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *grammar-c17*
  :short "Grammar constant for the C17 dialect without extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since currently @(tsee abnf::deftreeops) (used below)
     only operates on grammar constants,
     we pick a particular C dialect to start,
     defining a grammar constant for it.
     We plan to generalize @(tsee abnf::deftreeops)
     to operate on parameterized grammars,
     specifically a function like @(tsee grammar-for)."))
  (grammar-for (c::make-dialect :std (c::standard-c17))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar-c17* :prefix c17-cst)
