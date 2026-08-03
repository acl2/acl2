; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/tree-operations/deftreeops" :dir :system)

(include-book "../portcullis")

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ir-grammar
  :parents (concrete-syntax parsing-and-printing)
  :short "ABNF grammar for the Futhark textual subset emitted by Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the "
    (xdoc::seetopic "abnf::grammar-parser" "verified ABNF grammar parser")
    " to parse @('grammar.abnf') into an ACL2 grammar value.")
   (xdoc::p
    "The official Futhark language reference is at "
    (xdoc::ahref
     "https://futhark.readthedocs.io/en/stable/language-reference.html"
     "Futhark ReadTheDocs")
    ".  That document gives the grammar for ordinary Futhark source.")
   (xdoc::p
    "The current Remora compiler's @('futhark') mode prints Futhark SOACS IR
     text rather than ordinary Futhark source.  The grammar here therefore
     describes the Remora-emitted textual subset of that IR.  It recognizes
     the current Remora-pinned format and the older Futhark 0.25.34 entry and
     map forms retained by the parser tests; version-dependent alternatives
     are identified explicitly in @('grammar.abnf').")
   (xdoc::p
    "The ABNF source file itself is US-ASCII, as required by the ABNF
     standard.  The input language described by the grammar is a sequence of
     Unicode code points; non-ASCII source characters are represented in ABNF
     with numeric value notation and ranges."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "Parsed ABNF grammar for the Remora-emitted Futhark subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is generated from @('grammar.abnf').  The generated grammar
     is proved well formed and closed by @(tsee abnf::defgrammar).")
   (xdoc::p
    "The grammar is intentionally permissive in a few lexical positions,
     especially @('word').  The parser and syntax abstraction layer enforce
     the remaining side conditions described in @('grammar.abnf')."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar* :prefix cst)
