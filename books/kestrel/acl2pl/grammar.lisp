; ACL2 Programming Language Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "projects/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "projects/abnf/grammar-operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (acl2-programming-language)
  :short "ABNF grammar for ACL2's reader syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar consists of a lexical sub-grammar and a syntactic sub-grammar,
     both in the same ABNF grammar file.")
   (xdoc::p
    "The grammar specifies SBCL-specific behavior as the primary definition,
     with notes on CCL differences."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The grammar of ACL2's reader syntax, in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our verified ABNF grammar parser and our ABNF grammar abstractor
     to turn the grammar in the @('grammar.abnf') file
     into an ACL2 representation.")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output.")
   (xdoc::p
    "We show that the grammar is well-formed, closed, and
     uses only ISO-8859-1 bytes (0-255) as terminals."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t

  ///

  (defruled iso-8859-1-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar* (acl2::integers-from-to 0 255))))
