; JSON Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "kestrel/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "kestrel/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "kestrel/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/abnf/operations/plugging" :dir :system)

(local (include-book "kestrel/utilities/integers-from-to-as-set" :dir :system))

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "The ABNF grammar of JSON."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar-rules*
  :short "The JSON grammar rules from RFC 8259."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('grammar.abnf') contains the grammar rules,
     copied and pasted from RFC 8259.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the JSON grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The JSON grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-grammar-rules*
  :short "All the JSON grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are obtained by plugging the core rules into the IMAP rules.")
   (xdoc::p
    "These rules are well-formed and closed.")
   (xdoc::p
    "These rules generate terminal strings consisting only of Unicode codes,
     i.e. natural numbers between 0 and @('x10FFFF').
     Proving this by execution would take a long time
     due to the specification-appropriate but execution-inefficient
     definition of @(tsee abnf::rulelist-in-termset-p)
     and to the relatively large size of the range of natural numbers.
     Thus, we prove the theorems (quickly)
     by disabling the executable counterpart of @(tsee acl2::integers-from-to)
     and by using library theorems that relate @(tsee acl2::integers-from-to)
     to @(tsee in) and @(tsee set::list-in).")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (abnf::plug-rules *grammar-rules*
                    abnf::*core-rules*)
  ///

  (acl2::add-const-to-untranslate-preprocess *all-grammar-rules*)

  (defrule rulelist-wfp-of-*all-grammar-rules*
    (abnf::rulelist-wfp *all-grammar-rules*))

  (defrule rulelist-closedp-of-*all-grammar-rules*
    (abnf::rulelist-closedp *all-grammar-rules*))

  (defrule unicode-only-*all-grammar-rules*
    (abnf::rulelist-in-termset-p *all-grammar-rules*
                                 (acl2::integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p)
    :disable ((:e acl2::integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *all-grammar-rules* :prefix cst)
