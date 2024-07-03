; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "kestrel/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "kestrel/abnf/grammar-definer/deftreeops" :dir :system)
(include-book "kestrel/abnf/operations/in-terminal-set" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (concrete-syntax)
  :short "An ABNF grammar of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the documentation comments in @('grammar.abnf')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The ABNF grammar represented in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use our verified grammar parser and our abstractor
     to turn the grammar in the @('grammar.abnf') file
     into an ACL2 representation.")
   (xdoc::p
    "We use @(tsee acl2::add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output.")
   (xdoc::p
    "We show that the grammar is well-formed, closed, and Unicode."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled unicode-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar*
                                 (acl2::integers-from-to 0 #x10ffff))
    :enable (abnf::rule-in-termset-p
             abnf::repetition-in-termset-p
             abnf::element-in-termset-p
             abnf::num-val-in-termset-p
             abnf::char-val-in-termset-p
             abnf::char-insensitive-in-termset-p
             abnf::char-sensitive-in-termset-p)
    :disable ((:e acl2::integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::deftreeops *grammar* :prefix cst)
