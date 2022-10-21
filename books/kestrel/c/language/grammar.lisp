; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/abnf/grammar-definer/defgrammar" :dir :system)
(include-book "kestrel/abnf/operations/in-terminal-set" :dir :system)

; (depends-on "grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ grammar
  :parents (language)
  :short "A grammar for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "See the documentation comments in @('grammar.abnf')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(abnf::defgrammar *grammar*
  :short "The grammar of C, in ACL2."
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
    "We show that the grammar is well-formed, closed, and ASCII."))
  :file "grammar.abnf"
  :untranslate t
  :well-formed t
  :closed t
  ///

  (defruled ascii-only-*grammar*
    (abnf::rulelist-in-termset-p *grammar* (acl2::integers-from-to 0 127))))
