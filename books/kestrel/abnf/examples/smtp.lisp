; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/abstract-syntax")
(include-book "../notation/semantics")
(include-book "../operations/well-formedness")
(include-book "../operations/closure")
(include-book "../operations/in-terminal-set")
(include-book "../notation/core-rules")
(include-book "../notation/concrete-syntax")
(include-book "../grammar-parser/executable")
(include-book "../notation/syntax-abstraction")

; (depends-on "smtp.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ smtp-example
  :parents (examples)
  :short "The ABNF grammar of the SMTP (Simple Mail Transfer Protocol) syntax."
  :long
  (xdoc::topstring-p
   "The SMTP syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc5321" "RFC 5321")
   ".")
  :order-subtopics t
  :default-parent t)

(defsection *smtp-grammar-rules*
  :short "The SMTP grammar rules from RFC 5321."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('smtp.abnf') contains the grammar rules,
     copied and pasted from RFC 5321.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the SMTP grammar rules,
     excluding the referenced IMF rules and ABNF core rules.")
   (xdoc::p
    "The SMTP grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "smtp.abnf") state)
     (value `(defconst *smtp-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *smtp-grammar-rules*)

  (defrule rulelist-wfp-of-*smtp-grammar-rules*
    (rulelist-wfp *smtp-grammar-rules*)))
