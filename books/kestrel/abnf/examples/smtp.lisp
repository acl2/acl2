; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-definer/defgrammar")
(include-book "../operations/in-terminal-set")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *smtp-grammar-rules*
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
  :file "smtp.abnf"
  :untranslate t
  :well-formedness t)
