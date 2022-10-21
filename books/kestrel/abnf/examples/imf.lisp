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

; (depends-on "imf.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imf-example
  :parents (examples)
  :short "The ABNF grammar of the IMF (Internet Message Format) syntax."
  :long
  (xdoc::topstring-p
   "The IMF syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc5322" "RFC 5322")
   ".")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *imf-grammar-rules*
  :short "The IMF grammar rules from RFC 5322."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('imf.abnf') contains the IMF grammar rules,
     copied and pasted from RFC 5322.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the IMF grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The IMF grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  :file "imf.abnf"
  :untranslate t
  :well-formedness t)
