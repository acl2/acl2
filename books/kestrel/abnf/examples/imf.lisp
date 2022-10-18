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

(defsection *imf-grammar-rules*
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

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "imf.abnf") state)
     (value `(defconst *imf-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *imf-grammar-rules*)

  (defrule rulelist-wfp-of-*imf-grammar-rules*
    (rulelist-wfp *imf-grammar-rules*)))
