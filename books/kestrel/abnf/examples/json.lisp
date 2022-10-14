; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../abstract-syntax")
(include-book "../semantics")
(include-book "../operations/well-formedness")
(include-book "../operations/closure")
(include-book "../operations/in-terminal-set")
(include-book "../operations/plugging")
(include-book "../core-rules")
(include-book "../concrete-syntax")
(include-book "../parser")
(include-book "../syntax-abstraction")

; (depends-on "json.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json-example
  :parents (examples)
  :short "The ABNF grammar of the JSON (JavaScript Object Notation) syntax."
  :long
  (xdoc::topstring-p
   "The JSON syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc7159" "RFC 7159")
   ".")
  :order-subtopics t
  :default-parent t)

(defsection *json-grammar-rules*
  :short "The JSON grammar rules from RFC 7159."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('json.abnf') contains the grammar rules,
     copied and pasted from RFC 7159.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the JSON grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The JSON grammar rules are well-formed and closed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "json.abnf") state)
     (value `(defconst *json-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *json-grammar-rules*)

  (defrule rulelist-wfp-of-*json-grammar-rules*
    (rulelist-wfp *json-grammar-rules*)))

(defval *all-json-grammar-rules*
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
     definition of @(tsee rulelist-in-termset-p)
     and to the relatively large size of the range of natural numbers.
     Thus, we prove the theorems (quickly)
     by disabling the executable counterpart of @(tsee integers-from-to)
     and by using library theorems that relate @(tsee integers-from-to)
     to @(tsee in) and @(tsee list-in).")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (plug-rules *json-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-json-grammar-rules*)

  (defrule rulelist-wfp-of-*all-json-grammar-rules*
    (rulelist-wfp *all-json-grammar-rules*))

  (defrule rulelist-closedp-of-*all-json-grammar-rules*
    (rulelist-closedp *all-json-grammar-rules*))

  (defrule unicode-only-*all-json-grammar-rules*
    (rulelist-in-termset-p *all-json-grammar-rules*
                           (integers-from-to 0 #x10ffff))
    :enable (rule-in-termset-p
             repetition-in-termset-p
             element-in-termset-p
             num-val-in-termset-p
             char-val-in-termset-p
             char-insensitive-in-termset-p)
    :disable ((:e integers-from-to))
    :prep-books
    ((local
      (include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)))))
