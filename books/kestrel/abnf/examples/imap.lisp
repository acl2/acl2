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
(include-book "../operations")
(include-book "../core-rules")
(include-book "../concrete-syntax")
(include-book "../parser")
(include-book "../abstractor")

; (depends-on "imap-grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imap-example
  :parents (examples)
  :short "The ABNF grammar of
          the IMAP (Internet Message Access Protocol) 4rev1 syntax."
  :long
  (xdoc::topstring-p
   "The IMAP 4rev1 syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc3501" "RFC 3501")
   ".")
  :order-subtopics t)

(defsection *imap-grammar-rules*
  :parents (imap-example)
  :short "The IMAP grammar rules from RFC 3501."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('imap-grammar.abnf') contains the grammar rules,
     copied and pasted from RFC 3501.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the IMAP grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The IMAP grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "imap-grammar.abnf") state)
     (value `(defconst *imap-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *imap-grammar-rules*)

  (defrule rulelist-wfp-of-*imap-grammar-rules*
    (rulelist-wfp *imap-grammar-rules*)))
