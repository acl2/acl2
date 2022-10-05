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
(include-book "../operations/top")
(include-book "../core-rules")
(include-book "../concrete-syntax")
(include-book "../parser")
(include-book "../abstractor")

; (depends-on "uri.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uri-example
  :parents (examples)
  :short "The ABNF grammar of the URI (Uniform Resource Identifier) syntax."
  :long
  (xdoc::topstring-p
   "The URI syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
   ".")
  :order-subtopics t
  :default-parent t)

(defsection *uri-grammar-rules*
  :short "The URI grammar rules from RFC 3986."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('uri.abnf') contains the URI grammar rules,
     copied and pasted from RFC 3986.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the URI grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The URI grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "uri.abnf") state)
     (value `(defconst *uri-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *uri-grammar-rules*)

  (defrule rulelist-wfp-of-*uri-grammar-rules*
    (rulelist-wfp *uri-grammar-rules*)))

(defval *all-uri-grammar-rules*
  :short "All the URI grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are obtained by plugging the core rules into the URI rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed.
     They generate terminal strings consisting only of ASCII codes;
     more precisely, the ASCII codes of
     all the visible characters (i.e. @('VCHAR') in the ABNF core rules)
     except
     double quote,
     angle brackets,
     backslash,
     caret,
     curly braces, and
     vertical bar.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (plug-rules *uri-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-uri-grammar-rules*)

  (defrule rulelist-wfp-of-*all-uri-grammar-rules*
    (rulelist-wfp *all-uri-grammar-rules*))

  (defrule rulelist-closedp-of-*all-uri-grammar-rules*
    (rulelist-closedp *all-uri-grammar-rules*))

  (defrule ascii-only-*all-uri-grammar-rules*
    (rulelist-in-termset-p *all-uri-grammar-rules*
                           (integers-from-to 0 127)))

  (defrule precise-ascii-codes-of-*all-uri-grammar-rules*
    (rulelist-in-termset-p *all-uri-grammar-rules*
                           (difference (integers-from-to 33 126)
                                       (list (char-code #\")
                                             (char-code #\<)
                                             (char-code #\>)
                                             (char-code #\\)
                                             (char-code #\^)
                                             (char-code #\{)
                                             (char-code #\|)
                                             (char-code #\}))))))
