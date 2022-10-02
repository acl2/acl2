; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "uri")

; (depends-on "http-grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ http-example
  :parents (examples)
  :short "The ABNF grammar of
          the HTTP (Hypertext Transfer Protocol) 1.1 syntax."
  :long
  (xdoc::topstring-p
   "The HTTP 1.1 syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "RFC 7230")
   ".")
  :order-subtopics t
  :default-parent t)

(defsection *http-grammar-rules*
  :short "The HTTP grammar rules from RFC 7230."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('http-grammar.abnf') contains the HTTP grammar rules,
     copied and pasted from RFC 7230.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the HTTP grammar rules,
     excluding the referenced URI rules and ABNF core rules.")
   (xdoc::p
    "The HTTP grammar rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "http-grammar.abnf") state)
     (value `(defconst *http-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *http-grammar-rules*)

  (defrule rulelist-wfp-of-*http-grammar-rules*
    (rulelist-wfp *http-grammar-rules*)))

(defval *all-http-grammar-rules*
  :short "All the HTTP grammar rules,
          including the referenced URI rules and ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The HTTP grammar rules include rules defined by prose notation
     that refer to the URI grammar rules.
     To obtain the complete HTTP grammar rules,
     we plug into the HTTP rules the URI grammar rules.
     Since the rule @('uri-host') in the HTTP grammar
     is defined by prose that references the rule @('host') in the URI grammar,
     before the plugging operation
     we rename @('host') to @('uri-host') in the URI grammar rules.
     Finally, we plug the ABNF core rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed,
     and generate terminal strings consisting only of octets.")
   (xdoc::p
    "Section 1.2 of RFC 7230 lists a number of ABNF core rules
     that are included by reference in the HTTP grammar rules.
     With the exception of @('CTL'),
     those are exactly the ABNF core rules
     present in the complete HTTP grammar rules.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (plug-rules (plug-rules *http-grammar-rules*
                          (rulelist-rename-rule *uri-grammar-rules*
                                                (rulename "host")
                                                (rulename "uri-host")))
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-http-grammar-rules*)

  (defrule rulelist-wfp-of-*all-http-grammar-rules*
    (rulelist-wfp *all-http-grammar-rules*))

  (defrule rulelist-closedp-of-*all-http-grammar-rules*
    (rulelist-closedp *all-http-grammar-rules*))

  (defrule octet-only-*all-http-grammar-rules*
    (rulelist-in-termset-p *all-http-grammar-rules*
                           (integers-from-to 0 255)))

  (defrule abnf-core-rules-in-*all-http-grammar-rules*
    (implies (member-equal core-rule *core-rules*)
             (iff (member-equal core-rule *all-http-grammar-rules*)
                  (member-equal core-rule (list *rule_ALPHA*
                                                *rule_CR*
                                                *rule_CRLF*
                                                *rule_DIGIT*
                                                *rule_DQUOTE*
                                                *rule_HEXDIG*
                                                *rule_HTAB*
                                                *rule_LF*
                                                *rule_OCTET*
                                                *rule_SP*
                                                *rule_VCHAR*))))
    :rule-classes nil))

(defval *all-http-message-grammar-rules*
  :short "All the HTTP grammar rules
          that define the first-level structure of messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the top-level rule @('HTTP-message') that defines messages,
     not all the rules in @(tsee *all-http-grammar-rules*) are reached
     when generating strings of terminals.
     The rules that are not reached serve to define
     the format of certain field values and
     the format for the chunked transfer coding.")
   (xdoc::p
    "The rules reached starting from @('HTTP-message') provide
     a first-level definition of messages.
     According to these rules, strings of terminals (octets)
     are parsed into trees rooted at @('HTTP-message').
     In these parse trees, field values are ``opaque'',
     i.e. they are essentially unstructured sequences of certain octets,
     according to the @('field-content') rule.
     These field values can be parsed further according to the other rules.")
   (xdoc::p
    "The rules reached starting from @('HTTP-message')
     are well-formed and closed.
     Since they are a subset of @(tsee *all-http-grammar-rules*),
     they also generate terminal strings consisting only of octets."))
  (trans-rules-of-names (list (rulename "HTTP-message"))
                        *all-http-grammar-rules*)
  ///

  (defrule rulelist-wfp-of-*all-http-message-grammar-rules*
    (rulelist-wfp *all-http-message-grammar-rules*))

  (defrule rulelist-closedp-of-*all-http-message-grammar-rules*
    (rulelist-closedp *all-http-message-grammar-rules*)))
