; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "abstract-syntax")
(include-book "semantics")
(include-book "operations")
(include-book "core-rules")
(include-book "concrete-syntax")
(include-book "parser")
(include-book "abstractor")

; (depends-on "uri-grammar.txt")
; (depends-on "http-grammar.txt")
; (depends-on "imf-grammar.txt")
; (depends-on "smtp-grammar.txt")
; (depends-on "imap-grammar.txt")
; (depends-on "json-grammar.txt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ examples
  :parents (abnf)
  :short "Some real-world examples of ABNF grammars."
  :long
  "<p>
   We take some real-world ABNF grammars,
   copied and pasted from official standards,
   and show that they are successfully processed by the
   <see topic='@(url grammar-parser)'>parser</see> and
   <see topic='@(url concrete-to-abstract-syntax)'>abstractor</see>.
   We also demonstrate the use of some @(see operations) on these grammars.
   </p>"
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uri-example
  :parents (examples)
  :short "The ABNF grammar of the URI (Uniform Resource Identifier) syntax."
  :long
  "<p>
   The URI syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc3986\">RFC 3968</a>.
   </p>"
  :order-subtopics t)

(defsection *uri-grammar-rules*
  :parents (uri-example)
  :short "The URI grammar rules from RFC 3986."
  :long
  "<p>
   The file @('uri-grammar.txt') contains the URI grammar rules,
   copied and pasted from RFC 3986.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the URI grammar rules,
   excluding the referenced ABNF core rules.
   </p>
   <p>
   The URI grammar rules are well-formed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "uri-grammar.txt") state)
     (value `(defconst *uri-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *uri-grammar-rules*)

  (defrule rulelist-wfp-of-*uri-grammar-rules*
    (rulelist-wfp *uri-grammar-rules*)))

(defval *all-uri-grammar-rules*
  :parents (uri-example)
  :short "All the URI grammar rules, including the referenced ABNF core rules."
  :long
  "<p>
   These are obtained by plugging the core rules into the URI rules.
   </p>
   <p>
   The resulting rules are well-formed and closed.
   They generate terminal strings consisting only of ASCII codes;
   more precisely, the ASCII codes of
   all the visible characters (i.e. @('VCHAR') in the ABNF core rules)
   except
   double quote,
   angle brackets,
   backslash,
   caret,
   curly braces, and
   vertical bar.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ http-example
  :parents (examples)
  :short "The ABNF grammar of
          the HTTP (Hypertext Transfer Protocol) 1.1 syntax."
  :long
  "<p>
   The HTTP 1.1 syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc7230\">RFC 7230</a>.
   </p>"
  :order-subtopics t)

(defsection *http-grammar-rules*
  :parents (http-example)
  :short "The HTTP grammar rules from RFC 7230."
  :long
  "<p>
   The file @('http-grammar.txt') contains the HTTP grammar rules,
   copied and pasted from RFC 7230.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the HTTP grammar rules,
   excluding the referenced URI rules and ABNF core rules.
   </p>
   <p>
   The HTTP grammar rules are well-formed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "http-grammar.txt") state)
     (value `(defconst *http-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *http-grammar-rules*)

  (defrule rulelist-wfp-of-*http-grammar-rules*
    (rulelist-wfp *http-grammar-rules*)))

(defval *all-http-grammar-rules*
  :parents (http-example)
  :short "All the HTTP grammar rules,
          including the referenced URI rules and ABNF core rules."
  :long
  "<p>
   The HTTP grammar rules include rules defined by prose notation
   that refer to the URI grammar rules.
   To obtain the complete HTTP grammar rules,
   we plug into the HTTP rules the URI grammar rules.
   Since the rule @('uri-host') in the HTTP grammar
   is defined by prose that references the rule @('host') in the URI grammar,
   before the plugging operation
   we rename @('host') to @('uri-host') in the URI grammar rules.
   Finally, we plug the ABNF core rules.
   </p>
   <p>
   The resulting rules are well-formed and closed,
   and generate terminal strings consisting only of octets.
   </p>
   <p>
   Section 1.2 of RFC 7230 lists a number of ABNF core rules
   that are included by reference in the HTTP grammar rules.
   With the exception of @('CTL'),
   those are exactly the ABNF core rules
   present in the complete HTTP grammar rules.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
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
  :parents (http-example)
  :short "All the HTTP grammar rules
          that define the first-level structure of messages."
  :long
  "<p>
   Starting from the top-level rule @('HTTP-message') that defines messages,
   not all the rules in @(tsee *all-http-grammar-rules*) are reached
   when generating strings of terminals.
   The rules that are not reached serve to define
   the format of certain field values and
   the format for the chunked transfer coding.
   </p>
   <p>
   The rules reached starting from @('HTTP-message') provide
   a first-level definition of messages.
   According to these rules, strings of terminals (octets)
   are parsed into trees rooted at @('HTTP-message').
   In these parse trees, field values are ``opaque'',
   i.e. they are essentially unstructured sequences of certain octets,
   according to the @('field-content') rule.
   These field values can be parsed further according to the other rules.
   </p>
   <p>
   The rules reached starting from @('HTTP-message') are well-formed and closed.
   Since they are a subset of @(tsee *all-http-grammar-rules*),
   they also generate terminal strings consisting only of octets.
   </p>"
  (trans-rules-of-names (list (rulename "HTTP-message"))
                        *all-http-grammar-rules*)
  ///

  (defrule rulelist-wfp-of-*all-http-message-grammar-rules*
    (rulelist-wfp *all-http-message-grammar-rules*))

  (defrule rulelist-closedp-of-*all-http-message-grammar-rules*
    (rulelist-closedp *all-http-message-grammar-rules*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imf-example
  :parents (examples)
  :short "The ABNF grammar of the IMF (Internet Message Format) syntax."
  :long
  "<p>
   The IMF syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc5322\">RFC 5322</a>.
   </p>"
  :order-subtopics t)

(defsection *imf-grammar-rules*
  :parents (imf-example)
  :short "The IMF grammar rules from RFC 5322."
  :long
  "<p>
   The file @('imf-grammar.txt') contains the IMF grammar rules,
   copied and pasted from RFC 5322.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the IMF grammar rules,
   excluding the referenced ABNF core rules.
   </p>
   <p>
   The IMF grammar rules are well-formed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "imf-grammar.txt") state)
     (value `(defconst *imf-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *imf-grammar-rules*)

  (defrule rulelist-wfp-of-*imf-grammar-rules*
    (rulelist-wfp *imf-grammar-rules*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ smtp-example
  :parents (examples)
  :short "The ABNF grammar of the SMTP (Simple Mail Transfer Protocol) syntax."
  :long
  "<p>
   The SMTP syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc5321\">RFC 5321</a>.
   </p>"
  :order-subtopics t)

(defsection *smtp-grammar-rules*
  :parents (smtp-example)
  :short "The SMTP grammar rules from RFC 5321."
  :long
  "<p>
   The file @('smtp-grammar.txt') contains the grammar rules,
   copied and pasted from RFC 5321.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the SMTP grammar rules,
   excluding the referenced IMF rules and ABNF core rules.
   </p>
   <p>
   The SMTP grammar rules are well-formed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "smtp-grammar.txt") state)
     (value `(defconst *smtp-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *smtp-grammar-rules*)

  (defrule rulelist-wfp-of-*smtp-grammar-rules*
    (rulelist-wfp *smtp-grammar-rules*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ imap-example
  :parents (examples)
  :short "The ABNF grammar of
          the IMAP (Internet Message Access Protocol) 4rev1 syntax."
  :long
  "<p>
   The IMAP 4rev1 syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc3501\">RFC 3501</a>.
   </p>"
  :order-subtopics t)

(defsection *imap-grammar-rules*
  :parents (imap-example)
  :short "The IMAP grammar rules from RFC 3501."
  :long
  "<p>
   The file @('imap-grammar.txt') contains the grammar rules,
   copied and pasted from RFC 3501.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the IMAP grammar rules,
   excluding the referenced ABNF core rules.
   </p>
   <p>
   The IMAP grammar rules are well-formed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "imap-grammar.txt") state)
     (value `(defconst *imap-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *imap-grammar-rules*)

  (defrule rulelist-wfp-of-*imap-grammar-rules*
    (rulelist-wfp *imap-grammar-rules*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ json-example
  :parents (examples)
  :short "The ABNF grammar of the JSON (JavaScript Object Notation) syntax."
  :long
  "<p>
   The JSON syntax is specified by
   <a href=\"https://www.rfc-editor.org/info/rfc7159\">RFC 7159</a>.
   </p>"
  :order-subtopics t)

(defsection *json-grammar-rules*
  :parents (json-example)
  :short "The JSON grammar rules from RFC 7159."
  :long
  "<p>
   The file @('json-grammar.txt') contains the grammar rules,
   copied and pasted from RFC 7159.
   The ABNF grammar parser and abstractor are used
   to build an ACL2 representation of the JSON grammar rules,
   excluding the referenced ABNF core rules.
   </p>
   <p>
   The JSON grammar rules are well-formed and closed.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"

  (make-event
   (mv-let (tree state)
     (parse-grammar-from-file (string-append (cbd) "json-grammar.txt") state)
     (value `(defconst *json-grammar-rules*
               (abstract-rulelist ',tree)))))

  (add-const-to-untranslate-preprocess *json-grammar-rules*)

  (defrule rulelist-wfp-of-*json-grammar-rules*
    (rulelist-wfp *json-grammar-rules*)))

(defval *all-json-grammar-rules*
  :parents (json-example)
  :short "All the JSON grammar rules, including the referenced ABNF core rules."
  :long
  "<p>
   These are obtained by plugging the core rules into the IMAP rules.
   </p>
   <p>
   These rules are well-formed and closed.
   </p>
   <p>
   These rules generate terminal strings consisting only of Unicode codes,
   i.e. natural numbers between 0 and @('x10FFFF').
   However, running this proof currently takes a long time
   due to the inefficient definition of @(tsee rulelist-in-termset-p)
   and to the relatively large size of the range of natural numbers.
   It remains to speed up this proof and include it here.
   </p>
   <p>
   We use @(tsee add-const-to-untranslate-preprocess)
   to keep this constant unexpanded in output.
   </p>"
  (plug-rules *json-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-json-grammar-rules*)

  (defrule rulelist-wfp-of-*all-json-grammar-rules*
    (rulelist-wfp *all-json-grammar-rules*))

  (defrule rulelist-closedp-of-*all-json-grammar-rules*
    (rulelist-closedp *all-json-grammar-rules*)))
