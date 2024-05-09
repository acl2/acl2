; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-definer/defgrammar")
(include-book "../grammar-definer/deftreeops")
(include-book "../operations/in-terminal-set")
(include-book "../operations/plugging")

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
    "We keep this constant unexpanded in output."))
  :file "imf.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-imf-grammar-rules*
  :short "All the IMF grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are obtained by plugging the core rules into the IMF rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed.
     They generate terminal strings consisting only of ASCII codes")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  (plug-rules *imf-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-imf-grammar-rules*)

  (defrule rulelist-wfp-of-*all-imf-grammar-rules*
    (rulelist-wfp *all-imf-grammar-rules*))

  (defrule rulelist-closedp-of-*all-imf-grammar-rules*
    (rulelist-closedp *all-imf-grammar-rules*))

  (defrule ascii-only-*all-imf-grammar-rules*
    (rulelist-in-termset-p *all-imf-grammar-rules*
                           (integers-from-to 0 127)))

  (defrule abnf-core-rules-in-*all-imf-grammar-rules*
    (implies (member-equal core-rule *core-rules*)
             (iff (member-equal core-rule *all-imf-grammar-rules*)
                  (member-equal core-rule (list *rule_ALPHA*
                                                *rule_CR*
                                                *rule_CRLF*
                                                *rule_DIGIT*
                                                *rule_DQUOTE*
                                                *rule_HTAB*
                                                *rule_LF*
                                                *rule_SP*
                                                *rule_VCHAR*
                                                *rule_WSP*))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftreeops *all-imf-grammar-rules* :prefix imf-cst)
