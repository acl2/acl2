; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "imf")
(include-book "../operations/renaming")

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
    "We keep this constant unexpanded in output."))
  :file "smtp.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-smtp-grammar-rules*
  :short "All the SMTP grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The SMTP grammar references @('FWS') and @('CFWS'),
     which are defined in the IMF grammar, as stated in RFC 5321.
     To obtain the complete SMTP rules,
     we plug into the SMTP rules the IMF rules.
     The two grammars have different definitions for certain rule names,
     but presumably those should be considered in different ``name spaces'';
     we handle this by renaming the conflicting rule names in the IMF grammar.
     Finally, we plug the ABNF core rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed.
     They generate terminal strings consisting only of ASCII codes")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  (plug-rules (plug-rules *smtp-grammar-rules*
                          (rulelist-rename-rule
                           (rulelist-rename-rule
                            (rulelist-rename-rule
                             (rulelist-rename-rule
                              *imf-grammar-rules*
                              (rulename "local-part")
                              (rulename "imf-local-part"))
                             (rulename "quoted-string")
                             (rulename "imf-quoted-string"))
                            (rulename "domain")
                            (rulename "imf-domain"))
                           (rulename "atom")
                           (rulename "imf-atom")))
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-smtp-grammar-rules*)

  (defrule rulelist-wfp-of-*all-smtp-grammar-rules*
    (rulelist-wfp *all-smtp-grammar-rules*))

  (defrule rulelist-closedp-of-*all-smtp-grammar-rules*
    (rulelist-closedp *all-smtp-grammar-rules*))

  (defrule ascii-only-*all-smtp-grammar-rules*
    (rulelist-in-termset-p *all-smtp-grammar-rules*
                           (integers-from-to 0 127)))

  (defrule abnf-core-rules-in-*all-smtp-grammar-rules*
    (implies (member-equal core-rule *core-rules*)
             (iff (member-equal core-rule *all-smtp-grammar-rules*)
                  (member-equal core-rule (list *rule_ALPHA*
                                                *rule_CR*
                                                *rule_CRLF*
                                                *rule_DIGIT*
                                                *rule_DQUOTE*
                                                *rule_HEXDIG*
                                                *rule_HTAB*
                                                *rule_LF*
                                                *rule_SP*
                                                *rule_VCHAR*
                                                *rule_WSP*))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftreeops *all-smtp-grammar-rules* :prefix smtp-cst)
