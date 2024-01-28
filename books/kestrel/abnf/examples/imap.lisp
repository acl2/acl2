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

; (depends-on "imap.abnf")

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
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *imap-grammar-rules*
  :short "The IMAP grammar rules from RFC 3501."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('imap.abnf') contains the grammar rules,
     copied and pasted from RFC 3501.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the IMAP grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The IMAP grammar rules are well-formed.")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  :file "imap.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-imap-grammar-rules*
  :short "All the IMAP grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are obtained by plugging the core rules into the IMAP rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed.")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  (plug-rules *imap-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-imap-grammar-rules*)

  (defrule rulelist-wfp-of-*all-imap-grammar-rules*
    (rulelist-wfp *all-imap-grammar-rules*))

  (defrule rulelist-closedp-of-*all-imap-grammar-rules*
    (rulelist-closedp *all-imap-grammar-rules*))

  (defrule abnf-core-rules-in-*all-imap-grammar-rules*
    (implies (member-equal core-rule *core-rules*)
             (iff (member-equal core-rule *all-imap-grammar-rules*)
                  (member-equal core-rule (list *rule_ALPHA*
                                                *rule_CR*
                                                *rule_CRLF*
                                                *rule_CTL*
                                                *rule_DIGIT*
                                                *rule_DQUOTE*
                                                *rule_LF*
                                                *rule_SP*))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftreeops *all-imap-grammar-rules* :prefix imap-cst)
