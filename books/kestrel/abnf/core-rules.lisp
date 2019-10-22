; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "operations")

(include-book "kestrel/utilities/untranslate-preprocessing" :dir :system)

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ core-rules
  :parents (abnf)
  :short "Core rules of ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules are specified in [RFC:B].
     They are a set of rules commonly used
     as part of the definition of the concrete syntax of languages in ABNF.
     In particular, they are used
     as part of the definition of the concrete syntax of ABNF itself
     in [RFC:4].")
   (xdoc::p
    "Since the concrete syntax of ABNF is specified, in [RFC:4],
     using ABNF concrete syntax,
     and since that definition of the concrete syntax of ABNF
     uses the core rules,
     we break the circularity by formalizing the core rules
     using the abstract syntax of ABNF."))
  :order-subtopics t)

(defsection core-rule-names
  :parents (core-rules)
  :short "Names of the core rules."
  :long
  (xdoc::topstring-p
   "The names are lowercase,
    according to the normalized representation
    required by @(tsee rulename-wfp).")

  (local (xdoc::set-default-parents core-rule-names))

  (defval *alpha* (rulename "alpha"))
  (defval *bit* (rulename "bit"))
  (defval *char* (rulename "char"))
  (defval *cr* (rulename "cr"))
  (defval *crlf* (rulename "crlf"))
  (defval *ctl* (rulename "ctl"))
  (defval *digit* (rulename "digit"))
  (defval *dquote* (rulename "dquote"))
  (defval *hexdig* (rulename "hexdig"))
  (defval *htab* (rulename "htab"))
  (defval *lf* (rulename "lf"))
  (defval *lwsp* (rulename "lwsp"))
  (defval *octet* (rulename "octet"))
  (defval *sp* (rulename "sp"))
  (defval *vchar* (rulename "vchar"))
  (defval *wsp* (rulename "wsp")))

(defsection core-rule-definitions
  :parents (core-rules)
  :short "Definition of the core rules."
  :long
  (xdoc::topstring-p
   "These definitions use the "
   (xdoc::seetopic "convenience-constructors" "convenience constructors")
   " for the abstract syntax.")

  (local (xdoc::set-default-parents core-rule-definitions))

  (def-rule-const *alpha*
    (/_ (%- #x41 #x5a))
    (/_ (%- #x61 #x7a)))

  (def-rule-const *bit*
    (/_ "0")
    (/_ "1"))

  (def-rule-const *char*
    (/_ (%- #x01 #x7f)))

  (def-rule-const *cr*
    (/_ (%. #x0d)))

  (def-rule-const *crlf*
    (/_ *cr* *lf*))

  (def-rule-const *ctl*
    (/_ (%- #x00 #x1f))
    (/_ (%. #x7f)))

  (def-rule-const *digit*
    (/_ (%- #x30 #x39)))

  (def-rule-const *dquote*
    (/_ (%. #x22)))

  (def-rule-const *hexdig*
    (/_ *digit*)
    (/_ "A")
    (/_ "B")
    (/_ "C")
    (/_ "D")
    (/_ "E")
    (/_ "F"))

  (def-rule-const *htab*
    (/_ (%. #x09)))

  (def-rule-const *lf*
    (/_ (%. #x0a)))

  (def-rule-const *lwsp*
    (/_ (*_ (!_ (/_ *wsp*)
                (/_ *crlf* *wsp*)))))

  (def-rule-const *octet*
    (/_ (%- #x00 #xff)))

  (def-rule-const *sp*
    (/_ (%. #x20)))

  (def-rule-const *vchar*
    (/_ (%- #x21 #x7e)))

  (def-rule-const *wsp*
    (/_ *sp*)
    (/_ *htab*)))

(defval *core-rules*
  :parents (core-rules)
  :short "All the core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The core rules are well-formed and closed.")
   (xdoc::p
    "They generate only strings of octets.
     Without the @('OCTET') rule,
     they generate only strings of ASCII codes.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (list *rule_alpha*
        *rule_bit*
        *rule_char*
        *rule_cr*
        *rule_crlf*
        *rule_ctl*
        *rule_digit*
        *rule_dquote*
        *rule_hexdig*
        *rule_htab*
        *rule_lf*
        *rule_lwsp*
        *rule_octet*
        *rule_sp*
        *rule_vchar*
        *rule_wsp*)
  ///

  (add-const-to-untranslate-preprocess *core-rules*)

  (defruled rulelistp-of-*core-rules*
    (rulelistp *core-rules*))

  (defruled rulelist-wfp-of-*core-rules*
    (rulelist-wfp *core-rules*))

  (defruled rulelist-closedp-of-*core-rules*
    (rulelist-closedp *core-rules*))

  (defruled octet-only-*core-rules*
    (rulelist-in-termset-p *core-rules* (integers-from-to 0 255)))

  (defruled ascii-only-*core-rules*-without-*octet*
    (rulelist-in-termset-p (remove-equal *rule_octet* *core-rules*)
                           (integers-from-to 0 127))))
