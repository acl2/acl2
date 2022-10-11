; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "core-rules")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax-rules
  :parents (concrete-syntax)
  :short "Rules that specify the concrete syntax of ABNF."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the rules in [RFC:4].")
   (xdoc::p
    "Note that these rules refer to some core rule names,
     so we include the core rules in this file."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection concrete-syntax-rule-names
  :short "Names of the ABNF concrete syntax rules."

  (local (xdoc::set-default-parents concrete-syntax-rule-names))

  (defval *alternation* (rulename "alternation"))
  (defval *bin-val* (rulename "bin-val"))
  (defval *c-nl* (rulename "c-nl"))
  (defval *c-wsp* (rulename "c-wsp"))
  (defval *case-insensitive-string* (rulename "case-insensitive-string"))
  (defval *case-sensitive-string* (rulename "case-sensitive-string"))
  (defval *char-val* (rulename "char-val"))
  (defval *comment* (rulename "comment"))
  (defval *concatenation* (rulename "concatenation"))
  (defval *dec-val* (rulename "dec-val"))
  (defval *defined-as* (rulename "defined-as"))
  (defval *element* (rulename "element"))
  (defval *elements* (rulename "elements"))
  (defval *group* (rulename "group"))
  (defval *hex-val* (rulename "hex-val"))
  (defval *num-val* (rulename "num-val"))
  (defval *option* (rulename "option"))
  (defval *prose-val* (rulename "prose-val"))
  (defval *quoted-string* (rulename "quoted-string"))
  (defval *repeat* (rulename "repeat"))
  (defval *repetition* (rulename "repetition"))
  (defval *rule* (rulename "rule"))
  (defval *rulelist* (rulename "rulelist"))
  (defval *rulename* (rulename "rulename")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection concrete-syntax-rule-definitions
  :short "Definition of the concrete syntax rules."
  :long
  (xdoc::topstring-p
   "These definitions use the "
   (xdoc::seetopic "convenience-constructors" "convenience constructors")
   " for the abstract syntax.")

  (local (xdoc::set-default-parents concrete-syntax-rule-definitions))

  (def-rule-const *rulelist*
    (/_ (1*_ (!_ (/_ *rule*)
                 (/_ (!_ (/_ (*_ *c-wsp*)
                             *c-nl*)))))))

  (def-rule-const *rule*
    (/_ *rulename* *defined-as* *elements* *c-nl*))

  (def-rule-const *rulename*
    (/_ *alpha*
        (*_ (!_ (/_ *alpha*)
                (/_ *digit*)
                (/_ "-")))))

  (def-rule-const *defined-as*
    (/_ (*_ *c-wsp*)
        (!_ (/_ "=")
            (/_ "=/"))
        (*_ *c-wsp*)))

  (def-rule-const *elements*
    (/_ *alternation*
        (*_ *c-wsp*)))

  (def-rule-const *c-wsp*
    (/_ *wsp*)
    (/_ (!_ (/_ *c-nl* *wsp*))))

  (def-rule-const *c-nl*
    (/_ *comment*)
    (/_ *crlf*))

  (def-rule-const *comment*
    (/_ ";"
        (*_ (!_ (/_ *wsp*)
                (/_ *vchar*)))
        *crlf*))

  (def-rule-const *alternation*
    (/_ *concatenation*
        (*_ (!_ (/_ (*_ *c-wsp*)
                    "/"
                    (*_ *c-wsp*)
                    *concatenation*)))))

  (def-rule-const *concatenation*
    (/_ *repetition*
        (*_ (!_ (/_ (1*_ *c-wsp*)
                    *repetition*)))))

  (def-rule-const *repetition*
    (/_ (?_ (/_ *repeat*))
        *element*))

  (def-rule-const *repeat*
    (/_ (1*_ *digit*))
    (/_ (!_ (/_ (*_ *digit*) "*" (*_ *digit*)))))

  (def-rule-const *element*
    (/_ *rulename*)
    (/_ *group*)
    (/_ *option*)
    (/_ *char-val*)
    (/_ *num-val*)
    (/_ *prose-val*))

  (def-rule-const *group*
    (/_ "("
        (*_ *c-wsp*)
        *alternation*
        (*_ *c-wsp*)
        ")"))

  (def-rule-const *option*
    (/_ "["
        (*_ *c-wsp*)
        *alternation*
        (*_ *c-wsp*)
        "]"))

  (def-rule-const *char-val*
    (/_ *case-insensitive-string*)
    (/_ *case-sensitive-string*))

  (def-rule-const *case-insensitive-string*
    (/_ (?_ (/_ "%i"))
        *quoted-string*))

  (def-rule-const *case-sensitive-string*
    (/_ "%s"
        *quoted-string*))

  (def-rule-const *quoted-string*
    (/_ *dquote*
        (*_ (!_ (/_ (%- #x20 #x21))
                (/_ (%- #x23 #x7e))))
        *dquote*))

  (def-rule-const *num-val*
    (/_ "%"
        (!_ (/_ *bin-val*)
            (/_ *dec-val*)
            (/_ *hex-val*))))

  (def-rule-const *bin-val*
    (/_ "b"
        (1*_ *bit*)
        (?_ (/_ (1*_ (!_ (/_ "."
                             (1*_ *bit*)))))
            (/_ (!_ (/_ "-"
                        (1*_ *bit*)))))))

  (def-rule-const *dec-val*
    (/_ "d"
        (1*_ *digit*)
        (?_ (/_ (1*_ (!_ (/_ "."
                             (1*_ *digit*)))))
            (/_ (!_ (/_ "-"
                        (1*_ *digit*)))))))

  (def-rule-const *hex-val*
    (/_ "x"
        (1*_ *hexdig*)
        (?_ (/_ (1*_ (!_ (/_ "."
                             (1*_ *hexdig*)))))
            (/_ (!_ (/_ "-"
                        (1*_ *hexdig*)))))))

  (def-rule-const *prose-val*
    (/_ "<"
        (*_ (!_ (/_ (%- #x20 #x3d))
                (/_ (%- #x3f #x7e))))
        ">")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *concrete-syntax-rules*
  :short "The ABNF concrete syntax rules, excluding the core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ABNF concrete syntax rules are well-formed.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (list *rule_rulelist*
        *rule_rule*
        *rule_rulename*
        *rule_defined-as*
        *rule_elements*
        *rule_c-wsp*
        *rule_c-nl*
        *rule_comment*
        *rule_alternation*
        *rule_concatenation*
        *rule_repetition*
        *rule_repeat*
        *rule_element*
        *rule_group*
        *rule_option*
        *rule_char-val*
        *rule_case-insensitive-string*
        *rule_case-sensitive-string*
        *rule_quoted-string*
        *rule_num-val*
        *rule_bin-val*
        *rule_dec-val*
        *rule_hex-val*
        *rule_prose-val*)
  ///

  (add-const-to-untranslate-preprocess *concrete-syntax-rules*)

  (defruled rulelistp-of-*concrete-syntax-rules*
    (rulelistp *concrete-syntax-rules*)))
