; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "core-rules")

(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (abnf)
  :short "Concrete syntax of ABNF."
  :long
  (xdoc::topstring-p
   "The concrete syntax of ABNF is specified, in [RFC:4],
    using ABNF concrete syntax.
    We break the circularity by formalizing the concrete syntax of ABNF
    using the abstract syntax of ABNF.")
  :order-subtopics t)

(defxdoc+ concrete-syntax-rules
  :parents (concrete-syntax)
  :short "Rules that specify the concrete syntax of ABNF."
  :long
  (xdoc::topstring-p
   "These are the rules in [RFC:4].")
  :order-subtopics t)

(defsection concrete-syntax-rule-names
  :parents (concrete-syntax-rules)
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

(defsection concrete-syntax-rule-definitions
  :parents (concrete-syntax-rules)
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

(defval *concrete-syntax-rules*
  :parents (concrete-syntax-rules)
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
    (rulelistp *concrete-syntax-rules*))

  (defruled rulelist-wfp-of-*concrete-syntax-rules*
    (rulelist-wfp *concrete-syntax-rules*)))

(defval *all-concrete-syntax-rules*
  :parents (concrete-syntax)
  :short "All the ABNF concrete syntax rules,
          including the core rules that they reference."
  :long
  (xdoc::topstring
   (xdoc::p
    "These rules are well-formed, closed,
     and generate terminal strings consisting only of ASCII codes.")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (plug-rules *concrete-syntax-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-concrete-syntax-rules*)

  (defruled rulelist-wfp-of-*all-concrete-syntax-rules*
    (rulelist-wfp *all-concrete-syntax-rules*))

  (defruled rulelist-closedp-of-*all-concrete-syntax-rules*
    (rulelist-closedp *all-concrete-syntax-rules*))

  (defruled ascii-only-*all-concrete-syntax-rules*
    (rulelist-in-termset-p *all-concrete-syntax-rules*
                           (integers-from-to 0 127))))

(define parse-grammar* ((nats nat-listp))
  :returns (result (or (tree-setp result)
                       (equal result :infinite))
                   :hints (("Goal" :use (:instance
                                         return-type-of-parse
                                         (string nats)
                                         (rulename *rulelist*)
                                         (rules *all-concrete-syntax-rules*)))))
  :parents (concrete-syntax)
  :short "Parse a sequence of natural numbers as an ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a declaratively defined, non-executable parser
     for the ABNF language itself
     (@(tsee parse-grammar) is a verified executable parser).
     It turns text (represented as a sequence of natural numbers)
     with ABNF grammar rules (defining the concrete syntax of some language)
     into parse trees;
     the parse trees can be "
    (xdoc::seetopic "concrete-to-abstract-syntax" "abstracted")
    " to lists of rules in the ABNF abstract syntax.")
   (xdoc::p
    "This function may return more than one parse tree,
     because the @('rulelist') rule in [RFC:4] is ambiguous.
     For example, the string
     `@('rulename defined-as alternation c-nl WSP c-nl')'
     can be parsed in two different ways (see the theorem below):")
   (xdoc::ol
    (xdoc::li
     "As a @('rulelist') consisting of
      just a @('rule')
      whose @('elements') has `@('c-nl WSP')' as @('*c-wsp').")
    (xdoc::li
     "As a @('rulelist') consisting of
      a @('rule')
      whose @('elements') has `' (i.e. the empty string)
      as @('*c-wsp'),
      followed by a @('(*c-wsp c-nl)') with @('WSP') as @('*c-wsp')."))
   (xdoc::p
    "This ambiguity only concerns blank space and comments,
     so it does not affect the abstract syntax and the semantics.")
   (xdoc::p
    "It remains to be proved that this function
     always returns a finite set of trees, never @(':infinite')."))
  (parse nats *rulelist* *all-concrete-syntax-rules*)
  :no-function t
  ///

  (defruled rulelist-ambiguous-example
    (b* ((string (list *rulename*
                       *defined-as*
                       *alternation*
                       *c-nl*
                       *wsp*
                       *c-nl*))
         (tree-rulename (tree-leafrule *rulename*))
         (tree-defined-as (tree-leafrule *defined-as*))
         (tree-alternation (tree-leafrule *alternation*))
         (tree-c-nl (tree-leafrule *c-nl*))
         (tree-wsp (tree-leafrule *wsp*))
         (tree-c-nl-wsp (tree-nonleaf nil
                                      (list (list tree-c-nl)
                                            (list tree-wsp))))
         (tree-c-wsp-1 (tree-nonleaf *c-wsp*
                                     (list (list tree-c-nl-wsp))))
         (tree-c-wsp-2 (tree-nonleaf *c-wsp*
                                     (list (list tree-wsp))))
         (tree-elements-1 (tree-nonleaf *elements*
                                        (list (list tree-alternation)
                                              (list tree-c-wsp-1))))
         (tree-elements-2 (tree-nonleaf *elements*
                                        (list (list tree-alternation)
                                              nil)))
         (tree-rule-1 (tree-nonleaf *rule*
                                    (list (list tree-rulename)
                                          (list tree-defined-as)
                                          (list tree-elements-1)
                                          (list tree-c-nl))))
         (tree-rule-/-*cwsp-cnl-1 (tree-nonleaf nil
                                                (list (list tree-rule-1))))
         (tree-rulelist-1 (tree-nonleaf *rulelist*
                                        (list (list tree-rule-/-*cwsp-cnl-1))))
         (tree-rule-2 (tree-nonleaf *rule*
                                    (list (list tree-rulename)
                                          (list tree-defined-as)
                                          (list tree-elements-2)
                                          (list tree-c-nl))))
         (tree-rule-/-*cwsp-cnl-2 (tree-nonleaf nil
                                                (list (list tree-rule-2))))
         (tree-*cwsp-cnl (tree-nonleaf nil
                                       (list (list tree-c-wsp-2)
                                             (list tree-c-nl))))
         (tree-rule-/-*cwsp-cnl-3 (tree-nonleaf nil
                                                (list (list tree-*cwsp-cnl))))
         (tree-rulelist-2 (tree-nonleaf *rulelist*
                                        (list (list tree-rule-/-*cwsp-cnl-2
                                                    tree-rule-/-*cwsp-cnl-3)))))
      (and (stringp string)
           (treep tree-rulelist-1)
           (treep tree-rulelist-2)
           (tree-match-element-p tree-rulelist-1
                                 (element-rulename *rulelist*)
                                 *all-concrete-syntax-rules*)
           (tree-match-element-p tree-rulelist-2
                                 (element-rulename *rulelist*)
                                 *all-concrete-syntax-rules*)
           (not (equal tree-rulelist-1 tree-rulelist-2))
           (equal (tree->string tree-rulelist-1) string)
           (equal (tree->string tree-rulelist-2) string)))))
