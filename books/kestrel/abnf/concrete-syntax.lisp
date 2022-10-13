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
(include-book "concrete-syntax-rules")
(include-book "semantics")

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
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-concrete-syntax-rules*
  :parents (concrete-syntax)
  :short "All the ABNF concrete syntax rules,
          including the core rules that they reference
          (directly and indirectly)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Properties of these rules
     are proved in @(see concrete-syntax-validation).")
   (xdoc::p
    "We use @(tsee add-const-to-untranslate-preprocess)
     to keep this constant unexpanded in output."))
  (append *concrete-syntax-rules*
          (list *rule_alpha*
                *rule_bit*
                *rule_cr*
                *rule_crlf*
                *rule_digit*
                *rule_dquote*
                *rule_hexdig*
                *rule_htab*
                *rule_lf*
                *rule_sp*
                *rule_vchar*
                *rule_wsp*))
  ///

  (add-const-to-untranslate-preprocess *all-concrete-syntax-rules*)

  (defruled rulelistp-of-*all-concrete-syntax-rules*
    (rulelistp *all-concrete-syntax-rules*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
