; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "well-formedness")
(include-book "closure")

(include-book "../semantics")

(include-book "kestrel/std/strings/letter-chars" :dir :system)
(include-book "kestrel/std/strings/letter-digit-dash-chars" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/osets" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)
(include-book "kestrel/fty/string-list-result" :dir :system)

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (abnf)
  :short "Operations on ABNF grammars."
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ in-terminal-set
  :parents (operations)
  :short "ABNF grammars that generate only terminals in given sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "If all the terminal value notations used in a rule list denote values
     that belong to a certain set of terminals (natural numbers),
     then the terminal strings of that rule list
     consist of only terminals that belong to that set.
     This is proved below.")
   (xdoc::p
    "For example, if all the terminal value notations are octets,
     the terminal strings consist of octets
     and can be parsed starting from character strings
     (since @(see acl2::characters) are isomorphic to octets)
     instead of natural numbers."))
  :order-subtopics t)

(define num-val-in-termset-p ((num-val num-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if a numeric value notation denotes values in a set."
  (num-val-case num-val
                :direct (list-in num-val.get termset)
                :range (list-in (integers-from-to num-val.min num-val.max)
                                termset))
  :no-function t)

(define char-sensitive-in-termset-p ((char characterp) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if the code of a character is in a set."
  (in (char-code char) termset)
  :no-function t)

(define char-insensitive-in-termset-p ((char characterp) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if the code of a character,
          as well as the codes of its uppercase or lowercase counterparts,
          are in a set."
  (and (in (char-code char) termset)
       (in (char-code (upcase-char char)) termset)
       (in (char-code (downcase-char char)) termset))
  :no-function t)

(std::deflist chars-sensitive-in-termset-p (x termset)
  :guard (and (character-listp x) (nat-setp termset))
  :parents (in-terminal-set)
  :short "Lift @(tsee char-sensitive-in-termset-p) to lists."
  (char-sensitive-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown)

(std::deflist chars-insensitive-in-termset-p (x termset)
  :guard (and (character-listp x)
              (nat-setp termset))
  :parents (in-terminal-set)
  :short "Lift @(tsee char-insensitive-in-termset-p) to lists."
  (char-insensitive-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown)

(define char-val-in-termset-p ((char-val char-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if a character value notation denotes values in a set."
  (char-val-case char-val
                 :sensitive (chars-sensitive-in-termset-p
                             (explode char-val.get) termset)
                 :insensitive (chars-insensitive-in-termset-p
                               (explode char-val.get) termset))
  :no-function t)

(define prose-val-in-termset-p ((prose-val prose-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "A prose value notation is unconstrained,
          so it cannot be guaranteed to denote values in a set."
  nil
  :ignore-ok t
  :no-function t)

(defines alt/conc/rep/elem-in-termset-p

  (define alternation-in-termset-p ((alternation alternationp)
                                    (termset nat-setp))
    :returns (yes/no booleanp)
    :parents (in-terminal-set)
    :short "Check if all the terminal value notations in an alternation
            denote values in a set."
    :long (xdoc::topstring-@def "alternation-in-termset-p")
    (or (endp alternation)
        (and (concatenation-in-termset-p (car alternation) termset)
             (alternation-in-termset-p (cdr alternation) termset)))
    :measure (two-nats-measure (alternation-count alternation) 0)
    :no-function t)

  (define concatenation-in-termset-p ((concatenation concatenationp)
                                      (termset nat-setp))
    :returns (yes/no booleanp)
    :parents (in-terminal-set)
    :short "Check if all the terminal value notations in a concatenation
            denote values in a set."
    :long (xdoc::topstring-@def "concatenation-in-termset-p")
    (or (endp concatenation)
        (and (repetition-in-termset-p (car concatenation) termset)
             (concatenation-in-termset-p (cdr concatenation) termset)))
    :measure (two-nats-measure (concatenation-count concatenation) 0)
    :no-function t)

  (define repetition-in-termset-p ((repetition repetitionp)
                                   (termset nat-setp))
    :returns (yes/no booleanp)
    :parents (in-terminal-set)
    :short "Check if all the terminal value notations in a repetition
            denote values in a set,
            or the repetition consists of zero instances."
    :long (xdoc::topstring-@def "repetition-in-termset-p")
    (or (element-in-termset-p (repetition->element repetition) termset)
        (equal (repetition->range repetition)
               (repeat-range 0 (nati-finite 0))))
    :measure (two-nats-measure (repetition-count repetition) 1)
    :no-function t)

  (define element-in-termset-p ((element elementp)
                                (termset nat-setp))
    :returns (yes/no booleanp)
    :parents (in-terminal-set)
    :short "Check if all the terminal value notations in an element
            denote values in a set."
    :long (xdoc::topstring-@def "element-in-termset-p")
    (element-case element
                  :rulename t
                  :group (alternation-in-termset-p element.get termset)
                  :option (alternation-in-termset-p element.get termset)
                  :char-val (char-val-in-termset-p element.get termset)
                  :num-val (num-val-in-termset-p element.get termset)
                  :prose-val (prose-val-in-termset-p element.get termset))
    :measure (two-nats-measure (element-count element) 1)
    :no-function t)

  ///

  (std::deflist alternation-in-termset-p (x termset)
    (concatenation-in-termset-p x termset)
    :guard (and (alternationp x) (nat-setp termset))
    :elementp-of-nil t)

  (std::deflist concatenation-in-termset-p (x termset)
    (repetition-in-termset-p x termset)
    :guard (and (concatenationp x) (nat-setp termset))
    :elementp-of-nil t))

(define rule-in-termset-p ((rule rulep) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if all the terminal value notations in a rule
          denote values in a set."
  (alternation-in-termset-p (rule->definiens rule) termset)
  :no-function t)

(std::deflist rulelist-in-termset-p (x termset)
  :guard (and (rulelistp x)
              (nat-setp termset))
  :parents (in-terminal-set)
  :short "Check if all the terminal value notations in a list of rules
          denote values in a set."
  (rule-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown
  ///

  (defrule alternation-in-termset-p-of-lookup-rulename
    (implies (rulelist-in-termset-p rules termset)
             (alternation-in-termset-p (lookup-rulename rulename rules)
                                       termset))
    :enable (lookup-rulename rule-in-termset-p)))

(define symbol-in-termset-p ((symbol symbolp) (termset nat-setp))
  :returns (yes/no booleanp)
  :parents (in-terminal-set)
  :short "Check if a symbol is either a rule name or a natural number in a set."
  :long
  (xdoc::topstring-p
   "To prove that the terminal strings generated by a rule list
    consist of only terminals in a set,
    it is convenient to work with trees
    whose rule names may not all be expanded,
    to avoid dealing with this additional constraint.
    For these trees,
    we need to weaken the notion that @(tsee tree->string)
    only consists of terminals in the set,
    by allowing non-terminal symbols as well.")
  (symbol-case symbol
               :terminal (in symbol.get termset)
               :nonterminal t)
  :no-function t
  ///

  (defrule symbol-in-termset-p-when-natp
    (implies (natp nat)
             (equal (symbol-in-termset-p nat termset)
                    (in nat termset)))
    :enable (symbol-terminal->get symbol-kind))

  (defrule symbol-in-termset-p-when-rulenamep
    (implies (rulenamep rulename)
             (symbol-in-termset-p rulename termset))
    :enable (symbol-terminal->get symbol-kind)))

(std::deflist string-in-termset-p (x termset)
  :guard (and (stringp x)
              (nat-setp termset))
  :parents (in-terminal-set)
  :short "Check if a string consists of terminals in a set and rule names."
  (symbol-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown
  ///

  (defrule string-in-termset-p-when-nat-listp
    (implies (nat-listp nats)
             (equal (string-in-termset-p nats termset)
                    (list-in nats termset)))))

(defrule leaves-in-termset-when-match-num-val-in-termset
  :parents (in-terminal-set)
  :short "Numeric value notations that denote values in a set
          can be matched only by trees whose terminal leaves are in the set."
  (implies (and (tree-match-num-val-p tree num-val)
                (num-val-in-termset-p num-val termset))
           (string-in-termset-p (tree->string tree) termset))
  :enable (tree-match-num-val-p
           num-val-in-termset-p
           tree->string
           acl2::equal-len-const
           list-in))

(defruled nat-in-termset-when-match-sensitive-char-in-termset
  :parents (in-terminal-set)
  :short "Lemma to prove
          @(tsee nats-in-termset-when-match-sensitive-chars-in-termset)."
  :long
  (xdoc::topstring-p
   "This is disabled by default because its conclusion is fairly general,
    not specific to terminal sets.")
  (implies (and (natp nat)
                (nat-match-sensitive-char-p nat char)
                (char-sensitive-in-termset-p char termset))
           (in nat termset))
  :enable (nat-match-sensitive-char-p
           char-sensitive-in-termset-p))

(defruled nats-in-termset-when-match-sensitive-chars-in-termset
  :parents (in-terminal-set)
  :short "Lemma to prove
          @(tsee leaves-in-termset-when-match-char-val-in-termset)."
  :long
  (xdoc::topstring-p
   "This is disabled by default because its conclusion is fairly general,
    not specific to terminal sets.")
  (implies (and (nat-listp nats)
                (nats-match-sensitive-chars-p nats chars)
                (chars-sensitive-in-termset-p chars termset))
           (list-in nats termset))
  :enable (nats-match-sensitive-chars-p
           chars-sensitive-in-termset-p
           nat-in-termset-when-match-sensitive-char-in-termset))

(defruled nat-in-termset-when-match-insensitive-char-in-termset
  :parents (in-terminal-set)
  :short "Lemma to prove
          @(tsee nats-in-termset-when-match-insensitive-chars-in-termset)."
  :long
  (xdoc::topstring-p
   "This is disabled by default because its conclusion is fairly general,
    not specific to terminal sets.")
  (implies (and (natp nat)
                (nat-match-insensitive-char-p nat char)
                (char-insensitive-in-termset-p char termset))
           (in nat termset))
  :enable (nat-match-insensitive-char-p
           char-insensitive-in-termset-p))

(defruled nats-in-termset-when-match-insensitive-chars-in-termset
  :parents (in-terminal-set)
  :short "Lemma to prove
          @(tsee leaves-in-termset-when-match-char-val-in-termset)."
  :long
  (xdoc::topstring-p
   "This is disabled by default because its conclusion is fairly general,
    not specific to terminal sets.")
  (implies (and (nat-listp nats)
                (nats-match-insensitive-chars-p nats chars)
                (chars-insensitive-in-termset-p chars termset))
           (list-in nats termset))
  :enable (nats-match-insensitive-chars-p
           chars-insensitive-in-termset-p
           nat-in-termset-when-match-insensitive-char-in-termset))

(defrule leaves-in-termset-when-match-char-val-in-termset
  :parents (in-terminal-set)
  :short "Character value notations that denote terminals in a set
          can be matched only by trees whose terminal leaves are in the set."
  (implies (and (tree-match-char-val-p tree char-val)
                (char-val-in-termset-p char-val termset))
           (string-in-termset-p (tree->string tree) termset))
  :enable (tree-match-char-val-p
           char-val-in-termset-p
           tree->string
           nats-in-termset-when-match-sensitive-chars-in-termset
           nats-in-termset-when-match-insensitive-chars-in-termset))

(defsection leaves-in-termset-when-match-alt/conc/rep/elem-in-termset
  :parents (in-terminal-set)
  :short "Alternations, concatenation, repetitions, and elements
          whose terminal value notations all denote values in a set,
          can be matched only by (lists of (lists of)) trees
          whose terminal leaves are in the set."
  :long
  (xdoc::topstring-p
   "The proof uses
    @(tsee leaves-in-termset-when-match-num-val-in-termset) and
    @(tsee leaves-in-termset-when-match-char-val-in-termset).")

  (defthm-tree-match-alt/conc/rep/elem-p-flag

    (defthm leaves-in-termset-when-match-alternation-in-termset
      (implies (and (tree-list-list-match-alternation-p treess
                                                        alternation
                                                        rules)
                    (alternation-in-termset-p alternation termset)
                    (rulelist-in-termset-p rules termset))
               (string-in-termset-p (tree-list-list->string treess) termset))
      :flag tree-list-list-match-alternation-p)

    (defthm leaves-in-termset-when-match-concatenation-in-termset
      (implies (and (tree-list-list-match-concatenation-p treess
                                                          concatenation
                                                          rules)
                    (concatenation-in-termset-p concatenation termset)
                    (rulelist-in-termset-p rules termset))
               (string-in-termset-p (tree-list-list->string treess) termset))
      :flag tree-list-list-match-concatenation-p)

    (defthm leaves-in-termset-when-match-repetition-in-termset
      (implies (and (tree-list-match-repetition-p trees repetition rules)
                    (repetition-in-termset-p repetition termset)
                    (rulelist-in-termset-p rules termset))
               (string-in-termset-p (tree-list->string trees) termset))
      :flag tree-list-match-repetition-p)

    (defthm leaves-in-termset-when-list-match-element-in-termset
      (implies (and (tree-list-match-element-p trees element rules)
                    (element-in-termset-p element termset)
                    (rulelist-in-termset-p rules termset))
               (string-in-termset-p (tree-list->string trees) termset))
      :flag tree-list-match-element-p)

    (defthm leaves-in-termset-when-match-element-in-termset
      (implies (and (tree-match-element-p tree element rules)
                    (element-in-termset-p element termset)
                    (rulelist-in-termset-p rules termset))
               (string-in-termset-p (tree->string tree) termset))
      :flag tree-match-element-p)

    :hints (("Goal"
             :in-theory
             (enable tree-list-list-match-alternation-p
                     tree-list-list-match-concatenation-p
                     tree-list-match-repetition-p
                     tree-list-match-element-p
                     tree-match-element-p
                     alternation-in-termset-p
                     concatenation-in-termset-p
                     repetition-in-termset-p
                     element-in-termset-p
                     tree->string
                     tree-list->string
                     tree-list-list->string
                     leaves-in-termset-when-match-num-val-in-termset
                     leaves-in-termset-when-match-char-val-in-termset)))))

(defruled terminal-strings-in-termset-when-rules-in-termset
  :parents (in-terminal-set)
  :short "Rules whose terminal value notations all denote values in a set,
          generate terminal strings consisting of terminals in the set."
  :long
  (xdoc::topstring-p
   "This is disabled by default because its conclusion is fairly general,
    not specific to terminal sets.")
  (implies (and (terminal-string-for-rules-p nats rules)
                (rulelist-in-termset-p rules termset))
           (list-in nats termset))
  :enable (terminal-string-for-rules-p
           string-parsablep
           parse-treep
           element-in-termset-p)
  :use (:instance leaves-in-termset-when-match-element-in-termset
        (tree (string-parsablep-witness
               nats
               (terminal-string-for-rules-p-witness nats rules)
               rules))
        (element (element-rulename
                  (terminal-string-for-rules-p-witness nats rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ambiguity
  :parents (operations)
  :short "Ambiguity (and unambiguity) in ABNF grammars."
  :long
  (xdoc::topstring-p
   "This part of the ABNF formalization is work in progress.
    More definitions and theorems should be added.")
  :order-subtopics t)

(define-sk rules-ambiguousp ((rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of ambiguous lists of rules."
  :long
  (xdoc::topstring-p
   "A list of rules is ambiguous iff it includes some ambiguous string.
    Note that the condition that
    the existentially quantified @('rulename') be defined by @('rules')
    would be superfluous,
    because if @('rulename') is not defined
    then no parse trees can originate from it.")
  (exists (string rulename)
          (and (stringp string)
               (rulenamep rulename)
               (string-ambiguousp string rulename rules))))

(defrule num-val-unambiguous
  :parents (ambiguity)
  :short "Numeric value notations are never ambiguous."
  :long
  (xdoc::topstring-p
   "Any two trees that match a numeric value notation
    and that have the same string at the leaves
    are the same tree.")
  (implies (and (tree-match-num-val-p tree1 num-val)
                (tree-match-num-val-p tree2 num-val))
           (equal (equal (tree->string tree1)
                         (tree->string tree2))
                  (tree-equiv tree1 tree2)))
  :enable (tree-match-num-val-p tree->string tree-fix tree-leafterm->get))

(defrule char-val-unambiguous
  :parents (ambiguity)
  :short "Character value notations are never ambiguous."
  :long
  (xdoc::topstring-p
   "Any two trees that match a character value notation
    and that have the same string at the leaves
    are the same tree.")
  (implies (and (tree-match-char-val-p tree1 char-val)
                (tree-match-char-val-p tree2 char-val))
           (equal (equal (tree->string tree1)
                         (tree->string tree2))
                  (tree-equiv tree1 tree2)))
  :enable (tree-match-char-val-p tree->string tree-fix tree-leafterm->get))

(defruled prose-val-ambiguous
  :parents (ambiguity)
  :short "Prose value notations are always ambiguous."
  :long
  (xdoc::topstring-p
   "We can always construct two different trees
    with the same string at the leaves
    that match any prose value notation.
    Recall that a prose value notation is matched by any tree.")
  (implies (and (equal tree1 (make-tree-nonleaf
                              :rulename? nil
                              :branches (list (list (tree-leafterm '(1))
                                                    (tree-leafterm '(2))))))
                (equal tree2 (make-tree-nonleaf
                              :rulename? nil
                              :branches (list (list (tree-leafterm '(1 2)))))))
           (and (treep tree1)
                (treep tree2)
                (not (equal tree1 tree2))
                (equal (tree->string tree1)
                       (tree->string tree2))
                (tree-match-prose-val-p tree1 prose-val)
                (tree-match-prose-val-p tree2 prose-val))))

(define-sk element-unambiguousp ((element elementp) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of unambiguous elements."
  :long
  (xdoc::topstring-p
   "An element is unambiguous iff
    any two trees that match the element and have the same string at the leaves
    are the same tree.")
  (forall (tree1 tree2)
          (implies (and (treep tree1)
                        (treep tree2)
                        (tree-match-element-p tree1 element rules)
                        (tree-match-element-p tree2 element rules))
                   (equal (equal (tree->string tree1)
                                 (tree->string tree2))
                          (equal tree1 tree2))))
  ///

  (defruled element-ambiguousp-rewrite
    (implies (and (element-unambiguousp element rules)
                  (tree-match-element-p tree1 element rules)
                  (tree-match-element-p tree2 element rules))
             (equal (equal (tree->string tree1)
                           (tree->string tree2))
                    (tree-equiv tree1 tree2)))
    :use (:instance element-unambiguousp-necc
                    (tree1 (tree-fix tree1))
                    (tree2 (tree-fix tree2)))))

(defrule element-num-val-unambiguous
  :parents (ambiguity)
  :short "Numeric value elements are never ambiguous."
  :long
  (xdoc::topstring-p
   "This is a simple consequnce of @(tsee num-val-unambiguous).")
  (implies (element-case element :num-val)
           (element-unambiguousp element rules))
  :enable (element-unambiguousp tree-match-element-p))

(defrule element-char-val-unambiguous
  :parents (ambiguity)
  :short "Character value elements are never ambiguous."
  :long
  (xdoc::topstring
   "This is a simple consequnce of @(tsee char-val-unambiguous).")
  (implies (element-case element :char-val)
           (element-unambiguousp element rules))
  :enable (element-unambiguousp tree-match-element-p))

(defrule element-prose-val-ambiguous
  :parents (ambiguity)
  :short "Prose value elements are always ambiguous."
  :long
  (xdoc::topstring-p
   "This is a simple consequence of @(tsee prose-val-ambiguous).")
  (implies (element-case element :prose-val)
           (not (element-unambiguousp element rules)))
  :enable tree-match-element-p
  :use (:instance element-unambiguousp-necc
                  (tree1 (make-tree-nonleaf
                          :rulename? nil
                          :branches (list (list (tree-leafterm '(1))
                                                (tree-leafterm '(2))))))
                  (tree2 (make-tree-nonleaf
                          :rulename? nil
                          :branches (list (list (tree-leafterm '(1 2))))))))

(define-sk repetition-unambiguousp ((repetition repetitionp) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of unambiguous repetitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A repetition is unambiguous iff
     any two lists of trees that match the repetition
     and have the same string at the leaves
     are the same list of trees.")
   (xdoc::p
    "A repetition of 0 elements is always unambiguous."))
  (forall (trees1 trees2)
          (implies (and (tree-listp trees1)
                        (tree-listp trees2)
                        (tree-list-match-repetition-p trees1 repetition rules)
                        (tree-list-match-repetition-p trees2 repetition rules))
                   (equal (equal (tree-list->string trees1)
                                 (tree-list->string trees2))
                          (equal trees1 trees2))))
  ///

  (defruled repetition-unambiguousp-rewrite
    (implies (and (repetition-unambiguousp repetition rules)
                  (tree-list-match-repetition-p trees1 repetition rules)
                  (tree-list-match-repetition-p trees2 repetition rules))
             (equal (equal (tree-list->string trees1)
                           (tree-list->string trees2))
                    (tree-list-equiv trees1 trees2)))
    :use (:instance repetition-unambiguousp-necc
                    (trees1 (tree-list-fix trees1))
                    (trees2 (tree-list-fix trees2))))

  (defrule empty-repetition-umabiguous
    (implies (equal (repetition->range repetition)
                    (repeat-range 0 (nati-finite 0)))
             (repetition-unambiguousp repetition rules))
    :enable tree-list-match-repetition-p))

(define-sk concatenation-unambiguousp ((concatenation concatenationp)
                                       (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of unambiguous concatenations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A concatenation is unambiguous iff
     any two lists of lists of trees that match the concatenation
     and have the same string at the leaves
     are the same list of lists of trees.")
   (xdoc::p
    "An empty concatenation is always unambiguous."))
  (forall (treess1 treess2)
          (implies (and (tree-list-listp treess1)
                        (tree-list-listp treess2)
                        (tree-list-list-match-concatenation-p
                         treess1 concatenation rules)
                        (tree-list-list-match-concatenation-p
                         treess2 concatenation rules))
                   (equal (equal (tree-list-list->string treess1)
                                 (tree-list-list->string treess2))
                          (equal treess1 treess2))))
  ///

  (defruled concatenation-unambiguousp-rewrite
    (implies (and (concatenation-unambiguousp concatenation rules)
                  (tree-list-list-match-concatenation-p treess1
                                                        concatenation
                                                        rules)
                  (tree-list-list-match-concatenation-p treess2
                                                        concatenation
                                                        rules))
             (equal (equal (tree-list-list->string treess1)
                           (tree-list-list->string treess2))
                    (tree-list-list-equiv treess1 treess2)))
    :use (:instance concatenation-unambiguousp-necc
                    (treess1 (tree-list-list-fix treess1))
                    (treess2 (tree-list-list-fix treess2))))

  (defrule empty-concatenation-unambiguous
    (concatenation-unambiguousp nil rules)
    :enable tree-list-list-match-concatenation-p))

(define-sk alternation-unambiguousp ((alternation alternationp)
                                     (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of unambiguous alternations."
  :long
  (xdoc::topstring
   (xdoc::p
    "An alternation is unambiguous iff
     any two lists of lists of trees that match the alternation
     and have the same string at the leaves
     are the same list of lists of trees.")
   (xdoc::p
    "An empty alternation is always unambiguous."))
  (forall (treess1 treess2)
          (implies (and (tree-list-listp treess1)
                        (tree-list-listp treess2)
                        (tree-list-list-match-alternation-p
                         treess1 alternation rules)
                        (tree-list-list-match-alternation-p
                         treess2 alternation rules))
                   (equal (equal (tree-list-list->string treess1)
                                 (tree-list-list->string treess2))
                          (equal treess1 treess2))))
  ///

  (defruled alternation-unambiguousp-rewrite
    (implies (and (alternation-unambiguousp alternation rules)
                  (tree-list-list-match-alternation-p treess1
                                                      alternation
                                                      rules)
                  (tree-list-list-match-alternation-p treess2
                                                      alternation
                                                      rules))
             (equal (equal (tree-list-list->string treess1)
                           (tree-list-list->string treess2))
                    (tree-list-list-equiv treess1 treess2)))
    :use (:instance alternation-unambiguousp-necc
                    (treess1 (tree-list-list-fix treess1))
                    (treess2 (tree-list-list-fix treess2))))

  (defrule alternation-unambiguousp-of-nil
    (alternation-unambiguousp nil rules)
    :enable tree-list-list-match-alternation-p))

(define-sk concatenation-alternation-disjointp ((concatenation concatenationp)
                                                (alternation alternationp)
                                                (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (ambiguity)
  :short "Notion of disjoint concatenation-alternation pairs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A concatenation is disjoint from an alternation iff
     the concatenation and the alternation are matched
     by disjoint sets of lists of lists of trees.
     That is, there is no list of lists of trees that matches
     both the concatenation and the alternation.")
   (xdoc::p
    "The empty alternation is disjoint from the empty concatenation."))
  (forall (treess1 treess2)
          (implies (and (tree-list-listp treess1)
                        (tree-list-listp treess2)
                        (tree-list-list-match-concatenation-p
                         treess1 concatenation rules)
                        (tree-list-list-match-alternation-p
                         treess2 alternation rules))
                   (not (equal (tree-list-list->string treess1)
                               (tree-list-list->string treess2)))))
  :rewrite (implies (and (concatenation-alternation-disjointp
                          concatenation alternation rules)
                         (tree-list-listp treess1)
                         (tree-list-listp treess2)
                         (tree-list-list-match-concatenation-p
                          treess1 concatenation rules)
                         (tree-list-list-match-alternation-p
                          treess2 alternation rules))
                    (and (not (equal (tree-list-list->string treess1)
                                     (tree-list-list->string treess2)))
                         (not (equal (tree-list-list->string treess2)
                                     (tree-list-list->string treess1)))))
  ///

  (defrule concatenation-alternation-disjointp-of-nil
    (concatenation-alternation-disjointp concatenation nil rules)
    :enable tree-list-list-match-alternation-p))

(defrule alternation-unambiguousp-of-cons-when-disjointp
  :parents (ambiguity)
  :short "If an umambiguous concatenation
          is disjoint from an unambiguous alternation,
          then adding the concatenation maintains the alternation unambiguous."
  :long
  (xdoc::topstring
   (xdoc::p
    "This theorem can be used to show that an alternation is unambiguous,
     one constituting concatenation at a time,
     starting with "
    (xdoc::seetopic "concatenation-alternation-disjointp"
                    "@('concatenation-alternation-disjointp-of-nil')")
    ". In other words, it must be showed that the alternatives of the alternation
     are all disjoint, i.e. they have no lists of lists of trees in common."))
  (implies (and (concatenation-unambiguousp concatenation rules)
                (alternation-unambiguousp alternation rules)
                (concatenation-alternation-disjointp
                 concatenation alternation rules))
           (alternation-unambiguousp (cons concatenation alternation) rules))
  :expand ((alternation-unambiguousp (cons concatenation alternation) rules))
  :enable (tree-list-list-match-alternation-p
           concatenation-unambiguousp-necc
           alternation-unambiguousp-necc
           concatenation-alternation-disjointp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ plugging
  :parents (operations)
  :short "Composition of ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certain ABNF grammars are defined modularly.
     A ``module'' may not be "
    (xdoc::seetopic "closure" "closed")
    ", but when it is combined with other modules,
     the resulting grammar may be closed.")
   (xdoc::p
    "For example, the "
    (xdoc::seetopic "concrete-syntax-rules" "concrete syntax rules")
    " are not closed.
     But when they are combined with the "
    (xdoc::seetopic "core-rules" "core rules")
    ", the "
    (xdoc::seetopic "*all-concrete-syntax-rules*" "resulting rule list")
    " is closed.")
   (xdoc::p
    "As another example,
     the HTTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "RFC 7230")
    " includes rules defined by prose value notations
     that refer to the URI grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
    ". The intended way to compose the two grammars is
     to replace the prose HTTP rules with the corresponding URI rules.")
   (xdoc::p
    "Here we define an operation to accomplish the kind of composition
    exemplified above.
    The operation ``plugs'' a rule list into another rule list,
    e.g. it plugs the core rules into the concrete syntax rules,
    and it plugs the URI rules into the HTTP rules."))
  :order-subtopics t)

(define rule-prosep ((rule rulep))
  :returns (yes/no booleanp)
  :parents (plugging)
  :short "Check if a rule has a single prose value notation as definiens."
  (b* ((alternation (rule->definiens rule)))
    (and (consp alternation)
         (not (consp (cdr alternation)))
         (b* ((concatenation (car alternation)))
           (and (consp concatenation)
                (not (consp (cdr concatenation)))
                (b* ((repetition (car concatenation))
                     (range (repetition->range repetition))
                     (element (repetition->element repetition)))
                  (and (equal range (repeat-range 1 (nati-finite 1)))
                       (element-case element :prose-val)))))))
  :no-function t)

(define remove-prose-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
  :parents (plugging)
  :short "Remove from a list of rules all the prose rules
          whose names have definitions in another list of rules."
  :long
  (xdoc::topstring-p
   "This is the first step of the "
   (xdoc::seetopic "plug-rules" "plugging operation")
   ". This step removes from @('rules1') all the prose rules
    whose names have definitions in @('rules2').")
  (cond ((endp rules1) nil)
        (t (b* ((rule (car rules1)))
             (and (mbt (rulep rule))
                  (if (and (rule-prosep rule)
                           (lookup-rulename (rule->name rule) rules2))
                      (remove-prose-rules (cdr rules1) rules2)
                    (cons rule (remove-prose-rules (cdr rules1) rules2)))))))
  :no-function t)

(define plug-rules ((rules1 rulelistp) (rules2 rulelistp))
  :returns (rules rulelistp)
  :parents (plugging)
  :short "Plug a list of rules into another list of rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "This plugs @('rules2') into @('rules1'), not vice versa.
     This choice is motivated by the fact that grammar rules
     are usually presented in a top-down manner,
     and so it seems more natural to have
     the ``plugged'' rules (e.g. HTTP)
     appear before the ``plugging'' rules (e.g. URI).")
   (xdoc::p
    "After removing from @('rules1') the prose rules
     whose names have definitions in @('rules2'),
     we find the rules in @('rules2') that transitively define
     rule names referenced but not defined
     in the remaining rules of @('rules1').
     We append the rules found after the remaining rules of @('rules1').")
   (xdoc::p
    "Thus, prose rules in @('rules1') are effectively replaced
     by corresponding rules in @('rules')
     (assuming that each prose rule removed from @('rules1')
     is the only rule in @('rules1') that defines its rule name).
     Besides replacing @('prose-rules') like this,
     the plugging operation may also provide definitions
     for rule names that are only referenced in @('rules1').")
   (xdoc::p
    "Prose rules in @('rules1')
     whose names do not have definitions in @('rules2')
     are not removed from @('rules1') and thus appear in the resulting rules.
     Similarly, rules referenced in @('rules1')
     but defined neither in @('rules1') nor in @('rules2')
     remain referenced but not defined in the resulting rules.
     These features allow multi-step plugging,
     i.e. @('rules2') is plugged into @('rules1'),
     then @('rules3') is plugged into the result of the previous operation,
     and so on."))
  (b* ((rules1 (remove-prose-rules rules1 rules2))
       (rules2 (trans-rules-of-names (difference
                                      (rulelist-called-rules rules1)
                                      (rulelist-defined-rules rules1))
                                     rules2)))
    (append rules1 rules2))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renaming
  :parents (operations)
  :short "Renaming of rules in ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is sometimes useful to systematically rename a rule in a grammar.")
   (xdoc::p
    "For example, the HTTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "RFC 7230")
    " includes a rule @('uri-host') defined by a prose value notation
     that references the rule @('host') from the URI grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
    ". Prior to @(see plugging) the URI grammar rules
     into the HTTP grammar rules,
     the rule @('host') in the URI grammar rules
     should be renamed to @('uri-host')."))
  :order-subtopics t)

(defines alt/conc/rep/elem-rename-rule
  :verify-guards nil ; done below

  (define alternation-rename-rule ((alternation alternationp)
                                   (oldname rulenamep)
                                   (newname rulenamep))
    :returns (new-alternation alternationp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in an alternation
            to a new rule name."
    :long (xdoc::topstring-@def "alternation-rename-rule")
    (cond ((endp alternation) nil)
          (t (cons (concatenation-rename-rule (car alternation)
                                              oldname newname)
                   (alternation-rename-rule (cdr alternation)
                                            oldname newname))))
    :measure (two-nats-measure (alternation-count alternation) 0)
    :no-function t)

  (define concatenation-rename-rule ((concatenation concatenationp)
                                     (oldname rulenamep)
                                     (newname rulenamep))
    :returns (new-concatenation concatenationp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in a conatenation
            to a new rule name."
    :long (xdoc::topstring-@def "concatenation-rename-rule")
    (cond ((endp concatenation) nil)
          (t (cons (repetition-rename-rule (car concatenation)
                                           oldname newname)
                   (concatenation-rename-rule (cdr concatenation)
                                              oldname newname))))
    :measure (two-nats-measure (concatenation-count concatenation) 0)
    :no-function t)

  (define repetition-rename-rule ((repetition repetitionp)
                                  (oldname rulenamep)
                                  (newname rulenamep))
    :returns (new-repetition repetitionp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in a repetition
            to a new rule name."
    :long (xdoc::topstring-@def "repetition-rename-rule")
    (make-repetition :range (repetition->range repetition)
                     :element (element-rename-rule
                               (repetition->element repetition)
                               oldname newname))
    :measure (two-nats-measure (repetition-count repetition) 1)
    :no-function t)

  (define element-rename-rule ((element elementp)
                               (oldname rulenamep)
                               (newname rulenamep))
    :returns (new-element elementp)
    :parents (renaming)
    :short "Rename all the occurrences of a rule name in an element
            to a new rule name."
    :long (xdoc::topstring-@def "element-rename-rule")
    (element-case element
                  :rulename (if (equal element.get oldname)
                                (element-rulename newname)
                              (element-fix element))
                  :group (element-group (alternation-rename-rule element.get
                                                                 oldname
                                                                 newname))
                  :option (element-option (alternation-rename-rule element.get
                                                                   oldname
                                                                   newname))
                  :char-val (element-fix element)
                  :num-val (element-fix element)
                  :prose-val (element-fix element))
    :measure (two-nats-measure (element-count element) 0)
    :no-function t)

  ///

  (verify-guards alternation-rename-rule))

(define rule-rename-rule ((rule rulep) (oldname rulenamep) (newname rulenamep))
  :returns (new-rule rulep)
  :parents (renaming)
  :short "Rename all the occurrences of a rule name to a new rule name,
          both in the definiens of a rule
          and in the name of the rule itself."
  (make-rule :name (if (equal (rule->name rule) oldname)
                       newname
                     (rule->name rule))
             :incremental (rule->incremental rule)
             :definiens (alternation-rename-rule (rule->definiens rule)
                                                 oldname newname))
  :no-function t)

(define rulelist-rename-rule ((rules rulelistp)
                              (oldname rulenamep)
                              (newname rulenamep))
  :returns (new-rules rulelistp)
  :parents (renaming)
  :short "Rename all the occurrences of a rule name to a new rule name,
          in all the rules in a list of rules."
  (cond ((endp rules) nil)
        (t (cons (rule-rename-rule (car rules) oldname newname)
                 (rulelist-rename-rule (cdr rules) oldname newname))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ removal
  :parents (operations)
  :short "Removal of rules in ABNF grammars."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is sometimes useful to remove from a grammar
     all the rules that define certain rule names.")
   (xdoc::p
    "For example, the SMTP grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5321" "RFC 5321")
    " references rules defined in the IMF grammar specified in "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5322" "RFC 5322")
    ". The IMF rules depend on a rule @('atom'),
     but the SMTP rules provide their own definition of @('Atom')
     (recall that rule names are case-insensitive).
     Thus, before @(see plugging) the IMF rules into the SMTP rules,
     the removal operation can be used to remove, from the IMF rules,
     @('atom') and possibly any other rule already defined by SMTP."))
  :order-subtopics t)

(define remove-rules-that-define ((rulenames rulename-setp) (rules rulelistp))
  :returns (new-rules rulelistp)
  :parents (removal)
  :short "Remove from a list of rules all the ones
          that define one of the given rule names."
  (cond ((endp rules) nil)
        (t (if (in (rule->name (car rules)) rulenames)
               (remove-rules-that-define rulenames (cdr rules))
             (cons (rule-fix (car rules))
                   (remove-rules-that-define rulenames (cdr rules))))))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rule-utilities
  :parents (operations)
  :short "Finding various structures within rule lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some rules or groups of rules can be used to help automate defining
     an abstract syntax corresponding to the concrete syntax defined in
     a grammar.")
   (xdoc::p
    "We begin by observing that if there is only one rule for a given
     rulename, and if the right hand side is a simple alternation of
     rulenames, then the rule names could correspond to a type/subtype
     relationship.  This relationship can be used to help generate
     an abstract syntax model of the language, and to help simplify
     code that processes values of the abstract syntax."))
  :order-subtopics t)

(define rulenames-from-singular-conc-and-rep ((concs alternationp))
  :returns (rulenames acl2::string-list-resultp)
  (b* (((when (endp concs)) nil)
       (first-conc (first concs))
       ((unless (equal (len first-conc) 1))
        (reserrf (cons :concatenation-is-not-singular first-conc)))
       (the-rep (car first-conc))
       ((unless (and (repetitionp the-rep)
                     (numrep-match-repeat-range-p
                      1 (repetition->range the-rep))))
        (reserrf (cons :not-singular-repetition the-rep)))
       (the-el (repetition->element the-rep))
       ((unless (and (elementp the-el)
                     (element-case the-el :rulename)))
        (reserrf (cons :not-rulename-element the-el)))
       (rest-rulenames (rulenames-from-singular-conc-and-rep (rest concs)))
       ((when (reserrp rest-rulenames))
        rest-rulenames)
       ((unless (acl2::string-listp rest-rulenames))
        (reserrf (cons :impossible rest-rulenames))))
    (cons (acl2::str-fix (rulename->get (element-rulename->get the-el)))
          rest-rulenames)))

(define rule-simple-subs ((rule-name acl2::stringp) (grammar rulelistp))
  :returns (sub-rule-names acl2::string-list-resultp)
  :parents (rule-utilities)
  :short "See if a rule could be used to define a type/subtype relationship."
  :long
  (xdoc::topstring
   (xdoc::p
    "This uses a very restrictive definition of whether the rule names
     in a rule are being used like a type/subtype relationship:")
   (xdoc::ul
    (xdoc::li
     "There must be only one rule with the given name in @('grammar').")
    (xdoc::li
     "It is not an incremental rule.")
    (xdoc::li
     "The rule must consist solely of an alternation of unadorned rule names.
      By unadorned we mean the concatenation and repetition are singular
      in the abstract syntax."))
   (xdoc::p
    "For example:")
   (xdoc::@{}
    "integer-type = unsigned-type / signed-type")
   (xdoc::p
    "If all of the requirements are satisified, the return value is a list
     of the \"sub\" rulenames.  Otherwise a @(see reserrp) is returned."))

  (b* (((mv rules ?not-rules)
        (rules-of-name (rulename (acl2::str-fix rule-name)) grammar))
       ((unless (equal (len rules) 1))
        (reserrf (cons :not-exactly-one-rule-with-name rule-name)))
       (the-rule (car rules))
       ((when (rule->incremental the-rule))
        (reserrf (cons :the-rule-is-incremental the-rule)))
       (alt (rule->definiens the-rule))
       ((unless (alternationp alt))
        (reserrf (cons :impossible alt))))
    (rulenames-from-singular-conc-and-rep (rule->definiens the-rule))))
