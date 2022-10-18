; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../notation/semantics")

(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/osets" :dir :system)

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

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
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define num-val-in-termset-p ((num-val num-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "Check if a numeric value notation denotes values in a set."
  (num-val-case num-val
                :direct (list-in num-val.get termset)
                :range (list-in (integers-from-to num-val.min num-val.max)
                                termset))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-sensitive-in-termset-p ((char characterp) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "Check if the code of a character is in a set."
  (in (char-code char) termset)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-insensitive-in-termset-p ((char characterp) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "Check if the code of a character,
          as well as the codes of its uppercase or lowercase counterparts,
          are in a set."
  (and (in (char-code char) termset)
       (in (char-code (upcase-char char)) termset)
       (in (char-code (downcase-char char)) termset))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist chars-sensitive-in-termset-p (x termset)
  :guard (and (character-listp x) (nat-setp termset))
  :short "Lift @(tsee char-sensitive-in-termset-p) to lists."
  (char-sensitive-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist chars-insensitive-in-termset-p (x termset)
  :guard (and (character-listp x)
              (nat-setp termset))
  :short "Lift @(tsee char-insensitive-in-termset-p) to lists."
  (char-insensitive-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-val-in-termset-p ((char-val char-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "Check if a character value notation denotes values in a set."
  (char-val-case char-val
                 :sensitive (chars-sensitive-in-termset-p
                             (explode char-val.get) termset)
                 :insensitive (chars-insensitive-in-termset-p
                               (explode char-val.get) termset))
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prose-val-in-termset-p ((prose-val prose-val-p) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "A prose value notation is unconstrained,
          so it cannot be guaranteed to denote values in a set."
  nil
  :ignore-ok t
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines alt/conc/rep/elem-in-termset-p

  (define alternation-in-termset-p ((alternation alternationp)
                                    (termset nat-setp))
    :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rule-in-termset-p ((rule rulep) (termset nat-setp))
  :returns (yes/no booleanp)
  :short "Check if all the terminal value notations in a rule
          denote values in a set."
  (alternation-in-termset-p (rule->definiens rule) termset)
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist rulelist-in-termset-p (x termset)
  :guard (and (rulelistp x)
              (nat-setp termset))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-in-termset-p ((symbol symbolp) (termset nat-setp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist string-in-termset-p (x termset)
  :guard (and (stringp x)
              (nat-setp termset))
  :short "Check if a string consists of terminals in a set and rule names."
  (symbol-in-termset-p x termset)
  :true-listp nil
  :elementp-of-nil :unknown
  ///

  (defrule string-in-termset-p-when-nat-listp
    (implies (nat-listp nats)
             (equal (string-in-termset-p nats termset)
                    (list-in nats termset)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule leaves-in-termset-when-match-num-val-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nat-in-termset-when-match-sensitive-char-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nats-in-termset-when-match-sensitive-chars-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nat-in-termset-when-match-insensitive-char-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nats-in-termset-when-match-insensitive-chars-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule leaves-in-termset-when-match-char-val-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection leaves-in-termset-when-match-alt/conc/rep/elem-in-termset
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled terminal-strings-in-termset-when-rules-in-termset
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
