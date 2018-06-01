; ABNF Library -- Semantics
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "abstract-syntax")

(local (include-book "kestrel/utilities/list-theorems" :dir :system))
(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/true-list-listp-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-list-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc semantics
  :parents (abnf)
  :short "Semantics of ABNF."
  :long
  "<p>
   The abstract syntactic entities of ABNF
   denote tree structures built by expanding the rules.
   When all the rule names are expanded,
   the leaves of the tree form a sequence of terminal values,
   for which the tree is a parse tree.
   </p>
   <p>
   These concepts are analogous to the ones
   for the typical notion of formal grammar in textbooks,
   but because ABNF is more complex, its semantics are more complex.
   </p>")

(xdoc::order-subtopics semantics nil t)

(fty::defflexsum symbol
  :parents (semantics)
  :short "Symbols."
  :long
  "<p>
   As explained in RFC.2.3, the terminal values of ABNF are natural numbers.
   </p>
   <p>
   Rule names are the nonterminal symbols of ABNF.
   </p>
   <p>
   In analogy with the typical notion of formal grammar in textbooks,
   an ABNF symbol is a terminal or a nonterminal,
   i.e. a natural number or a rule name.
   </p>
   <p>
   Since natural numbers and rule names are disjoint,
   we put them together without tags.
   </p>"
  (:terminal :fields ((get :type nat :acc-body x))
             :ctor-body get
             :cond (natp x))
  (:nonterminal :fields ((get :type rulename :acc-body x))
                :ctor-body get)
  :pred symbolp
  ///

  (defrule disjoint-nat/rulename
    :parents (symbol)
    (not (and (natp x)
              (rulenamep x)))
    :rule-classes nil)

  (defrule symbolp-when-natp
    :parents (symbol)
    (implies (natp x)
             (symbolp x))
    :enable symbolp)

  (defrule symbolp-when-rulenamep
    :parents (symbol)
    (implies (rulenamep x)
             (symbolp x))
    :enable symbolp)

  (defruled symbolp-alt-def
    :parents (symbol)
    (equal (symbolp x)
           (or (natp x)
               (rulenamep x)))
    :enable symbolp))

(fty::deflist string
  :parents (semantics)
  :short "Strings."
  :long
  "<p>
   A string is a true list of symbols.
   </p>"
  :elt-type symbol
  :true-listp t
  :pred stringp
  ///

  (defrule stringp-when-nat-listp
    :parents (string)
    (implies (nat-listp x)
             (stringp x))
    :enable stringp))

(fty::deftypes trees

  (fty::deftagsum tree
    :parents (semantics)
    :short "Trees of rule names and terminal values."
    :long
    "<p>
     This type captures the basic structure of ABNF trees,
     without reference to specific rules.
     </p>
     <p>
     Since a single @('num-val') or @('char-val')
     may expand into a sequence of terminal values (i.e. natural numbers),
     we use lists of natural numbers as leaves of the trees.
     </p>
     <p>
     To represent trees whose rule names are not all expanded,
     rule names may appear as leaves too.
     </p>
     <p>
     A non-leaf node of a tree is optionally labeled by a rule name.
     When it is labeled by a rule name,
     the branches correspond to
     a @(see concatenation) chosen from
     the @(see alternation) associated to the rule name.
     But since a concatenation is a sequence of @(see repetition)s,
     and a repetition may expand to multiple instances
     of the @(see element) of the repetition,
     the branches are organized as a list of lists:
     the outer list corresponds to
     the list of repetitions that form the chosen concatenation,
     while each inner list corresponds to
     the element instances of the corresponding repetition.
     An empty inner list is used for a repetition of no elements.
     An empty outer list is used for an empty concatenation,
     which is disallowed by RFC.4 but allowed by our abstract syntax;
     an empty outer list is also used for an option (RFC.3.8) that is absent.
     </p>
     <p>
     Since, via groups (RFC.3.5) and options (RFC.3.8),
     an element may recursively be an alternation,
     if a branch in an inner list under a rule name is an alternation,
     that branch recursively has a list of lists of branches.
     In this case, there is no rule name labeling the root of this branch.
     A rule name provides a name for an alternation;
     the presence of a rule name in a non-leaf node of a tree
     indicates that a named alternation is expanded at that place in the tree.
     </p>"
    (:leafterm ((get nat-list)))
    (:leafrule ((get rulename)))
    (:nonleaf ((rulename? maybe-rulename)
               (branches tree-list-list)))
    :pred treep
    ///

    (defruled tree-fix-when-nonleaf-norulename-nobranches
      :parents (tree)
      (implies (and (equal (tree-kind tree) :nonleaf)
                    (not (tree-nonleaf->rulename? tree))
                    (not (consp (tree-nonleaf->branches tree))))
               (equal (tree-fix tree)
                      '(:nonleaf nil nil)))
      :enable (tree-fix tree-nonleaf->rulename? tree-nonleaf->branches)))

  (fty::deflist tree-list
    :parents (semantics)
    :short "True lists of trees of rule names and terminal values."
    :long
    "<p>
     As explained <see topic='@(url tree)'>here</see>,
     these are the inner lists that correspond to repetitions.
     </p>"
    :elt-type tree
    :true-listp t
    :pred tree-listp)

  (fty::deflist tree-list-list
    :parents (semantics)
    :short "True lists of true lists
            of trees of rule names and terminal values."
    :long
    "<p>
     As explained <see topic='@(url tree)'>here</see>,
     these are the outer lists that correspond to concatenations.
     </p>"
    :elt-type tree-list
    :true-listp t
    :pred tree-list-listp
    ///

    (defrule true-list-listp-when-tree-list-listp
      :parents (tree-list-list)
      (implies (tree-list-listp treess)
               (true-list-listp treess)))))

(defrule true-listp-of-car-of-tree-nonleaf->branches
  :parents (tree)
  (true-listp (car (tree-nonleaf->branches x)))
  :rule-classes :type-prescription)

(fty::defoption maybe-tree
  tree
  :parents (semantics)
  :short "Union of trees and @('nil')."
  :pred maybe-treep)

(define set-all-treep ((set setp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Check if all the elements of a set are trees."
  (or (empty set)
      (and (treep (head set))
           (set-all-treep (tail set))))
  :no-function t
  ///

  (defrule set-all-treep-of-insert
    (equal (set-all-treep (insert tree trees))
           (and (treep tree)
                (set-all-treep (sfix trees))))))

(define tree-setp (x)
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Recognize finite sets of trees."
  (and (setp x)
       (set-all-treep x))
  :no-function t
  ///

  (defrule setp-when-tree-setp
    (implies (tree-setp trees)
             (setp trees)))

  (defrule tree-setp-of-insert
    (equal (tree-setp (insert tree trees))
           (and (treep tree)
                (tree-setp (sfix trees))))))

(defines tree->string
  :parents (semantics)
  :short "String at the leaves of trees."
  :long
  "<p>
   This collects all the leaves of a tree, left to right,
   and assembles them into a string.
   </p>
   @(def tree->string)
   @(def tree-list->string)
   @(def tree-list-list->string)"

  (define tree->string ((tree treep))
    :returns (string stringp)
    (tree-case tree
               :leafterm tree.get
               :leafrule (list tree.get)
               :nonleaf (tree-list-list->string tree.branches))
    :measure (tree-count tree)
    :no-function t)

  (define tree-list->string ((trees tree-listp))
    :returns (string stringp)
    (cond ((endp trees) nil)
          (t (append (tree->string (car trees))
                     (tree-list->string (cdr trees)))))
    :measure (tree-list-count trees)
    :no-function t)

  (define tree-list-list->string ((treess tree-list-listp))
    :returns (string stringp)
    (cond ((endp treess) nil)
          (t (append (tree-list->string (car treess))
                     (tree-list-list->string (cdr treess)))))
    :measure (tree-list-list-count treess)
    :no-function t)

  ///

  (defrule tree-list->string-when-atom
    (implies (atom trees)
             (equal (tree-list->string trees) nil)))

  (defrule tree-list->string-of-cons
    (equal (tree-list->string (cons tree trees))
           (append (tree->string tree)
                   (tree-list->string trees))))

  (defrule tree-list-list->string-when-atom
    (implies (atom treess)
             (equal (tree-list-list->string treess) nil)))

  (defrule tree-list-list->string-of-cons
    (equal (tree-list-list->string (cons trees treess))
           (append (tree-list->string trees)
                   (tree-list-list->string treess)))))

(defines tree-terminatedp
  :parents (semantics)
  :short "Notion of terminated tree."
  :long
  "<p>
   A tree is terminated iff all its leaves are natural numbers (not rule names).
   </p>
   @(def tree-terminatedp)
   @(def tree-list-terminatedp)
   @(def tree-list-list-terminatedp)"

  (define tree-terminatedp ((tree treep))
    :returns (yes/no booleanp)
    (tree-case tree
               :leafterm t
               :leafrule nil
               :nonleaf (tree-list-list-terminatedp tree.branches))
    :measure (tree-count tree)
    :no-function t)

  (define tree-list-terminatedp ((trees tree-listp))
    :returns (yes/no booleanp)
    (or (endp trees)
        (and (tree-terminatedp (car trees))
             (tree-list-terminatedp (cdr trees))))
    :measure (tree-list-count trees)
    :no-function t)

  (define tree-list-list-terminatedp ((treess tree-list-listp))
    :returns (yes/no booleanp)
    (or (endp treess)
        (and (tree-list-terminatedp (car treess))
             (tree-list-list-terminatedp (cdr treess))))
    :measure (tree-list-list-count treess)
    :no-function t)

  ///

  (std::deflist tree-list-terminatedp (x)
    (tree-terminatedp x)
    :guard (tree-listp x)
    :elementp-of-nil t)

  (std::deflist tree-list-list-terminatedp (x)
    (tree-list-terminatedp x)
    :guard (tree-list-listp x)
    :elementp-of-nil t)

  (defrule tree-list-terminatedp-when-atom
    (implies (atom trees)
             (tree-list-terminatedp trees)))

  (defrule tree-list-list-terminatedp-when-atom
    (implies (atom treess)
             (tree-list-list-terminatedp treess)))

  (defthm-tree-terminatedp-flag

    (defthm nat-listp-of-tree->string-when-terminated
      (implies (tree-terminatedp tree)
               (nat-listp (tree->string tree)))
      :flag tree-terminatedp)

    (defthm nat-listp-of-tree-list->string-when-terminated
      (implies (tree-list-terminatedp trees)
               (nat-listp (tree-list->string trees)))
      :flag tree-list-terminatedp)

    (defthm nat-listp-of-tree-list-list->string-when-terminated
      (implies (tree-list-list-terminatedp treess)
               (nat-listp (tree-list-list->string treess)))
      :flag tree-list-list-terminatedp)

    :hints (("Goal" :in-theory (enable tree->string
                                       tree-list->string
                                       tree-list-list->string)))))

(define tree-match-num-val-p ((tree treep) (num-val num-val-p))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of numeric value notations."
  :long
  "<p>
   A tree matches a numeric value notation iff
   one of the following conditions holds:
   </p>
   <ul>
     <li>
     The numeric value notation is a list of natural numbers,
     and the tree is a leaf consisting of exactly that list of natural numbers.
     </li>
     <li>
     The numeric value notation is a range of natural numbers,
     and the tree is a leaf consisting of one natural number in that range.
     (Note that no tree matches a range whose minimum exceeds the maximum.)
     </li>
   </ul>"
  (and (tree-case tree :leafterm)
       (let ((nats (tree-leafterm->get tree)))
         (num-val-case num-val
                       :direct (equal nats num-val.get)
                       :range (and (= (len nats) 1)
                                   (<= num-val.min (car nats))
                                   (<= (car nats) num-val.max)))))
  :guard-hints (("Goal"
                 :cases
                 ((natp (car (tree-leafterm->get tree))))
                 ;; Matt K. mod to get proof to work in ACL2(r):
                 :in-theory (enable tree-leafterm->get)))
  :no-function t)

(define nat-match-sensitive-char-p ((nat natp) (char characterp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of characters in case-sensitive character value notations."
  :long
  "<p>
   A natural number matches
   a character in a case-sensitive character value notation iff
   the natural number is the character's code.
   </p>"
  (equal nat (char-code char))
  :no-function t
  ///

  (defrule nat-match-sensitive-char-p-of-char-fix
    (equal (nat-match-sensitive-char-p nat (char-fix char))
           (nat-match-sensitive-char-p nat char))))

(define nat-match-insensitive-char-p ((nat natp) (char characterp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of characters
          in case-insensitive character value notations."
  :long
  "<p>
   A natural number matches
   a character in a case-insensitive character value notation iff
   the natural number is the code
   of the character or
   of the uppercase or lowercase counterpart of the character.
   </p>"
  (or (equal nat (char-code char))
      (equal nat (char-code (upcase-char char)))
      (equal nat (char-code (downcase-char char))))
  :no-function t
  ///

  (defrule nat-match-insensitive-char-p-of-char-fix
    (equal (nat-match-insensitive-char-p nat (char-fix char))
           (nat-match-insensitive-char-p nat char))))

(define nats-match-sensitive-chars-p ((nats nat-listp)
                                      (chars character-listp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Lifting of @(tsee nat-match-sensitive-char-p) to lists."
  (cond ((endp nats) (endp chars))
        (t (and (consp chars)
                (nat-match-sensitive-char-p (car nats) (car chars))
                (nats-match-sensitive-chars-p (cdr nats) (cdr chars)))))
  :no-function t
  ///

  (defrule nats-match-sensitive-chars-p-when-atom-chars
    (implies (atom chars)
             (equal (nats-match-sensitive-chars-p nats chars)
                    (not (consp nats)))))

  (defrule nats-match-sensitive-chars-p-of-cons-chars
    (equal (nats-match-sensitive-chars-p nats (cons char chars))
           (and (consp nats)
                (nat-match-sensitive-char-p (car nats) char)
                (nats-match-sensitive-chars-p (cdr nats) chars)))))

(define nats-match-insensitive-chars-p ((nats nat-listp)
                                        (chars character-listp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Lifting of @(tsee nat-match-insensitive-char-p) to lists."
  (cond ((endp nats) (endp chars))
        (t (and (consp chars)
                (nat-match-insensitive-char-p (car nats) (car chars))
                (nats-match-insensitive-chars-p (cdr nats) (cdr chars)))))
  :no-function t
  ///

  (defrule nats-match-insensitive-chars-p-when-atom-chars
    (implies (atom chars)
             (equal (nats-match-insensitive-chars-p nats chars)
                    (not (consp nats)))))

  (defrule nats-match-insensitive-chars-p-of-cons-chars
    (equal (nats-match-insensitive-chars-p nats (cons char chars))
           (and (consp nats)
                (nat-match-insensitive-char-p (car nats) char)
                (nats-match-insensitive-chars-p (cdr nats) chars)))))

(define tree-match-char-val-p ((tree treep) (char-val char-val-p))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of character value notations."
  :long
  "<p>
   A tree matches a character value notation iff
   the tree is a leaf consisting of a list of natural numbers
   that match the corresponding characters,
   case-sensitively or case-insensitively
   (depending on the kind of character value notation).
   </p>"
  (and
   (tree-case tree :leafterm)
   (let ((nats (tree-leafterm->get tree)))
     (char-val-case char-val
                    :sensitive (nats-match-sensitive-chars-p
                                nats (explode char-val.get))
                    :insensitive (nats-match-insensitive-chars-p
                                  nats (explode char-val.get)))))
  :no-function t)

(define tree-match-prose-val-p ((tree treep) (prose-val prose-val-p))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of prose value notations."
  :long
  "<p>
   Formally speaking, any tree matches prose,
   because prose has no formal semantics.
   When a rule includes prose,
   its meaning can be formalized via external predicates on trees.
   </p>"
  t
  :ignore-ok t
  :no-function t)

(define numrep-match-repeat-range-p ((numrep natp) (range repeat-rangep))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Semantics of repetition ranges."
  :long
  "<p>
   A number of repetitions (a natural number) matches a repetition range iff
   it is between the range's minimum and the range's maximum.
   </p>"
  (let ((min (repeat-range->min range))
        (max (repeat-range->max range)))
    (and (<= min numrep)
         (or (nati-case max :infinity)
             (<= numrep (nati-finite->get max)))))
  :no-function t
  ///

  (defrule 0-when-match-repeat-range-0
    (implies (equal range (repeat-range 0 (nati-finite 0)))
             (equal (numrep-match-repeat-range-p n range)
                    (equal n 0)))
    :enable numrep-match-repeat-range-p))

(define lookup-rulename ((rulename rulenamep) (rules rulelistp))
  :returns (alternation alternationp)
  :parents (semantics)
  :short "Collect all the alternatives associated to a rule name
          from some rules."
  :long
  "<p>
   For <see topic='@(url rule-wfp)'>well-formed rules</see>,
   this function is an appropriate way to test whether @('rulename')
   appears (on the left side of) some rule in @('rules').
   The reason is that well-formed rules
   must have non-empty alternations as definientia.
   </p>"
  (cond ((endp rules) nil)
        (t (let ((rule (car rules)))
             (if (equal (rule->name rule) rulename)
                 (append (rule->definiens rule)
                         (lookup-rulename rulename (cdr rules)))
               (lookup-rulename rulename (cdr rules))))))
  :no-function t)

(defines tree-match-alt/conc/rep/elem-p
  :flag-local nil

  (define tree-list-list-match-alternation-p ((treess tree-list-listp)
                                              (alternation alternationp)
                                              (rules rulelistp))
    :returns (yes/no booleanp)
    :parents (semantics)
    :short "Semantics of alternations."
    :long
    "<p>
     A list of lists of trees matches an alternation iff
     it matches one of its concatenations.
     </p>
     @(def tree-list-list-match-alternation-p)"
    (and (consp alternation)
         (or (tree-list-list-match-concatenation-p treess
                                                   (car alternation)
                                                   rules)
             (tree-list-list-match-alternation-p treess
                                                 (cdr alternation)
                                                 rules)))
    :measure (two-nats-measure (tree-list-list-count treess)
                               (alternation-count alternation))
    :no-function t)

  (define tree-list-list-match-concatenation-p ((treess tree-list-listp)
                                                (concatenation concatenationp)
                                                (rules rulelistp))
    :returns (yes/no booleanp)
    :parents (semantics)
    :short "Semantics of concatenations."
    :long
    "<p>
     A list of lists of trees matches a concatenation iff
     each list of trees matches the corresponding repetition.
     </p>
     @(def tree-list-list-match-concatenation-p)"
    (cond ((endp treess) (endp concatenation))
          (t (and (consp concatenation)
                  (tree-list-match-repetition-p (car treess)
                                                (car concatenation)
                                                rules)
                  (tree-list-list-match-concatenation-p (cdr treess)
                                                        (cdr concatenation)
                                                        rules))))
    :measure (two-nats-measure (tree-list-list-count treess)
                               (concatenation-count concatenation))
    :no-function t)

  (define tree-list-match-repetition-p ((trees tree-listp)
                                        (repetition repetitionp)
                                        (rules rulelistp))
    :returns (yes/no booleanp)
    :parents (semantics)
    :short "Semantics of repetitions."
    :long
    "<p>
     A list of trees matches a repetition iff
     the length of the list matches the range of the repetition
     and each tree in the list matches the element of the repetition.
     </p>
     @(def tree-list-match-repetition-p)"
    (and (numrep-match-repeat-range-p (len trees)
                                      (repetition->range repetition))
         (tree-list-match-element-p trees
                                    (repetition->element repetition)
                                    rules))
    :measure (two-nats-measure (tree-list-count trees)
                               (repetition-count repetition))
    :no-function t)

  (define tree-list-match-element-p ((trees tree-listp)
                                     (element elementp)
                                     (rules rulelistp))
    :returns (yes/no booleanp)
    :parents (semantics)
    :short "Auxiliary function to define @(tsee tree-list-match-repetition-p)."
    :long
    "<p>
     A list of trees matches an element iff each tree matches the element.
     </p>
     @(def tree-list-match-element-p)"
    (or (atom trees)
        (and (tree-match-element-p (car trees)
                                   element
                                   rules)
             (tree-list-match-element-p (cdr trees)
                                        element
                                        rules)))
    :measure (two-nats-measure (tree-list-count trees)
                               (element-count element))
    :no-function t)

  (define tree-match-element-p ((tree treep)
                                (element elementp)
                                (rules rulelistp))
    :returns (yes/no booleanp)
    :parents (semantics)
    :short "Semantics of elements."
    :long
    "<p>
     A tree matches an element iff one of the following conditions holds:
     </p>
     <ul>
       <li>
       The element is a rule name,
       and the tree is a leaf consisting of the rule name.
       In this situation, the rule name is not expanded.
       </li>
       <li>
       The element is a rule name,
       the tree is a non-leaf with that rule name,
       the rules associate an alternation to the rule name,
       and the branches of the tree match that alternation.
       In this situation, the rule name is expanded.
       </li>
       <li>
       The element is a grouped alternation,
       the tree is a non-leaf without rule name,
       and the branches of the tree match the alternation.
       </li>
       <li>
       The element is an optional alternation,
       the tree is a non-leaf without rule name,
       and either the branches of the tree match the alternation
       or the tree has no branches.
       </li>
       <li>
       The element is a numeric value notation
       and the tree matches it.
       </li>
       <li>
       The element is a character value notation
       and the tree matches it.
       </li>
       <li>
       The element is a prose value notation
       and the tree matches it.
       </li>
     </ul>
     @(def tree-match-element-p)"
    (element-case
     element
     :rulename (tree-case
                tree
                :leafterm nil
                :leafrule (equal tree.get element.get)
                :nonleaf (and (equal tree.rulename? element.get)
                              (let ((alternation
                                     (lookup-rulename element.get rules)))
                                (tree-list-list-match-alternation-p
                                 tree.branches alternation rules))))
     :group (and (tree-case tree :nonleaf)
                 (null (tree-nonleaf->rulename? tree))
                 (tree-list-list-match-alternation-p
                  (tree-nonleaf->branches tree)
                  element.get
                  rules))
     :option (and (tree-case tree :nonleaf)
                  (null (tree-nonleaf->rulename? tree))
                  (or (tree-list-list-match-alternation-p
                       (tree-nonleaf->branches tree)
                       element.get
                       rules)
                      (null (tree-nonleaf->branches tree))))
     :char-val (tree-match-char-val-p tree element.get)
     :num-val (tree-match-num-val-p tree element.get)
     :prose-val (tree-match-prose-val-p tree element.get))
    :measure (two-nats-measure (tree-count tree)
                               (element-count element))
    :no-function t)

  ///

  (defrule tree-list-list-match-alternation-p-when-atom-alternation
    :parents (tree-list-list-match-alternation-p)
    (implies (atom alternation)
             (not (tree-list-list-match-alternation-p treess
                                                      alternation
                                                      rules))))

  (defrule tree-list-list-match-alternation-p-of-cons-alternation
    :parents (tree-list-list-match-alternation-p)
    (equal (tree-list-list-match-alternation-p treess
                                               (cons concatenation alternation)
                                               rules)
           (or (tree-list-list-match-concatenation-p treess concatenation rules)
               (tree-list-list-match-alternation-p treess alternation rules))))

  (defrule tree-list-list-match-concatenation-p-when-atom-concatenation
    :parents (tree-list-list-match-concatenation-p)
    (implies (atom concatenation)
             (equal (tree-list-list-match-concatenation-p treess
                                                          concatenation
                                                          rules)
                    (not (consp treess)))))

  (defrule tree-list-list-match-concatenation-p-of-cons-concatenation
    :parents (tree-list-list-match-concatenation-p)
    (equal (tree-list-list-match-concatenation-p treess
                                                 (cons repetition concatenation)
                                                 rules)
           (and (consp treess)
                (tree-list-match-repetition-p (car treess)
                                              repetition
                                              rules)
                (tree-list-list-match-concatenation-p (cdr treess)
                                                      concatenation
                                                      rules))))

  (defruled tree-list-match-repetition-p-of-1-repetition
    :parents (tree-list-match-repetition-p)
    (implies (equal (repetition->range repetition)
                    (repeat-range 1 (nati-finite 1)))
             (equal (tree-list-match-repetition-p trees repetition rules)
                    (and (consp trees)
                         (not (consp (cdr trees)))
                         (tree-match-element-p (car trees)
                                               (repetition->element repetition)
                                               rules))))
    :enable numrep-match-repeat-range-p)

  (defruled tree-list-match-repetition-p-of-1+-repetitions
    :parents (tree-list-match-repetition-p)
    (implies (equal (repetition->range repetition)
                    (repeat-range 1 (nati-infinity)))
             (equal (tree-list-match-repetition-p trees repetition rules)
                    (and (consp trees)
                         (tree-match-element-p (car trees)
                                               (repetition->element repetition)
                                               rules)
                         (tree-list-match-repetition-p
                          (cdr trees)
                          (repetition (repeat-range 0 (nati-infinity))
                                      (repetition->element repetition))
                          rules))))
    :enable numrep-match-repeat-range-p)

  (defruled tree-list-match-repetition-p-of-0+-reps-when-consp
    :parents (tree-list-match-repetition-p)
    (implies (and (consp trees)
                  (equal (repetition->range repetition)
                         (repeat-range 0 (nati-infinity))))
             (equal (tree-list-match-repetition-p trees repetition rules)
                    (and (tree-match-element-p (car trees)
                                               (repetition->element repetition)
                                               rules)
                         (tree-list-match-repetition-p (cdr trees)
                                                       repetition
                                                       rules))))
    :enable numrep-match-repeat-range-p)

  (defrule tree-list-match-repetition-p-of-0+-reps-when-1+-reps
    :parents (tree-list-match-repetition-p)
    (implies (tree-list-match-repetition-p trees
                                           (repetition
                                            (repeat-range 1 (nati-infinity))
                                            element)
                                           rules)
             (tree-list-match-repetition-p trees
                                           (repetition
                                            (repeat-range 0 (nati-infinity))
                                            element)
                                           rules))
    :rule-classes nil
    :enable numrep-match-repeat-range-p)

  (defrule tree-list-match-repetition-p-of-1+-reps-when-0+-reps
    :parents (tree-list-match-repetition-p)
    (implies (and (tree-list-match-repetition-p trees
                                                (repetition
                                                 (repeat-range 0 (nati-infinity))
                                                 element)
                                                rules)
                  (consp trees))
             (tree-list-match-repetition-p trees
                                           (repetition
                                            (repeat-range 1 (nati-infinity))
                                            element)
                                           rules))
    :rule-classes nil
    :enable numrep-match-repeat-range-p)

  (std::deflist tree-list-match-element-p (x element rules)
    (tree-match-element-p x element rules)
    :guard (and (tree-listp x)
                (elementp element)
                (rulelistp rules))
    :elementp-of-nil :unknown)

  (defrule nat-listp-of-tree->string-when-match-element-num/char-val
    :parents (tree-match-element-p)
    (implies (and (tree-match-element-p tree element rules)
                  (member-equal (element-kind element)
                                '(:num-val :char-val)))
             (nat-listp (tree->string tree)))
    :enable (tree-match-num-val-p
             tree-match-char-val-p
             tree->string)))

(define parse-treep
  (tree (string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Recognize the parse trees of a string,
          with respect to a rule name and a list of rules."
  :long
  "<p>
   Given a list of rules, a rule name, and a string,
   a parse tree for the string is a tree
   that matches the rule name (viewed as an element)
   and such that the string is the one at the leaves of the tree.
   A parse tree describes
   how a string is an &ldquo;instance&rdquo; of the rule name,
   given the rules.
   </p>"
  (and (treep tree)
       (tree-match-element-p tree (element-rulename rulename) rules)
       (equal (tree->string tree)
              string))
  :no-function t
  ///

  (defrule treep-when-parse-treep
    (implies (parse-treep tree string rulename rules)
             (treep tree))))

(define-sk string-parsablep
  ((string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Notion of parsable string."
  :long
  "<p>
   A string is parsable iff it has at least one parse tree.
   </p>"
  (exists (tree)
          (parse-treep tree string rulename rules))
  ///

  (defrule treep-of-string-parsablep-witness-when-string-parsablep
    (implies (string-parsablep string rulename rules)
             (treep (string-parsablep-witness string rulename rules))))

  (defrule not-parse-treep-when-not-string-parsablep
    (implies (not (string-parsablep string rulename rules))
             (not (parse-treep tree string rulename rules)))))

(define-sk string-ambiguousp
  ((string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Notion of ambiguous string."
  :long
  "<p>
   A string is ambiguous iff it has at least two distinct parse trees.
   </p>"
  (exists (tree1 tree2)
          (and (not (equal tree1 tree2))
               (parse-treep tree1 string rulename rules)
               (parse-treep tree2 string rulename rules)))
  ///

  (defruled string-parsablep-when-string-ambiguousp
    (implies (string-ambiguousp string rulename rules)
             (string-parsablep string rulename rules))
    :enable (string-ambiguousp string-parsablep-suff))

  (defrule at-most-one-parse-tree-when-not-string-ambiguousp
    (implies (and (not (string-ambiguousp string rulename rules))
                  (parse-treep tree1 string rulename rules)
                  (parse-treep tree2 string rulename rules))
             (equal tree1 tree2))
    :rule-classes nil))

(define string-unambiguousp
  ((string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Notion of unambiguous string."
  :long
  "<p>
   A string is unambiguous iff it has exactly one parse tree.
   </p>"
  (and (string-parsablep string rulename rules)
       (not (string-ambiguousp string rulename rules)))
  :no-function t
  ///

  (defrule parse-treep-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (equal (parse-treep tree string rulename rules)
                    (equal tree
                           (string-parsablep-witness string rulename rules))))
    :enable string-parsablep
    :use (:instance at-most-one-parse-tree-when-not-string-ambiguousp
                    (tree1 tree)
                    (tree2 (string-parsablep-witness string rulename rules))))

  (defrule treep-of-string-parsablep-witness-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (treep (string-parsablep-witness string rulename rules)))))

(define-sk parse-trees-of-string-p
  ((trees tree-setp) (string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Check if a finite set of trees is
          the set of all and only the parse trees of a string."
  :long
  "<p>
   If this is true, then the string has a finite number of parse trees.
   </p>"
  (forall (tree)
          (iff (in tree trees)
               (parse-treep tree string rulename rules)))
  ///

  (defrule at-most-one-parse-tree-set-of-string
    (implies (and (tree-setp trees1)
                  (tree-setp trees2)
                  (parse-trees-of-string-p trees1 string rulename rules)
                  (parse-trees-of-string-p trees2 string rulename rules))
             (equal trees1 trees2))
    :rule-classes nil
    :enable (double-containment pick-a-point-subset-strategy)
    :disable parse-trees-of-string-p)

  (defrule parse-trees-of-string-p-when-not-string-parsablep
    (implies (and (not (string-parsablep string rulename rules))
                  (tree-setp trees))
             (equal (parse-trees-of-string-p trees string rulename rules)
                    (equal trees nil)))
    :use (:instance at-most-one-parse-tree-set-of-string
                    (trees1 trees)
                    (trees2 nil)))

  (defrule not-string-parsablep-when-parse-trees-of-string-p-of-nil
    (implies (parse-trees-of-string-p nil string rulename rules)
             (not (string-parsablep string rulename rules)))
    :enable string-parsablep
    :disable parse-trees-of-string-p-necc
    :use (:instance parse-trees-of-string-p-necc
                    (trees nil)
                    (tree (string-parsablep-witness string rulename rules))))

  (defrule parse-trees-of-string-p-when-string-unambiguousp
    (implies (and (string-unambiguousp string rulename rules)
                  (tree-setp trees))
             (equal (parse-trees-of-string-p trees string rulename rules)
                    (equal trees
                           (insert
                            (string-parsablep-witness string rulename rules)
                            nil))))
    :use (:instance at-most-one-parse-tree-set-of-string
                    (trees1 trees)
                    (trees2 (insert
                             (string-parsablep-witness string rulename rules)
                             nil))))

  (defrule string-unambiguousp-when-parse-trees-of-string-p-of-one
    (implies (parse-trees-of-string-p
              (insert (string-parsablep-witness string rulename rules) nil)
              string rulename rules)
             (string-unambiguousp string rulename rules))
    :enable (string-unambiguousp string-ambiguousp)
    :disable parse-trees-of-string-p-necc
    :use ((:instance parse-trees-of-string-p-necc
                     (trees (insert
                             (string-parsablep-witness string rulename rules)
                             nil))
                     (tree (string-parsablep-witness string rulename rules)))
          (:instance parse-trees-of-string-p-necc
                     (trees (insert
                             (string-parsablep-witness string rulename rules)
                             nil))
                     (tree (mv-nth 0 (string-ambiguousp-witness
                                      string rulename rules))))
          (:instance parse-trees-of-string-p-necc
                     (trees (insert
                             (string-parsablep-witness string rulename rules)
                             nil))
                     (tree (mv-nth 1 (string-ambiguousp-witness
                                      string rulename rules)))))))

(define-sk finite-parse-trees-p
  ((string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Check if a string has a finite number of parse trees."
  :long
  "<p>
   If this is not true, the string is ambiguous,
   because it has an infinite number of parse trees.
   </p>"
  (exists (trees)
          (and (tree-setp trees)
               (parse-trees-of-string-p trees string rulename rules)))
  ///

  (defrule tree-setp-of-finite-parse-trees-p-witness-when-finite-parse-trees-p
    (implies (finite-parse-trees-p string rulename rules)
             (tree-setp (finite-parse-trees-p-witness string rulename rules))))

  (defrule finite-parse-trees-p-when-not-string-parsablep
    (implies (not (string-parsablep string rulename rules))
             (finite-parse-trees-p string rulename rules))
    :use (:instance finite-parse-trees-p-suff (trees nil)))

  (defrule finite-parse-trees-p-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (finite-parse-trees-p string rulename rules))
    :use (:instance finite-parse-trees-p-suff
                    (trees (insert (string-parsablep-witness
                                    string rulename rules)
                                   nil))))

  (defrule finite-parse-trees-p-witness-when-not-string-parsablep
    (implies (not (string-parsablep string rulename rules))
             (equal (finite-parse-trees-p-witness string rulename rules)
                    nil))
    :disable finite-parse-trees-p-when-not-string-parsablep
    :use finite-parse-trees-p-when-not-string-parsablep)

  (defrule finite-parse-trees-p-witness-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (equal (finite-parse-trees-p-witness string rulename rules)
                    (insert (string-parsablep-witness string rulename rules)
                            nil)))
    :disable finite-parse-trees-p-when-string-unambiguousp
    :use finite-parse-trees-p-when-string-unambiguousp)

  (defrule not-string-parsablep-when-finite-parse-trees-p-nil
    (implies (and (finite-parse-trees-p string rulename rules)
                  (equal (finite-parse-trees-p-witness string rulename rules)
                         nil))
             (not (string-parsablep string rulename rules))))

  (defrule string-unambiguousp-when-finite-parse-trees-p-one
    (implies (and (finite-parse-trees-p string rulename rules)
                  (equal (finite-parse-trees-p-witness string rulename rules)
                         (insert
                          (string-parsablep-witness string rulename rules)
                          nil)))
             (string-unambiguousp string rulename rules)))

  (defruled string-ambiguousp-when-infinite-parse-trees
    (implies (not (finite-parse-trees-p string rulename rules))
             (string-ambiguousp string rulename rules))
    :cases ((string-parsablep string rulename rules))
    :use ((:instance finite-parse-trees-p-suff (trees nil))
          finite-parse-trees-p-when-string-unambiguousp)
    :enable (string-unambiguousp
             string-parsablep-suff
             parse-trees-of-string-p)))

(define parse ((string stringp) (rulename rulenamep) (rules rulelistp))
  :returns (result (or (tree-setp result)
                       (equal result :infinite))
                   :hints (("Goal" :in-theory (enable finite-parse-trees-p))))
  :parents (semantics)
  :short "Parse a string."
  :long
  "<p>
   If the string has a finite number of parse trees,
   return the finite set of its parse trees.
   Otherwise, return @(':infinite') to indicate that
   the string has an infinite number of parse trees.
   </p>"
  (if (finite-parse-trees-p string rulename rules)
      (finite-parse-trees-p-witness string rulename rules)
    :infinite)
  :no-function t
  ///

  (defruled distinguish-infinite-from-trees
    (not (tree-setp :infinite)))

  (defrule parse-when-not-string-parsablep
    (implies (not (string-parsablep string rulename rules))
             (equal (parse string rulename rules)
                    nil)))

  (defrule parse-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (equal (parse string rulename rules)
                    (insert (string-parsablep-witness string rulename rules)
                            nil))))

  (defrule not-string-parsablep-when-parse-nil
    (implies (equal (parse string rulename rules)
                    nil)
             (not (string-parsablep string rulename rules))))

  (defrule string-unambiguousp-when-parse-one
    (implies (equal (parse string rulename rules)
                    (insert (string-parsablep-witness string rulename rules)
                            nil))
             (string-unambiguousp string rulename rules))))

(define parse! ((string stringp) (rulename rulenamep) (rules rulelistp))
  :guard (string-unambiguousp string rulename rules)
  :returns (tree treep)
  :parents (semantics)
  :short "Parse an unambiguous string."
  :long
  "<p>
   The result is the unique parse tree.
   </p>"
  (mbe :logic (tree-fix (string-parsablep-witness string rulename rules))
       :exec (string-parsablep-witness string rulename rules))
  :guard-hints (("Goal" :in-theory (enable string-unambiguousp)))
  :no-function t
  ///

  (defrule parse-is-parse!-when-string-unambiguousp
    (implies (string-unambiguousp string rulename rules)
             (equal (parse string rulename rules)
                    (insert (parse! string rulename rules) nil)))
    :enable string-unambiguousp))

(define-sk languagep (nats (rules rulelistp))
  :returns (yes/no booleanp)
  :parents (semantics)
  :short "Notion of language."
  :long
  "<p>
   The language defined by a list of rules consists of
   the sequences of natural numbers that form parsable strings.
   Note that the condition that
   the existentially quantified @('rulename') be defined by @('rules')
   would be superfluous,
   because if @('rulename') is not defined then no parse trees
   with only terminal leaves can originate from it.
   </p>"
  (exists (rulename)
          (and (nat-listp nats)
               (rulenamep rulename)
               (string-parsablep nats rulename rules))))
