; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../semantics")

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ambiguity
  :parents (operations)
  :short "Ambiguity (and unambiguity) in ABNF grammars."
  :long
  (xdoc::topstring-p
   "This part of the ABNF formalization is work in progress.
    More definitions and theorems should be added.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rules-ambiguousp ((rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule num-val-unambiguous
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule char-val-unambiguous
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled prose-val-ambiguous
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk element-unambiguousp ((element elementp) (rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule element-num-val-unambiguous
  :short "Numeric value elements are never ambiguous."
  :long
  (xdoc::topstring-p
   "This is a simple consequnce of @(tsee num-val-unambiguous).")
  (implies (element-case element :num-val)
           (element-unambiguousp element rules))
  :enable (element-unambiguousp tree-match-element-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule element-char-val-unambiguous
  :short "Character value elements are never ambiguous."
  :long
  (xdoc::topstring
   "This is a simple consequnce of @(tsee char-val-unambiguous).")
  (implies (element-case element :char-val)
           (element-unambiguousp element rules))
  :enable (element-unambiguousp tree-match-element-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule element-prose-val-ambiguous
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk repetition-unambiguousp ((repetition repetitionp) (rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk concatenation-unambiguousp ((concatenation concatenationp)
                                       (rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk alternation-unambiguousp ((alternation alternationp)
                                     (rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk concatenation-alternation-disjointp ((concatenation concatenationp)
                                                (alternation alternationp)
                                                (rules rulelistp))
  :returns (yes/no booleanp)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule alternation-unambiguousp-of-cons-when-disjointp
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
