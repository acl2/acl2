; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "../language/abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ renamings
  :parents (transformations)
  :short "Renamings of variables and functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee renaming-variables) and @(tsee renaming-functions).")
   (xdoc::p
    "The renaming information is captured as
     a list of pairs of identifiers
     @('((a1 . b1) (a2 . b2) ...)')
     such that @('a1'), @('a2'), etc. are all distinct
     and that @('b1'), @('b2'), etc. are all distinct.
     Technically, it is an alist with unique keys and unique values,
     but we treat is as a list of pairs,
     i.e. we do not use alist operations on them;
     it is an injective alist, so its ``direction'' is unimportant.
     Each pair @('(ai . bi)') describes a renaming between
     the variable @('ai') in the old code
     and the variable @('bi') in the new code.
     The keys are the variables or functions in scope in the old code;
     the values are the variables or functions in scope in the new code.
     These facts hold because of the way the list is threaded through,
     in the ACL2 code that defines the renaming relation.
     These facts are formally explicated and proved as part of the
     proof of static safety preservation of variable and function renaming.")
   (xdoc::p
    "The relative ordering of the pairs in the renaming list is irrelevant.
     Because of the way the list is constructed,
     the pairs happen to be ordered in reverse chronological order,
     i.e. the @(tsee car) is the most recent.
     From a point of view,
     it may be better to use a set of pairs (which is also an omap),
     to make it more explicit that the order does not matter.
     However, with lists we can more readily use
     functions like @(tsee no-duplicatesp-equal) and theorems about them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod renaming
  :short "Fixtype of renamings."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are alists from identifiers to identifiers
     that have unique keys and unique values,
     which we treat as lists of pairs rather than as alist as such
     (see discussion in @(see renaming-variables)).
     We wrap the alist into a one-component product type
     and we add constraints for key and value uniqueness.")
   (xdoc::p
    "We use this to capture variable renamings,
     but it can be also used for function renamings.
     We will put this into a more general place
     and also use this for function renamings."))
  ((list identifier-identifier-alist
         :reqfix (if (and (no-duplicatesp-equal (strip-cars list))
                          (no-duplicatesp-equal (strip-cdrs list)))
                     list
                   nil)))
  :require (and (no-duplicatesp-equal (strip-cars list))
                (no-duplicatesp-equal (strip-cdrs list)))
  :pred renamingp
  ///

  (defrule alistp-of-renaming->list
    (alistp (renaming->list ren))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult renaming-result
  :short "Fixtype of errors and renamings."
  :ok renaming
  :pred renaming-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled renaming-pair-equality
  :short "Theorem about pair equality in renamings."
  :long
  (xdoc::topstring
   (xdoc::p
    "Two pairs in a renaming are equal if and only if
     their @(tsee car)s or their @(tsee cdr)s are equal.
     This is because there cannot be two distinct pairs
     with the same @(tsee car) or @(tsee cdr)."))
  (implies (and (member-equal pair1 (renaming->list ren))
                (member-equal pair2 (renaming->list ren)))
           (equal (equal pair1 pair2)
                  (or (equal (car pair1)
                             (car pair2))
                      (equal (cdr pair1)
                             (cdr pair2)))))
  :use (:instance lemma (list (renaming->list ren)))
  :prep-lemmas
  ((defrule lemma
     (implies (and (identifier-identifier-alistp list)
                   (no-duplicatesp-equal (strip-cars list))
                   (no-duplicatesp-equal (strip-cdrs list))
                   (member-equal pair1 list)
                   (member-equal pair2 list))
              (equal (equal pair1 pair2)
                     (or (equal (car pair1)
                                (car pair2))
                         (equal (cdr pair1)
                                (cdr pair2)))))
     :prep-lemmas
     ((defrule lemma-lemma
        (implies (and (identifier-identifier-alistp list)
                      (member-equal pair list))
                 (and (member-equal (car pair) (strip-cars list))
                      (member-equal (cdr pair) (strip-cdrs list)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define renaming-old ((ren renamingp))
  :short "Set of old variables in a renaming."
  :returns (vars identifier-setp)
  (mergesort (strip-cars (renaming->list ren)))
  :hooks (:fix)
  ///

  (defruled old-var-in-renaming-old-when-in-renaming
    (implies (member-equal (cons old-var new-var)
                           (renaming->list ren))
             (set::in old-var (renaming-old ren)))
    :rule-classes :forward-chaining
    :induct (len ren)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define renaming-new ((ren renamingp))
  :short "Set of new variables in a renaming."
  :returns (vars identifier-setp)
  (mergesort (strip-cdrs (renaming->list ren)))
  :hooks (:fix)
  ///

  (defruled new-var-in-renaming-new-when-in-renaming
    (implies (member-equal (cons old-var new-var)
                           (renaming->list ren))
             (set::in new-var (renaming-new ren)))
    :rule-classes :forward-chaining
    :induct (len ren)))
