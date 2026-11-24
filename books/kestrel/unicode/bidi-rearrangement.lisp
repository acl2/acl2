; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-reordering")

(include-book "kestrel/lists-light/perm" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two facts of arithmetic for the proofs of this book.

(defrulel fix-of-nfix
  (equal (fix (nfix x))
         (nfix x))
  :enable (fix nfix))

(defrulel nfix-of-+-of-nfix
  (implies (natp y)
           (equal (nfix (+ y (nfix x)))
                  (+ y (nfix x))))
  :enable (nfix natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-rearrangement
  :parents (bidirectional-algorithm)
  :short "The order of display is a rearrangement
          of the characters that are displayed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Bidirectional Algorithm changes the order
     of the characters and nothing else:
     each character that has a level is displayed exactly once,
     and nothing else is displayed.
     The characters without a level are those that rule X9 removes
     (see @(tsee bidi-class-removed-p)).")
   (xdoc::p
    "We state this with the relation @('perm')
     of the book @('kestrel/lists-light/perm'),
     which holds of two lists when one is a permutation of the other:
     the order of display, which is a list of positions,
     is a permutation of the list of the positions
     of the characters that have a level
     (see @(tsee bidi-positions-with-level)),
     and that list has no position twice.
     This holds whatever the levels are:
     it is a property of rule L2 alone [UAX #9, rule L2]."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-positions-with-level ((levels bidi-level-option-listp)
                                   (position natp))
  :returns (positions nat-listp)
  :short "The positions of the characters that have a level,
          in the order of the text."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the levels of the characters
     from a position on, and the second is that position: 0 for a whole text.
     A character without a level, which rule X9 removed, is left out.
     This is the order in which the characters would be displayed
     if nothing were reordered."))
  (b* (((when (endp levels)) nil)
       (position (lnfix position))
       ((unless (acl2::maybe-natp-fix (car levels)))
        (bidi-positions-with-level (cdr levels) (+ 1 position))))
    (cons position
          (bidi-positions-with-level (cdr levels) (+ 1 position))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defsection bidi-positions-with-level-theorems
  :short "Theorems about @(tsee bidi-positions-with-level)."

  (local (in-theory (enable bidi-positions-with-level)))

  (defrule bidi-positions-with-level-when-not-consp
    (implies (not (consp levels))
             (equal (bidi-positions-with-level levels position)
                    nil)))

  (defruled bidi-display-item-list-positions-of-bidi-display-items
    (equal (bidi-display-item-list-positions
            (bidi-display-items levels position))
           (bidi-positions-with-level levels position))
    :induct t
    :enable (bidi-display-items
             bidi-display-item-list-positions))

  (defrule bidi-positions-with-level-of-append
    (equal (bidi-positions-with-level (append levels1 levels2) position)
           (append (bidi-positions-with-level levels1 position)
                   (bidi-positions-with-level levels2
                                              (+ (nfix position)
                                                 (len levels1)))))
    :induct t
    :enable (append len))

  (defrule nat-list-add-of-bidi-positions-with-level
    (equal (nat-list-add (bidi-positions-with-level levels position) offset)
           (bidi-positions-with-level levels
                                      (+ (nfix position) (nfix offset))))
    :induct t
    :enable nat-list-add)

  (defruled not-member-equal-of-bidi-positions-with-level-when-below
    (implies (and (natp a)
                  (< a (nfix position)))
             (not (member-equal a
                                (bidi-positions-with-level levels position))))
    :induct t
    :enable (member-equal nfix natp))

  (defrule no-duplicatesp-equal-of-bidi-positions-with-level
    (no-duplicatesp-equal (bidi-positions-with-level levels position))
    :induct t
    :enable (no-duplicatesp-equal
             nfix
             natp
             not-member-equal-of-bidi-positions-with-level-when-below)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rearrangement-theorems
  :short "The order of display is a permutation of the positions
          of the characters that have a level."

  ;; The positions of a list of characters to display, each plus an offset.

  (local
   (define shifted-positions ((items bidi-display-item-listp) (offset natp))
     :returns (positions nat-listp)
     (nat-list-add (bidi-display-item-list-positions items) offset)
     :hooks nil
     ///
     (defrule shifted-positions-when-not-consp
       (implies (not (consp items))
                (equal (shifted-positions items offset) nil))
       :enable (bidi-display-item-list-positions nat-list-add))
     (defrule shifted-positions-of-cons
       (equal (shifted-positions (cons item items) offset)
              (cons (+ (bidi-display-item->position item) (nfix offset))
                    (shifted-positions items offset)))
       :enable (bidi-display-item-list-positions nat-list-add nfix))
     (defrule shifted-positions-of-append
       (equal (shifted-positions (append items1 items2) offset)
              (append (shifted-positions items1 offset)
                      (shifted-positions items2 offset)))
       :induct (len items1)
       :enable (append len bidi-display-item-list-positions nat-list-add)
       :disable shifted-positions-of-cons)
     (defrule shifted-positions-of-bidi-display-item-list-fix
       (equal (shifted-positions (bidi-display-item-list-fix items) offset)
              (shifted-positions items offset)))))

  (defrulel nat-list-add-of-zero
    (equal (nat-list-add list 0)
           (nat-list-fix list))
    :induct t
    :enable (nat-list-add nat-list-fix nfix fix))

  (defrulel perm-of-cons-and-cons-same
    (equal (acl2::perm (cons a x) (cons a y))
           (acl2::perm x y))
    :enable remove1-equal)

  (defrulel shifted-positions-of-bidi-reverse-runs
    (acl2::perm (shifted-positions (bidi-reverse-runs items level run)
                                   offset)
                (append (shifted-positions run offset)
                        (shifted-positions items offset)))
    :induct (bidi-reverse-runs items level run)
    :enable bidi-reverse-runs
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2
              acl2::perm-of-append))

  (defrulel shifted-positions-of-bidi-reorder-items
    (acl2::perm (shifted-positions (bidi-reorder-items items level lowest)
                                   offset)
                (shifted-positions items offset))
    :induct (bidi-reorder-items items level lowest)
    :enable bidi-reorder-items
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2
              acl2::perm-of-append))

  (defrule perm-of-positions-of-bidi-reorder-items
    (acl2::perm (bidi-display-item-list-positions
                 (bidi-reorder-items items level lowest))
                (bidi-display-item-list-positions items))
    :use (:instance shifted-positions-of-bidi-reorder-items (offset 0))
    :enable shifted-positions
    :disable shifted-positions-of-bidi-reorder-items)

  (defruledl shifted-positions-of-bidi-display-items
    (equal (shifted-positions (bidi-display-items levels 0) offset)
           (bidi-positions-with-level levels offset))
    :enable (shifted-positions
             bidi-display-item-list-positions-of-bidi-display-items))

  (defruledl nat-list-add-of-bidi-display-item-list-positions
    (equal (nat-list-add (bidi-display-item-list-positions items) offset)
           (shifted-positions items offset))
    :enable shifted-positions)

  (defrulel nat-list-add-of-bidi-order-of-levels
    (acl2::perm (nat-list-add (bidi-order-of-levels levels) offset)
                (bidi-positions-with-level levels offset))
    :enable (bidi-order-of-levels
             nat-list-add-of-bidi-display-item-list-positions
             shifted-positions-of-bidi-display-items))

  (defrule perm-of-bidi-order-of-levels
    (acl2::perm (bidi-order-of-levels levels)
                (bidi-positions-with-level levels 0))
    :use (:instance nat-list-add-of-bidi-order-of-levels (offset 0))
    :disable nat-list-add-of-bidi-order-of-levels)

  (defrule perm-of-bidi-paragraph-order
    (acl2::perm (bidi-paragraph-order chars paragraph-level)
                (bidi-positions-with-level
                 (bidi-paragraph-levels chars paragraph-level)
                 0))
    :enable bidi-paragraph-order)

  (defrulel nfix-of-bidi-paragraph-length
    (equal (nfix (bidi-paragraph-length chars))
           (bidi-paragraph-length chars))
    :enable nfix)

  (defrulel perm-of-bidi-order-of-chars
    (acl2::perm (bidi-order-of-chars chars direction offset)
                (bidi-positions-with-level
                 (bidi-levels-of-chars chars direction)
                 offset))
    :induct (bidi-order-of-chars chars direction offset)
    :enable (bidi-order-of-chars
             bidi-paragraph-order)
    :expand ((bidi-levels-of-chars chars direction))
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2
              acl2::perm-of-append))

  (defrule perm-of-bidi-display-order
    (acl2::perm (bidi-display-order cps direction ver)
                (bidi-positions-with-level (bidi-levels cps direction ver)
                                           0))
    :enable (bidi-display-order bidi-levels)))
