; Tools for manipulating conjunctions and disjunctions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See proof of correctness in conjuncts-and-disjuncts-proof.lisp.

;; TODO: Should we be able to get conjuncts from (NOT (IF X X Y)) which is "not (x or y)" ?

(include-book "forms")
(include-book "conjunctions-and-disjunctions")
(include-book "tools/flag" :dir :system)
(include-book "kestrel/terms-light/negate-terms" :dir :system)
(local (include-book "pseudo-termp"))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "arities-okp"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable ;len-of-cdr-better member-of-cons ;CONSP-CDR
                   default-car))) ;for speed

(defthm non-trivial-logical-term-listp-of-negate-terms
  (implies (non-trivial-logical-term-listp terms)
           (non-trivial-logical-term-listp (negate-terms terms)))
  :hints (("Goal" :in-theory (enable negate-terms negate-term))))


;todo: handle (equal x 'nil) like (not 'x)
;todo: handle (if/myif/boolif x 'nil 't) like (not 'x)

;; Negate all the disjuncts, forming a conjunction of the results
(defund negate-disjunct-list (disjuncts)
  (declare (xargs :guard (disjunct-listp disjuncts)))
  (if (equal disjuncts *true-disjunction*)
      *false-conjunction*
    (negate-terms disjuncts)))

(defthm pseudo-term-listp-of-negate-disjunct-list
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-disjunct-list terms)))
  :hints (("Goal" :in-theory (enable negate-disjunct-list))))

(defthm logic-term-listp-of-negate-disjunct-list
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)
                               (if . 3))
                             w))
           (logic-term-listp (negate-disjunct-list terms) w))
  :hints (("Goal" :in-theory (enable negate-disjunct-list))))

(defthm conjunct-listp-of-negate-disjunct-list
  (implies (disjunct-listp disjuncts)
           (conjunct-listp (negate-disjunct-list disjuncts)))
  :hints (("Goal" :in-theory (enable negate-disjunct-list disjunct-listp conjunct-listp))))

;; Negate all the conjuncts, forming a disjunction of the results
(defund negate-conjunct-list (conjuncts)
   (declare (xargs :guard (conjunct-listp conjuncts)))
  (if (equal conjuncts *false-conjunction*)
      *true-disjunction*
    ;; todo: just call negate-terms?:
    (negate-terms conjuncts)))

(defthm disjunct-listp-of-negate-conjunct-list
  (implies (conjunct-listp conjuncts)
           (disjunct-listp (negate-conjunct-list conjuncts)))
  :hints (("Goal" :in-theory (enable negate-conjunct-list disjunct-listp conjunct-listp))))

(defthm pseudo-term-listp-of-negate-conjunct-list
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-conjunct-list terms)))
  :hints (("Goal" :in-theory (enable negate-conjunct-list))))

(defthm logic-term-listp-of-negate-conjunct-list
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)
                               (if . 3))
                             w))
           (logic-term-listp (negate-conjunct-list terms) w))
  :hints (("Goal" :in-theory (enable negate-conjunct-list))))

;TODO: replace various more specialized routines to get conjuncts (e.g., for if nests) with these?
;TODO: Compare to the version for DAGs
(mutual-recursion
 ;; Returns a list of conjuncts whose conjunction is equivalent (using IFF) to TERM.
 (defund get-conjuncts-of-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (not (consp term)) ;term is a variable
       (list term)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           (if (unquote term)
               ;; a non-nil constant gets dropped
               *true-conjunction*
             ;; a nil constant makes the whole thing nil
             *false-conjunction*)
         ;; function call:
         (if (eq 'not fn) ;de morgan: (not (or ...)) = (and (not ..) .. (not ..))
             (negate-disjunct-list (get-disjuncts-of-term (farg1 term)))
           (if (eq fn 'if)
               (if (equal *nil* (farg3 term)) ;; (if <x> <y> nil) is the same as (and <x> <y>) ;;todo: handle (if x y x) as well?
                   (combine-conjuncts (get-conjuncts-of-term (farg1 term))
                                      (get-conjuncts-of-term (farg2 term)))
                 (if (equal *nil* (farg2 term)) ;; (if x nil y) <=> (and (not x) y)
                     (combine-conjuncts (negate-disjunct-list (get-disjuncts-of-term (farg1 term)))
                                        (get-conjuncts-of-term (farg3 term)))
                   (list term)))
             (list term)))))))

 ;; Returns a list of disjuncts whose disjunction is equivalent (using IFF) to TERM.
 (defund get-disjuncts-of-term (term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (not (consp term)) ;term is a variable
       (list term)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           (if (unquote term)
               ;; a non-nil constant makes the whole thing true
               *true-disjunction*
             ;; a nil constant gets dropped
             *false-disjunction*)
         ;; function call:
         (if (eq 'not fn) ;de morgan: (not (and ...)) = (or (not ..) .. (not ..))
             (negate-conjunct-list (get-conjuncts-of-term (farg1 term)))
           (if (eq fn 'if)
               (if (or (equal *t* (farg2 term)) ; (if <x> t <y>) is the same as (or <x> <y>)
                       (equal (farg1 term) (farg2 term)) ; (if <x> <x> <y>) is the same as (or <x> <y>)
                       )
                   (combine-disjuncts (get-disjuncts-of-term (farg1 term))
                                      (get-disjuncts-of-term (farg3 term)))
                 (if (equal *t* (farg3 term)) ; (if x y t) <=> (or (not x) y)
                     (combine-disjuncts (negate-conjunct-list (get-conjuncts-of-term (farg1 term)))
                                        (get-disjuncts-of-term (farg2 term)))
                   (list term)))
             (list term))))))))

(make-flag get-conjuncts-of-term)

(defthm-flag-get-conjuncts-of-term
  (defthm pseudo-term-listp-of-get-conjuncts-of-term
    (implies (pseudo-termp term)
             (pseudo-term-listp (get-conjuncts-of-term term)))
    :flag get-conjuncts-of-term)
  (defthm pseudo-term-listp-of-get-disjuncts-of-term
    (implies (pseudo-termp term)
             (pseudo-term-listp (get-disjuncts-of-term term)))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term get-conjuncts-of-term))))

(defthm-flag-get-conjuncts-of-term
  (defthm conjunct-listp-of-get-conjuncts-of-term
    (implies (pseudo-termp term)
             (conjunct-listp (get-conjuncts-of-term term)))
    :flag get-conjuncts-of-term)
  (defthm disjunct-listp-of-get-disjuncts-of-term
    (implies (pseudo-termp term)
             (disjunct-listp (get-disjuncts-of-term term)))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term
                                     get-conjuncts-of-term))))

(defthm-flag-get-conjuncts-of-term
  (defthm true-listp-of-get-conjuncts-of-term
    (true-listp (get-conjuncts-of-term term))
    :flag get-conjuncts-of-term)
  (defthm true-listp-of-get-disjuncts-of-term
    (true-listp (get-disjuncts-of-term term))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term get-conjuncts-of-term))))

(verify-guards get-conjuncts-of-term)

(defthm-flag-get-conjuncts-of-term
  (defthm logic-term-listp-of-get-conjuncts-of-term
    (implies (and (logic-termp term w)
                  (arities-okp '((not . 1)
                                 (if . 3))
                               w))
             (logic-term-listp (get-conjuncts-of-term term) w))
    :flag get-conjuncts-of-term)
  (defthm logic-term-listp-of-get-disjuncts-of-term
    (implies (and (logic-termp term w)
                  (arities-okp '((not . 1)
                                 (if . 3))
                               w))
             (logic-term-listp (get-disjuncts-of-term term) w))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term get-conjuncts-of-term))))

(defun get-conjuncts-of-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (union-equal (get-conjuncts-of-term (first terms))
                 (get-conjuncts-of-terms (rest terms)))))
