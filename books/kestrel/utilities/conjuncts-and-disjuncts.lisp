; Tools for manipulating conjunctions and disjunctions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See proof of correctness in conjuncts-and-disjuncts-proof.lisp.

;; TODO: Should we be able to get conjuncts from (NOT (IF X X Y)) which is "not (x or y)" ?

(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/wrap-all" :dir :system)
(include-book "kestrel/booleans/booland" :dir :system) ; do not remove, since this tool depends on this definition of booland
(include-book "kestrel/booleans/boolor" :dir :system) ; do not remove, since this tool depends on this definition of boolor
(include-book "kestrel/booleans/boolif" :dir :system) ; do not remove, since this tool depends on this definition of boolif
(include-book "myif") ; do not remove, since this tool depends on this definition of myif
(include-book "negate-term")
(local (include-book "pseudo-termp"))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "logic-termp"))
(local (include-book "arities-okp"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(local (in-theory (disable ;len-of-cdr-better member-of-cons ;CONSP-CDR
                   default-car))) ;for speed

;; A single conjunct of "false"
(defconst *false-conjunction* (list *nil*))

;; The empty conjunction is equivalent to true
(defconst *true-conjunction* nil)

;; The empty disjunction is equivalent to false
(defconst *false-disjunction* nil)

;; A single disjunct of "true"
(defconst *true-disjunction* (list *t*))

;; We expect each of x and y to be either 1) the false-conjunction, or 2) a list of non-constant terms.
(defund combine-conjuncts (x y)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (pseudo-term-listp y))))
  (if (or (equal *false-conjunction* x)
          (equal *false-conjunction* y))
      *false-conjunction*
    (union-equal x y)))

(defthm logic-term-listp-of-combine-conjuncts
  (implies (and (logic-term-listp x w)
                (logic-term-listp y w))
           (logic-term-listp (combine-conjuncts x y) w))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

;; We expect each of x and y to be either 1) the true-disjunction, or 2) a list of non-constant terms.
(defund combine-disjuncts (x y)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (pseudo-term-listp y))))
  (if (or (equal *true-disjunction* x)
          (equal *true-disjunction* y))
      *true-disjunction*
    (union-equal x y)))

(defthm logic-term-listp-of-combine-disjuncts
  (implies (and (logic-term-listp x w)
                (logic-term-listp y w))
           (logic-term-listp (combine-disjuncts x y) w))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))

;; (defthm pseudo-term-listp-of-union-equal
;;   (implies (and (pseudo-term-listp x)
;;                 (pseudo-term-listp y))
;;            (pseudo-term-listp (union-equal x y)))
;;   :hints (("Goal" :in-theory (enable union-equal))))

(defthm pseudo-term-listp-of-combine-conjuncts
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (combine-conjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

(defthm pseudo-term-listp-of-combine-disjuncts
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (combine-disjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))

(defthm true-listp-of-combine-conjuncts
  (implies (and ;(true-listp x)
                (true-listp y))
           (true-listp (combine-conjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

(defthm true-listp-of-combine-disjuncts
  (implies (and ;(true-listp x)
                (true-listp y))
           (true-listp (combine-disjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))

;todo: handle (equal x 'nil) like (not 'x)
;todo: handle (if/myif/boolif x 'nil 't) like (not 'x)

(defund negate-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (cons (negate-term term)
            (negate-terms (rest terms))))))

(defthm pseudo-term-listp-of-negate-terms
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-terms terms)))
  :hints (("Goal" :in-theory (enable negate-terms))))

(defthm logic-term-listp-of-negate-terms
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)) w))
           (logic-term-listp (negate-terms terms) w))
  :hints (("Goal" :in-theory (enable negate-terms))))

;(local (in-theory (enable pseudo-termp)))

;; also pushes not through branches of IFs
(defund negate-term2 (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (variablep term)
      `(not ,term)
    (let ((fn (ffn-symb term)))
      (if (eq 'quote fn)
          (if (unquote term)
              *nil*      ;non-nil constant becomes nil
            *t*)         ;nil becomes t
        (if (eq 'not fn) ;strip the not
            (farg1 term)
          (if (member-eq fn '(if myif))
              ;; push the not into the branchs of if/myif:
              `(,fn ,(farg1 term) ,(negate-term2 (farg2 term)) ,(negate-term2 (farg3 term)))
            ;; no special handling:
            `(not ,term)))))))

(defthm pseudo-term-listp-of-negate-term2
  (implies (pseudo-termp term)
           (pseudo-termp (negate-term2 term)))
  :hints (("Goal" :in-theory (enable negate-term2))))

(defthm logic-term-listp-of-negate-term2
  (implies (and (logic-termp term w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (myif . 3))
                             w))
           (logic-termp (negate-term2 term) w))
  :hints (("Goal" :in-theory (enable negate-term2))))

(defund negate-terms2 (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (cons (negate-term2 term)
            (negate-terms2 (rest terms))))))

(defthm logic-term-listp-of-negate-terms2
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (myif . 3))
                             w))
           (logic-term-listp (negate-terms2 terms) w))
  :hints (("Goal" :in-theory (enable negate-terms2))))

(defthm pseudo-term-listp-of-negate-terms2
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-terms2 terms)))
  :hints (("Goal" :in-theory (enable negate-terms2))))

;; Negate all the disjuncts, forming a conjunction of the results
(defund negate-disjuncts (disjuncts)
   (declare (xargs :guard (pseudo-term-listp disjuncts)))
   (if (equal disjuncts *true-disjunction*)
      *false-conjunction*
    (negate-terms2 disjuncts)))

(defthm pseudo-term-listp-of-negate-disjuncts
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-disjuncts terms)))
  :hints (("Goal" :in-theory (enable negate-disjuncts))))

(defthm logic-term-listp-of-negate-disjuncts
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (myif . 3))
                             w))
           (logic-term-listp (negate-disjuncts terms) w))
  :hints (("Goal" :in-theory (enable negate-disjuncts))))

;; Negate all the conjuncts, forming a disjunction of the results
(defund negate-conjuncts (conjuncts)
   (declare (xargs :guard (pseudo-term-listp conjuncts)))
  (if (equal conjuncts *false-conjunction*)
      *true-disjunction*
    (negate-terms2 conjuncts)))

(defthm pseudo-term-listp-of-negate-conjuncts
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (negate-conjuncts terms)))
  :hints (("Goal" :in-theory (enable negate-conjuncts))))

(defthm logic-term-listp-of-negate-conjuncts
  (implies (and (logic-term-listp terms w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (myif . 3))
                             w))
           (logic-term-listp (negate-conjuncts terms) w))
  :hints (("Goal" :in-theory (enable negate-conjuncts))))

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
         (if (eq 'booland fn)
             (combine-conjuncts (get-conjuncts-of-term (farg1 term))
                                (get-conjuncts-of-term (farg2 term)))
           (if (eq 'not fn) ;de morgan: (not (or ...)) = (and (not ..) .. (not ..))
               (negate-disjuncts (get-disjuncts-of-term (farg1 term)))
             (if (member-eq fn '(myif boolif if))
                 (if (equal *nil* (farg3 term)) ;; (myif <x> <y> nil) is the same as (and <x> <y>) ;;todo: handle (if x y x) as well?
                     (combine-conjuncts (get-conjuncts-of-term (farg1 term))
                                        (get-conjuncts-of-term (farg2 term)))
                   (if (equal *nil* (farg2 term)) ;; (myif x nil y) <=> (and (not x) y)
                       (combine-conjuncts (negate-disjuncts (get-disjuncts-of-term (farg1 term)))
                                          (get-conjuncts-of-term (farg3 term)))
                     (list term)))
               (list term))))))))

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
         (if (eq 'boolor fn)
             (combine-disjuncts (get-disjuncts-of-term (farg1 term))
                                (get-disjuncts-of-term (farg2 term)))
           (if (eq 'not fn) ;de morgan: (not (and ...)) = (or (not ..) .. (not ..))
               (negate-conjuncts (get-conjuncts-of-term (farg1 term)))
             (if (member-eq fn '(if myif boolif))
                 (if (equal *t* (farg2 term)) ; (if <x> t <y>) is the same as (or <x> <y>)
                     (combine-disjuncts (get-disjuncts-of-term (farg1 term))
                                        (get-disjuncts-of-term (farg3 term)))
                   (if (equal *t* (farg3 term)) ; (if x y t) <=> (or (not x) y)
                       (combine-disjuncts (negate-conjuncts (get-conjuncts-of-term (farg1 term)))
                                          (get-disjuncts-of-term (farg2 term)))
                     (if (equal (farg1 term) (farg2 term)) ; (if x x y) <=> (or x y)
                         (combine-disjuncts (get-disjuncts-of-term (farg1 term))
                                            (get-disjuncts-of-term (farg3 term)))
                       (list term))))
               (list term)))))))))

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
                                 (if . 3)
                                 (boolif . 3)
                                 (booland . 2)
                                 (boolor . 2)
                                 (myif . 3))
                               w))
             (logic-term-listp (get-conjuncts-of-term term) w))
    :flag get-conjuncts-of-term)
  (defthm logic-term-listp-of-get-disjuncts-of-term
    (implies (and (logic-termp term w)
                  (arities-okp '((not . 1)
                                 (if . 3)
                                 (boolif . 3)
                                 (booland . 2)
                                 (boolor . 2)
                                 (myif . 3))
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
