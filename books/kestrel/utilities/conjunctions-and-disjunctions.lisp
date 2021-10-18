; Tools for representing conjunctions and disjunctions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; A single conjunct of "false"
(defconst *false-conjunction* (list *nil*))

;; The empty conjunction is equivalent to true
(defconst *true-conjunction* nil)

;; The empty disjunction is equivalent to false
(defconst *false-disjunction* nil)

;; A single disjunct of "true"
(defconst *true-disjunction* (list *t*))

;; We expect each of x and y to be either 1) *false-conjunction*, or 2) a list of non-constant terms.
(defund combine-conjuncts (x y)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (pseudo-term-listp y))))
  (if (or (equal *false-conjunction* x)
          (equal *false-conjunction* y))
      *false-conjunction*
    (union-equal x y)))

(defthm pseudo-term-listp-of-combine-conjuncts
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (combine-conjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

(defthm logic-term-listp-of-combine-conjuncts
  (implies (and (logic-term-listp x w)
                (logic-term-listp y w))
           (logic-term-listp (combine-conjuncts x y) w))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

(defthm true-listp-of-combine-conjuncts
  (implies (true-listp y)
           (true-listp (combine-conjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-conjuncts))))

;; We expect each of x and y to be either 1) the *true-disjunction*, or 2) a list of non-constant terms.
(defund combine-disjuncts (x y)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (pseudo-term-listp y))))
  (if (or (equal *true-disjunction* x)
          (equal *true-disjunction* y))
      *true-disjunction*
    (union-equal x y)))

(defthm pseudo-term-listp-of-combine-disjuncts
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (combine-disjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))

(defthm logic-term-listp-of-combine-disjuncts
  (implies (and (logic-term-listp x w)
                (logic-term-listp y w))
           (logic-term-listp (combine-disjuncts x y) w))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))

(defthm true-listp-of-combine-disjuncts
  (implies (true-listp y)
           (true-listp (combine-disjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-disjuncts))))
