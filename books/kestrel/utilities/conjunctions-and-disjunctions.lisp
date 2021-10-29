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

(include-book "forms")
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

(defun strip-nots-from-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (call-of 'not term)
      (strip-nots-from-term (farg1 term))
    term))

;; A non-trivial logical term is a pseudo-term that is not a constant and not
;; a nest of NOTs applied to a constant.
(defun non-trivial-logical-termp (term)
  (declare (xargs :guard t))
  (and (pseudo-termp term)
       (not (quotep (strip-nots-from-term term)))))

(defund non-trivial-logical-term-listp  (terms)
  (declare (xargs :guard t))
  (if (atom terms)
      (null terms)
    (let ((term (first terms)))
      (and (non-trivial-logical-termp term)
           (non-trivial-logical-term-listp (rest terms))))))

(defthm non-trivial-logical-term-listp-forward-to-pseudo-term-listp
  (implies (non-trivial-logical-term-listp x)
           (pseudo-term-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable non-trivial-logical-term-listp))))

(defthm non-trivial-logical-term-listp-of-cons
  (equal (non-trivial-logical-term-listp (cons term terms))
         (and (non-trivial-logical-termp term)
              (non-trivial-logical-term-listp terms)))
  :hints (("Goal" :in-theory (enable non-trivial-logical-term-listp))))

(defund conjunct-listp (x)
  (declare (xargs :guard t))
  (or (equal x *false-conjunction*)
      (non-trivial-logical-term-listp x)))

(defthm conjunct-listp-forward-to-pseudo-term-listp
  (implies (conjunct-listp x)
           (pseudo-term-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable conjunct-listp))))

(defthm conjunct-listp-of-cons
  (equal (conjunct-listp (cons term terms))
         (or (and (equal term *nil*)
                  (null terms))
             (and (non-trivial-logical-termp term)
                  (non-trivial-logical-term-listp terms))))
  :hints (("Goal" :in-theory (enable conjunct-listp))))

(defund disjunct-listp (x)
  (declare (xargs :guard t))
  (or (equal x *true-disjunction*)
      (non-trivial-logical-term-listp x)))

(defthm disjunct-listp-forward-to-pseudo-term-listp
  (implies (disjunct-listp x)
           (pseudo-term-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable disjunct-listp))))

(defthm disjunct-listp-of-cons
  (equal (disjunct-listp (cons term terms))
         (or (and (equal term *t*)
                  (null terms))
             (and (non-trivial-logical-termp term)
                  (non-trivial-logical-term-listp terms))))
  :hints (("Goal" :in-theory (enable disjunct-listp))))

;; We expect each of x and y to be either 1) *false-conjunction*, or 2) a list of non-constant terms.
(defund combine-conjuncts (x y)
  (declare (xargs :guard (and (conjunct-listp x)
                              (conjunct-listp y))
                  :guard-hints (("Goal" :in-theory (enable conjunct-listp
                                                           non-trivial-logical-term-listp)))))
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

(defthm conjunct-listp-of-combine-conjuncts
  (implies (and (conjunct-listp x)
                (conjunct-listp y))
           (conjunct-listp (combine-conjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-conjuncts
                                     conjunct-listp
                                     non-trivial-logical-term-listp))))

;; We expect each of x and y to be either 1) the *true-disjunction*, or 2) a list of non-constant terms.
(defund combine-disjuncts (x y)
  (declare (xargs :guard (and (disjunct-listp x)
                              (disjunct-listp y))
                  :guard-hints (("Goal" :in-theory (enable disjunct-listp
                                                           non-trivial-logical-term-listp)))))
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

(defthm disjunct-listp-of-combine-disjuncts
  (implies (and (disjunct-listp x)
                (disjunct-listp y))
           (disjunct-listp (combine-disjuncts x y)))
  :hints (("Goal" :in-theory (enable combine-disjuncts
                                     disjunct-listp
                                     non-trivial-logical-term-listp))))
