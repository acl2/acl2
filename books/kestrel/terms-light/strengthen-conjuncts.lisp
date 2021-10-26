; A tool to strengthen conjuncts
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This is similar to something ACL2 does when it simplifies guard (and perhaps
;; measure) conjectures.

(include-book "make-if-term")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "term-is-disjunctionp")
(include-book "term-is-conjunctionp")
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)

;;changes the evaluator
(defthm if-and-not-eval-when-term-is-disjunctionp
  (implies (term-is-disjunctionp disj)
           (iff (if-and-not-eval disj a)
                (or (if-and-not-eval (farg1 disj) a)
                    (if-and-not-eval (farg3 disj) a))))
  :hints (("Goal" :use (:functional-instance
                        if-eval-when-term-is-disjunctionp
                        (if-eval if-and-not-eval)
                        (if-eval-list if-and-not-eval-list)))))

;;changes the evaluator
(defthm if-and-not-eval-when-term-is-conjunctionp
  (implies (term-is-conjunctionp conj)
           (iff (if-and-not-eval conj a)
                (and (if-and-not-eval (farg1 conj) a)
                     (if-and-not-eval (farg2 conj) a))))
  :hints (("Goal" :use (:functional-instance
                        if-eval-when-term-is-conjunctionp
                        (if-eval if-and-not-eval)
                        (if-eval-list if-and-not-eval-list)))))


(defund complementary-termsp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (or (and (call-of 'not x)
           (equal (farg1 x) y))
      (and (call-of 'not y)
           (equal (farg1 y) x))))

(defthm not-complementary-termsp-self
  (not (complementary-termsp x x))
  :hints (("Goal" :in-theory (enable complementary-termsp))))

(defthm complementary-termsp-symmetric
  (equal (complementary-termsp x y)
         (complementary-termsp y x))
  :hints (("Goal" :in-theory (enable complementary-termsp))))

(defthm if-and-not-eval-when-complementary-termsp
  (implies (complementary-termsp x free)
           (iff (if-and-not-eval x a)
                (not (if-and-not-eval free a))))
  :hints (("Goal" :in-theory (enable complementary-termsp))))

;; Checks that X and Y are identical except for the negation of a single disjunct.
(defun complementary-disjunctionsp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (if (or (not (term-is-disjunctionp x))
          (not (term-is-disjunctionp y)))
      (complementary-termsp x y)
    (or (and (complementary-termsp (farg1 x) (farg1 y))
             (equal (farg3 x) (farg3 y)))
        (and (equal (farg1 x) (farg1 y))
             (complementary-disjunctionsp (farg3 x) (farg3 y))))))

;; (thm
;;  (IMPLIES (COMPLEMENTARY-TERMSP X y)
;;           (COMPLEMENTARY-DISJUNCTIONSP X y)))

(defthm complementary-disjunctionsp-symmetric
  (equal (complementary-disjunctionsp x y)
         (complementary-disjunctionsp y x)))

;; Can combine, e.g., the two conjuncts (or a (not b) c) with (or a b c) to create the new, stronger conjunct (or a b).
;; Assumes that X and Y are complementary disjunctions
;; Returns (mv changep new-conjunct) where if changep is true, then new-conjunct is equivalent to the conjunction of x and y.
(defund conjoin-complementary-disjunctions (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (complementary-disjunctionsp x y))
                  :guard-hints (("Goal" :expand (complementary-disjunctionsp x y)))))
  (if (or (not (term-is-disjunctionp x))
          (not (term-is-disjunctionp y)))
      ;; x and y must be complementary
      *nil*
    ;; x and y must both be disjunctions:
    (if (equal (farg1 x) (farg1 y)) ; (or (not x) ...) and (or x ...)
        `(if ,(farg1 x)
             't
           ,(conjoin-complementary-disjunctions (farg3 x) (farg3 y)))
      ;; we've found the complementary disjuncts:
      (farg3 x))))

(defthm if-and-not-eval-of-conjoin-complementary-disjunctions
  (implies (complementary-disjunctionsp x y)
           (iff (if-and-not-eval (conjoin-complementary-disjunctions x y) a)
                (and (if-and-not-eval x a)
                     (if-and-not-eval y a))))
  :hints (("Goal" :expand ((complementary-termsp x y)
                           (conjoin-complementary-disjunctions x y)))))

;; Find a conjunct of C that is complementary to X, or return nil.
;; Generally, X and the conjuncts of C are all disjunctions.
(defun find-complementary-conjunct (x c)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp c))))
  (if (not (term-is-conjunctionp c))
      (if (complementary-disjunctionsp x c)
          c
        nil)
    ;; c is a conjunction, so check the first conjunct:
    (let ((c1 (farg1 c)))
      (if (complementary-disjunctionsp x c1)
          c1
        (find-complementary-conjunct x (farg2 c))))))

(defthm pseudo-termp-of-find-complementary-conjunct
  (implies (pseudo-termp c)
           (pseudo-termp (find-complementary-conjunct x c))))

(defthm complementary-disjunctionsp-of-find-complementary-conjunct
  (implies (find-complementary-conjunct x c)
           (complementary-disjunctionsp x
                                        (find-complementary-conjunct x c))))

(defthm complementary-disjunctionsp-of-find-complementary-conjunct-alt
  (implies (find-complementary-conjunct x c)
           (complementary-disjunctionsp (find-complementary-conjunct x c)
                                        x)))

(defthm not-if-and-not-eval-when-find-complementary-conjunct-and-false
  (implies (and (find-complementary-conjunct x c)
                (not (if-and-not-eval (find-complementary-conjunct x c)
                                      a)))
           (not (if-and-not-eval c a))))

;; Remove the first occurence of X as a conjunct of C.
(defun remove-conjunct (x c)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp c))
                  :verify-guards nil ; done below
                  ))
  (if (not (term-is-conjunctionp c))
      (if (equal x c)
          *t* ; the conjunction of nothing is true
        c     ; todo: error?
        )
    ;; c is a conjunction, so check the first conjunct:
    (let ((c1 (farg1 c)))
      (if (equal c1 x)
          (farg2 c)
        (make-if-term-gen c1 (remove-conjunct x (farg2 c)) *nil*)))))

(defthm pseudo-termp-of-remove-conjunct
  (implies (pseudo-termp c)
           (pseudo-termp (remove-conjunct x c)))
  :hints (("Goal" :in-theory (enable remove-conjunct))))

(verify-guards remove-conjunct)

;; Removing a true conjunct has no effect
(defthm if-and-not-eval-of-remove-conjunct-when-true
  (implies (if-and-not-eval x a)
           (iff (if-and-not-eval (remove-conjunct x c) a)
                (if-and-not-eval c a)))
  :hints (("Goal" :in-theory (enable remove-conjunct))))

;; In general, the conjuncts of C are treated as disjunctions.
;; TODO: Use better terminology than "complementary" conjuncts -- maybe unifiable?
(defun combine-complementary-conjuncts (c)
  (declare (xargs :guard (pseudo-termp c)
                  :verify-guards nil ;done below
                  ))
  (if (not (term-is-conjunctionp c))
      c
    (let* ((c1 (farg1 c)) ; c is (and c1 ...)
           (maybe-complementary-conjunct (find-complementary-conjunct c1 (farg2 c))))
      (if (not maybe-complementary-conjunct)
          `(if ,c1 ,(combine-complementary-conjuncts (farg2 c)) 'nil)
        (progn$ (cw "Found complementary conjunct: ~x0~%" maybe-complementary-conjunct)
                `(if ,(conjoin-complementary-disjunctions maybe-complementary-conjunct c1) ; stronger than maybe-complementary-conjunct or c1 alone
                     ,(remove-conjunct maybe-complementary-conjunct (farg2 c))
                   'nil))))))

(verify-guards combine-complementary-conjuncts)

;; Correctness theorem for combine-complementary-conjuncts.
(defthm if-and-not-eval-of-combine-complementary-conjuncts
  (iff (if-and-not-eval (combine-complementary-conjuncts c) a)
       (if-and-not-eval c a)))
