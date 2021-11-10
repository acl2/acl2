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
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;; prove from if-eval-of-make-if-term-gen?
(defthm if-and-not-eval-of-make-if-term-gen
  (iff (if-and-not-eval (make-if-term-gen test then else) a)
       (if (if-and-not-eval test a)
           (if-and-not-eval then a)
         (if-and-not-eval else a)))
  :hints (("Goal" :in-theory (enable make-if-term-gen))))


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

;; Checks whether one term is the negation of the other
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
(defun combinable-disjunctionsp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (if (or (not (term-is-disjunctionp x))
          (not (term-is-disjunctionp y)))
      (complementary-termsp x y)
    (or (and (complementary-termsp (farg1 x) (farg1 y))
             (equal (farg3 x) (farg3 y)))
        (and (equal (farg1 x) (farg1 y))
             (combinable-disjunctionsp (farg3 x) (farg3 y))))))

;; (thm
;;  (IMPLIES (COMPLEMENTARY-TERMSP X y)
;;           (COMBINABLE-DISJUNCTIONSP X y)))

(defthm combinable-disjunctionsp-symmetric
  (equal (combinable-disjunctionsp x y)
         (combinable-disjunctionsp y x)))

;; Can combine, e.g., the two conjuncts (or a (not b) c) with (or a b c) to create the new, stronger conjunct (or a b).
;; Assumes that X and Y are combinable disjunctions
;; Returns (mv changep new-conjunct) where if changep is true, then new-conjunct is equivalent to the conjunction of x and y.
(defund conjoin-combinable-disjunctions (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (combinable-disjunctionsp x y))
                  :guard-hints (("Goal" :expand (combinable-disjunctionsp x y)))))
  (if (or (not (term-is-disjunctionp x))
          (not (term-is-disjunctionp y)))
      ;; x and y must be combinable
      *nil*
    ;; x and y must both be disjunctions:
    (if (equal (farg1 x) (farg1 y)) ; (or (not x) ...) and (or x ...)
        `(if ,(farg1 x)
             't
           ,(conjoin-combinable-disjunctions (farg3 x) (farg3 y)))
      ;; we've found the combinable disjuncts:
      (farg3 x))))

(defthm pseudo-termp-of-conjoin-combinable-disjunctions
  (implies (and (pseudo-termp x)
                (pseudo-termp y)
                (combinable-disjunctionsp x y))
           (pseudo-termp (conjoin-combinable-disjunctions x y)))
  :hints (("Goal" :in-theory (enable conjoin-combinable-disjunctions))))

(defthm if-and-not-eval-of-conjoin-combinable-disjunctions
  (implies (combinable-disjunctionsp x y)
           (iff (if-and-not-eval (conjoin-combinable-disjunctions x y) a)
                (and (if-and-not-eval x a)
                     (if-and-not-eval y a))))
  :hints (("Goal" :expand ((complementary-termsp x y)
                           (conjoin-combinable-disjunctions x y)))))

;; Find a conjunct of C that is combinable with X, or return nil.
;; Generally, X and the conjuncts of C are all disjunctions.
(defund find-combinable-conjunct (x c)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp c))))
  (if (not (term-is-conjunctionp c))
      (if (combinable-disjunctionsp x c)
          c
        nil)
    ;; c is a conjunction, so check the first conjunct:
    (let ((c1 (farg1 c)))
      (if (combinable-disjunctionsp x c1)
          c1
        (find-combinable-conjunct x (farg2 c))))))

(defthm pseudo-termp-of-find-combinable-conjunct
  (implies (pseudo-termp c)
           (pseudo-termp (find-combinable-conjunct x c)))
  :hints (("Goal" :in-theory (enable find-combinable-conjunct))))

(defthm combinable-disjunctionsp-of-find-combinable-conjunct
  (implies (find-combinable-conjunct x c)
           (combinable-disjunctionsp x
                                     (find-combinable-conjunct x c)))
  :hints (("Goal" :in-theory (enable find-combinable-conjunct))))

(defthm combinable-disjunctionsp-of-find-combinable-conjunct-alt
  (implies (find-combinable-conjunct x c)
           (combinable-disjunctionsp (find-combinable-conjunct x c)
                                     x))
  :hints (("Goal" :in-theory (enable find-combinable-conjunct))))

(defthm not-if-and-not-eval-when-find-combinable-conjunct-and-false
  (implies (and (find-combinable-conjunct x c)
                (not (if-and-not-eval (find-combinable-conjunct x c)
                                      a)))
           (not (if-and-not-eval c a)))
  :hints (("Goal" :in-theory (enable find-combinable-conjunct))))

;; Remove the first occurence of X as a conjunct of C.
(defund remove-conjunct (x c)
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

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defthm <=-of-acl2-count-of-remove-conjunct
  (implies (not (equal *t* (remove-conjunct x c)))
           (<= (acl2-count (remove-conjunct x c))
               (acl2-count c)))
  :rule-classes :linear
  :hints (("Goal" :expand ((remove-conjunct x c)
                           (acl2-count (cdr c))
                           (acl2-count (cddr c))
                           (acl2-count (cdddr c)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable remove-conjunct make-if-term-gen term-is-conjunctionp))))

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

(defthm not-if-and-not-eval-when-not-if-and-not-eval-of-remove-conjunct-when-true
  (implies (not (if-and-not-eval (remove-conjunct x c) a))
           (not (if-and-not-eval c a)))
  :hints (("Goal" :in-theory (enable remove-conjunct))))

(defthm if-and-not-eval-when-equal-of-t-and-remove-conjunct
  (implies (and (equal ''t (remove-conjunct x c))
                (if-and-not-eval x a))
           (if-and-not-eval c a))
  :hints (("Goal" :in-theory (enable remove-conjunct make-if-term-gen))))

;; Can combine two weaker conjuncts into a single stronger conjunct.
;; Makes a single pass through C.
;; In general, the conjuncts of C are treated as disjunctions.
(defund strengthen-conjuncts-aux (c)
  (declare (xargs :guard (pseudo-termp c)
                  :verify-guards nil ;done below
                  :ruler-extenders :all))
  (if (not (term-is-conjunctionp c))
      c
    (let* ((c1 (farg1 c)) ; c is (and c1 ...)
           (maybe-combinable-conjunct (find-combinable-conjunct c1 (farg2 c))))
      (if (not maybe-combinable-conjunct)
          ;; Keep c1 and keep going:
          `(if ,c1 ,(strengthen-conjuncts-aux (farg2 c)) 'nil)
        (progn$ ; (cw "Found combinable conjunct: ~x0~%" maybe-combinable-conjunct)
         (let ((reduced-arg2 (remove-conjunct maybe-combinable-conjunct (farg2 c)))
               ;; stronger than maybe-combinable-conjunct or c1 alone:
               (stronger-c1 (conjoin-combinable-disjunctions maybe-combinable-conjunct c1)))
           (if (equal *t* reduced-arg2) ; it was the only conjunct
               stronger-c1
             (let ((reduced-arg2 (strengthen-conjuncts-aux reduced-arg2)))
               (make-if-term-gen stronger-c1
                                 reduced-arg2
                                 *nil*)))))))))

(defthm pseudo-termp-of-strengthen-conjuncts-aux
  (implies (pseudo-termp c)
           (pseudo-termp (strengthen-conjuncts-aux c)))
  :hints (("Goal" :in-theory (enable strengthen-conjuncts-aux))))

(verify-guards strengthen-conjuncts-aux)

;; Correctness theorem for strengthen-conjuncts-aux.
(defthm if-and-not-eval-of-strengthen-conjuncts-aux
  (iff (if-and-not-eval (strengthen-conjuncts-aux c) a)
       (if-and-not-eval c a))
  :hints (("Goal" :in-theory (enable strengthen-conjuncts-aux))))

;; TODO: Make a version that calls strengthen-conjuncts-aux repeatedly.

;; (thm
;;  (implies (not (equal (strengthen-conjuncts-aux c) c))
;;           (< (acl2-count (strengthen-conjuncts-aux c))
;;              (acl2-count c)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable STRENGTHEN-CONJUNCTS-AUX
;;                              make-if-term-gen))))
