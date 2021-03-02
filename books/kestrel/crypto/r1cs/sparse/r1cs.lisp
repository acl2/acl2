; R1CSes in sparse form
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; A formalization of rank-1 constraint systems (R1CSes) in sparse form (with
;; only non-zero entries in the vectors represented).

;; See also ../dense/r1cs.lisp.

;; TODO: Consider not requiring the prime to actually be prime.

(include-book "../valuations")
(include-book "std/util/defaggregate" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))

;; ;; A coefficient is an element of the field.  TODO: Consider, for readability,
;; ;; allowing large coefficients to be represented by negative numbers.
;; (defun coefficientp (coeff prime)
;;   (declare (xargs :guard (rtl::primep prime)))
;;   (fep coeff prime))

;; A "pseudo-variable" is either a variable or the constant 1.
(defun pseudo-varp (x)
  (declare (xargs :guard t))
  (or (symbolp x)
      (equal x '1)))

;; A true list of pseudo-variables
(defund pseudo-var-listp (pseudo-vars)
  (declare (xargs :guard t))
  (if (atom pseudo-vars)
      (equal pseudo-vars nil)
    (and (pseudo-varp (first pseudo-vars))
         (pseudo-var-listp (rest pseudo-vars)))))

(defthm pseudo-var-listp-of-remove-equal
  (implies (pseudo-var-listp pseudo-vars)
           (pseudo-var-listp (remove-equal var pseudo-vars)))
  :hints (("Goal" :in-theory (enable pseudo-var-listp))))

(defthm pseudo-var-listp-of-cons
  (equal (pseudo-var-listp (cons var pseudo-vars))
         (and (pseudo-varp var)
              (pseudo-var-listp pseudo-vars)))
  :hints (("Goal" :in-theory (enable pseudo-var-listp))))

(defthm pseudo-var-listp-forward-to-true-listp
  (implies (pseudo-var-listp pseudo-vars)
           (true-listp pseudo-vars))
  :hints (("Goal" :in-theory (enable pseudo-var-listp))))

(defthm pseudo-var-listp-when-symbol-listp
  (implies (symbol-listp vars)
           (pseudo-var-listp vars))
  :hints (("Goal" :in-theory (enable pseudo-var-listp))))

;; A sparse vector, represented as a list of pairs where each pair contains a
;; coefficient and a pseudo-var.  Pseudo-vars not mentioned have an implicit
;; coefficient of 0.
(defund sparse-vectorp (vec)
  (declare (xargs :guard t))
  (if (atom vec)
      (equal vec nil)
    (let ((item (first vec)))
      (and (true-listp item)
           (= 2 (len item))
           ;; could say (coefficientp (first item) prime) but then we'd have to
           ;; pass in the prime:
           (integerp (first item))
           (pseudo-varp (second item))
           (sparse-vectorp (rest vec))))))

(defthm sparse-vectorp-of-cons
  (equal (sparse-vectorp (cons x y))
         (and (true-listp x)
              (equal 2 (len x))
              (integerp (first x))
              (pseudo-varp (second x))
              (sparse-vectorp y)))
  :hints (("Goal" :in-theory (enable sparse-vectorp))))

(defthm sparse-vectorp-forward-to-true-listp
  (implies (sparse-vectorp vec)
           (true-listp vec))
  :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable sparse-vectorp))))

;; Check that each pseudo-var is an element of ALLOWED-PSEUDO-VARS.  Also
;; checks that no pseudo-var appears in more than one entry in VEC.
;; Previously, this checked that coefficients are field elements, but we
;; decided to relax that check to allow coefficients like -1.
(defund good-sparse-vectorp-aux (vec allowed-pseudo-vars seen-pseudo-vars)
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (pseudo-var-listp allowed-pseudo-vars)
                              (pseudo-var-listp seen-pseudo-vars))
                  :guard-hints (("Goal" :in-theory (enable sparse-vectorp)))))
  (if (atom vec)
      (null vec)
    (let* ((item (first vec))
           ;; (coeff (first item))
           (pseudo-var (second item)))
      (and (member pseudo-var allowed-pseudo-vars)
           (not (member pseudo-var seen-pseudo-vars)) ;prevent duplicate vars
           (good-sparse-vectorp-aux (rest vec)
                                    allowed-pseudo-vars
                                    (cons pseudo-var seen-pseudo-vars))))))

(defthm good-sparse-vectorp-aux-of-nil
  (good-sparse-vectorp-aux nil allowed-pseudo-vars seen-pseudo-vars)
  :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

(defthm good-sparse-vectorp-aux-when-good-sparse-vectorp-aux-and-subsetp-equal-arg1
  (implies (and (good-sparse-vectorp-aux vec allowed-pseudo-vars2 seen-pseudo-vars)
                (subsetp-equal allowed-pseudo-vars2 allowed-pseudo-vars))
           (good-sparse-vectorp-aux vec allowed-pseudo-vars seen-pseudo-vars))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

(defthm good-sparse-vectorp-aux-when-good-sparse-vectorp-aux-and-subsetp-equal-arg2
  (implies (and (good-sparse-vectorp-aux vec allowed-pseudo-vars seen-pseudo-vars2)
                (subsetp-equal seen-pseudo-vars seen-pseudo-vars2))
           (good-sparse-vectorp-aux vec allowed-pseudo-vars seen-pseudo-vars))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

(defund good-sparse-vectorp (vec allowed-pseudo-vars)
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (pseudo-var-listp allowed-pseudo-vars))))
  (good-sparse-vectorp-aux vec allowed-pseudo-vars nil))

(defthm good-sparse-vectorp-when-good-sparse-vectorp-and-subsetp-equal
  (implies (and (good-sparse-vectorp vec allowed-pseudo-vars1)
                (subsetp-equal allowed-pseudo-vars1 allowed-pseudo-vars2))
           (good-sparse-vectorp vec allowed-pseudo-vars2))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-cdr
  (implies (good-sparse-vectorp vec allowed-pseudo-vars)
           (good-sparse-vectorp (cdr vec) allowed-pseudo-vars))
  :hints (("Goal" :expand (good-sparse-vectorp-aux vec allowed-pseudo-vars nil)
           :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-nil
  (good-sparse-vectorp nil allowed-pseudo-vars)
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-cdr
  (implies (good-sparse-vectorp vec allowed-pseudo-vars)
           (good-sparse-vectorp (cdr vec) allowed-pseudo-vars))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm member-equal-of-cadr-of-car-when-good-sparse-vectorp
  (implies (and (good-sparse-vectorp vec (cons 1 vars))
                (consp vec)
                (not (equal 1 (cadr (car vec)))))
           (member-equal (car (cdr (car vec))) vars))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp
                                     good-sparse-vectorp-aux))))

;; A constraint in an R1CS consists of 3 sparse vectors: a, b, and c.
(std::defaggregate r1cs-constraint
  ((a (sparse-vectorp a))
   (b (sparse-vectorp b))
   (c (sparse-vectorp c)))
  :pred r1cs-constraintp)

;; A true list of r1cs-constraints
(defun r1cs-constraint-listp (constraints)
  (declare (xargs :guard t))
  (if (atom constraints)
      (equal constraints nil)
    (and (r1cs-constraintp (first constraints))
         (r1cs-constraint-listp (rest constraints)))))

;; A good constraint is one whose a, b, and c vectors are all good.
(defun good-r1cs-constraintp (constraint allowed-vars)
  (declare (xargs :guard (and (r1cs-constraintp constraint)
                              (var-listp allowed-vars))))
  (let ((allowed-pseudo-vars (cons 1 allowed-vars)))
    (and (good-sparse-vectorp (r1cs-constraint->a constraint) allowed-pseudo-vars)
         (good-sparse-vectorp (r1cs-constraint->b constraint) allowed-pseudo-vars)
         (good-sparse-vectorp (r1cs-constraint->c constraint) allowed-pseudo-vars))))

(defthm good-r1cs-constraintp-monotone
  (implies (and (subsetp-equal allowed-vars1 allowed-vars2)
                (good-r1cs-constraintp constraint allowed-vars1))
           (good-r1cs-constraintp constraint allowed-vars2))
  :hints (("Goal" :in-theory (enable good-r1cs-constraintp))))

;; A list of good-r1cs-constraints
(defun good-r1cs-constraint-listp (constraints allowed-vars)
  (declare (xargs :guard (and (r1cs-constraint-listp constraints)
                              (var-listp allowed-vars))))
  (if (atom constraints)
      t
    (and (good-r1cs-constraintp (first constraints) allowed-vars)
         (good-r1cs-constraint-listp (rest constraints) allowed-vars))))

(defthm good-r1cs-constraint-listp-monotone
  (implies (and (subsetp-equal allowed-vars1 allowed-vars2)
                (good-r1cs-constraint-listp constraints allowed-vars1))
           (good-r1cs-constraint-listp constraints allowed-vars2))
  :hints (("Goal" :in-theory (enable good-r1cs-constraint-listp))))

;; An R1CS consists of a prime, a list of variables (including input vars,
;; intermediate vars, and output vars), and a list of constraints.  TODO:
;; Consider indicating which vars are inputs and which are outputs.
(std::defaggregate r1cs
  ((prime rtl::primep)
   (vars var-listp)
   (constraints r1cs-constraint-listp))
  :require ((constraints-ok (good-r1cs-constraint-listp constraints
                                                        vars)))
  :pred r1csp)

;; Since checking the guards if very slow when the prime is large:
(in-theory (disable (:e r1cs)))

;; Compute the dot product of the vector of coefficients and the vector of
;; values, where each value is either obtained by looking up a variable in the
;; valuation or is the special constant 1.  Since the representation is sparse,
;; we map over all the pairs in the vector and take the sum of the
;; corresponding products.
(defund dot-product (vec valuation prime)
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (rtl::primep prime)
                              (r1cs-valuationp valuation prime)
                              (good-sparse-vectorp vec (cons 1 (strip-cars valuation))))
                  :verify-guards nil ;done below
                  ))
  (if (endp vec)
      0
    (let* ((item (first vec))
           (coeff (first item))
           (pseudo-var (second item))
           (var-value (if (equal 1 pseudo-var)
                          1
                        (lookup-eq pseudo-var valuation))))
      (add (mul (mod coeff prime) ;reduce the coefficient mod the prime in case it is, e.g., -1
                var-value prime)
           (dot-product (rest vec) valuation prime)
           prime))))

(defthm fep-of-dot-product
  (implies (and (sparse-vectorp vec)
                (rtl::primep prime)
                (r1cs-valuationp valuation prime)
                (good-sparse-vectorp vec (cons 1 (strip-cars valuation))) ;drop?
                )
           (fep (dot-product vec valuation prime) prime))
  :hints (("Goal" :expand (good-sparse-vectorp vec (cons 1 (strip-cars valuation)))
           :in-theory (e/d (dot-product r1cs-valuationp sparse-vectorp valuation-bindsp)
                           (acl2::remove-equal-of-cons)))))

(verify-guards dot-product
  :hints (("Goal" :in-theory (e/d (valuation-bindsp)
                                  (strip-cars)))))

;; Check whether the VALUATION satisfies the CONSTRAINT.
(defund r1cs-constraint-holdsp (constraint valuation prime)
  (declare (xargs :guard (and (rtl::primep prime)
                              (r1cs-constraintp constraint)
                              (r1cs-valuationp valuation prime)
                              (good-r1cs-constraintp constraint (strip-cars valuation)))))
  ;; The constraint is (a dot x) * (b dot x) - (c dot x) = 0, where x contains
  ;; a single constant 1 followed by the values of the variables.  This is
  ;; equivalent to (a dot x) * (b dot x) = (c dot x).
  (equal (mul (dot-product (r1cs-constraint->a constraint)
                           valuation
                           prime)
              (dot-product (r1cs-constraint->b constraint)
                           valuation
                           prime)
              prime)
         (dot-product (r1cs-constraint->c constraint)
                      valuation
                      prime)))

;; Check whether the valuation satisfies all of the constraints.
(defun r1cs-constraints-holdp (constraints valuation prime)
  (declare (xargs :guard (and (rtl::primep prime)
                              (r1cs-constraint-listp constraints)
                              (r1cs-valuationp valuation prime)
                              (good-r1cs-constraint-listp constraints (strip-cars valuation)))))
  (if (endp constraints)
      t
    (and (r1cs-constraint-holdsp (first constraints) valuation prime)
         (r1cs-constraints-holdp (rest constraints) valuation prime))))

(defthm r1cs-constraints-holdp-of-append
  (equal (r1cs-constraints-holdp (append x y) valuation prime)
         (and (r1cs-constraints-holdp x valuation prime)
              (r1cs-constraints-holdp y valuation prime)))
  :hints (("Goal" :in-theory (enable r1cs-constraints-holdp))))

(local
 (defthm symbol-listp-when-var-listp
   (implies (var-listp vars)
            (symbol-listp vars))))

(local
 (defthm true-listp-when-var-listp
   (implies (var-listp vars)
            (true-listp vars))))

;; Check whether VALUATION satisifies R1CS.
(defun r1cs-holdsp (r1cs valuation)
  (declare (xargs :guard (and (r1csp r1cs)
                              (r1cs-valuationp valuation (r1cs->prime r1cs))
                              ;; all of the variables in the r1cs should be bound in the valuation
                              (subsetp-eq (r1cs->vars r1cs) (strip-cars valuation)))
                  :guard-hints (("Goal" :in-theory (enable r1csp
                                                           r1cs->constraints
                                                           r1cs->prime
                                                           r1cs->vars)))))
  (r1cs-constraints-holdp (r1cs->constraints r1cs)
                          valuation
                          (r1cs->prime r1cs)))
