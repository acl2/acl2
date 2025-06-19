; R1CSes in sparse form
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Supporting Author: Alessandro Coglio (coglio@kestrel.edu)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; A formalization of rank-1 constraint systems (R1CSes) in sparse form (with
;; only non-zero entries in the vectors represented).

;; See also ../dense/r1cs.lisp.

;; TODO: Consider not requiring the prime to actually be prime.

(include-book "../valuations")
(include-book "std/util/defaggregate" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/lists-light/reverse-list-def" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))

;; ;; A coefficient is an element of the field.  TODO: Consider, for readability,
;; ;; allowing large coefficients to be represented by negative numbers.
;; (defun coefficientp (coeff prime)
;;   (declare (xargs :guard (primep prime)))
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

; This can be thought of as a monomial, a single addend from a linear
; combination. Some terminology calls it an "R1CS term".
(defun sparse-vector-elementp (term)
  (declare (xargs :guard t))
  (and (true-listp term)
       (= 2 (len term))
       ;; could say (coefficientp (first item) prime) but then we'd have to
       ;; pass in the prime:
       (integerp (first term))
       (pseudo-varp (second term))))

;; A sparse vector, represented as a list of pairs where each pair contains a
;; coefficient and a pseudo-var.  Pseudo-vars not mentioned have an implicit
;; coefficient of 0.
(defund sparse-vectorp (vec)
  (declare (xargs :guard t))
  (if (atom vec)
      (equal vec nil)
    (let ((item (first vec)))
      (and (sparse-vector-elementp item)
           (sparse-vectorp (rest vec))))))

(defthm sparse-vectorp-of-cons
  (equal (sparse-vectorp (cons x y))
         (and (true-listp x)
              (equal 2 (len x))
              (integerp (first x))
              (pseudo-varp (second x))
              (sparse-vectorp y)))
  :hints (("Goal" :in-theory (enable sparse-vectorp))))

(defthm sparse-vectorp-of-append
  (equal (sparse-vectorp (append x y))
         (and (sparse-vectorp (true-list-fix x))
              (sparse-vectorp y)))
  :hints (("Goal" :in-theory (enable sparse-vectorp))))

(defthm sparse-vectorp-forward-to-true-listp
  (implies (sparse-vectorp vec)
           (true-listp vec))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable sparse-vectorp))))

(defthm sparse-vectorp-forward-to-alistp
  (implies (sparse-vectorp vec)
           (alistp vec))
  :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable sparse-vectorp))))

;; Checks that each pseudo-var is either 1 or an element of ALLOWED-VARS.
;; Previously, this checked that coefficients are field elements, but we
;; decided to relax that check to allow coefficients like -1.
;; Previously, this checked that no pseudo-var appeared more than once, but
;; we decided to drop that check since it was often violated in practice.
;; TODO: Add a lint-like check for repeated r1cs pseudo-vars.
(defund good-sparse-vectorp-aux (vec allowed-vars ;seen-pseudo-vars
                                     )
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (symbol-listp allowed-vars)
                              ;;(pseudo-var-listp seen-pseudo-vars)
                              )
                  :guard-hints (("Goal" :in-theory (enable sparse-vectorp)))))
  (if (atom vec)
      (null vec)
    (let* ((item (first vec))
           ;; (coeff (first item))
           (pseudo-var (second item)))
      (and (or (eql 1 pseudo-var)
               (member-eq pseudo-var allowed-vars))
           ;; (not (member pseudo-var seen-pseudo-vars)) ;prevent duplicate pseudo-vars
           (good-sparse-vectorp-aux (rest vec)
                                    allowed-vars
                                    ;;(cons pseudo-var seen-pseudo-vars)
                                    )))))

(defthm good-sparse-vectorp-aux-of-nil
  (good-sparse-vectorp-aux nil allowed-vars ;;seen-pseudo-vars
                           )
  :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

(defthm good-sparse-vectorp-aux-when-good-sparse-vectorp-aux-and-subsetp-equal-arg1
  (implies (and (good-sparse-vectorp-aux vec allowed-vars2 ;seen-pseudo-vars
                                         )
                (subsetp-equal allowed-vars2 allowed-vars))
           (good-sparse-vectorp-aux vec allowed-vars ;seen-pseudo-vars
                                    ))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

;; (defthm good-sparse-vectorp-aux-when-good-sparse-vectorp-aux-and-subsetp-equal-arg2
;;   (implies (and (good-sparse-vectorp-aux vec allowed-vars seen-pseudo-vars2)
;;                 (subsetp-equal seen-pseudo-vars seen-pseudo-vars2))
;;            (good-sparse-vectorp-aux vec allowed-vars seen-pseudo-vars))
;;   :hints (("Goal" :in-theory (enable good-sparse-vectorp-aux))))

(defund good-sparse-vectorp (vec allowed-vars)
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (symbol-listp allowed-vars))))
  (good-sparse-vectorp-aux vec allowed-vars ;; nil
                           ))

(defthm good-sparse-vectorp-when-good-sparse-vectorp-and-subsetp-equal
  (implies (and (good-sparse-vectorp vec allowed-vars1)
                (subsetp-equal allowed-vars1 allowed-vars2))
           (good-sparse-vectorp vec allowed-vars2))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-cdr
  (implies (good-sparse-vectorp vec allowed-vars)
           (good-sparse-vectorp (cdr vec) allowed-vars))
  :hints (("Goal" :expand (good-sparse-vectorp-aux vec allowed-vars ;;nil
                                                   )
           :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-nil
  (good-sparse-vectorp nil allowed-vars)
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm good-sparse-vectorp-of-cdr
  (implies (good-sparse-vectorp vec allowed-vars)
           (good-sparse-vectorp (cdr vec) allowed-vars))
  :hints (("Goal" :in-theory (enable good-sparse-vectorp))))

(defthm member-equal-of-cadr-of-car-when-good-sparse-vectorp
  (implies (and (good-sparse-vectorp vec vars)
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
  :pred r1cs-constraintp-aux
  :suppress-xdoc t)

;; TODO: Improve defaggregate to check that extra keys don't exist in the
;; alist! The lack of that check can cause problems if the keys are in the
;; wrong package.
(defund r1cs-constraintp (x)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable r1cs-constraintp-aux)))))
  (and (r1cs-constraintp-aux x)
       ;; TODO: Optimize:
       (subsetp-eq (strip-cars x) '(a b c))))

(defthm r1cs-constraintp-forward-to-r1cs-constraintp-aux
  (implies (r1cs-constraintp x)
           (r1cs-constraintp-aux x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable r1cs-constraintp))))

(defthm r1cs-constraintp-of-r1cs-constraint
  (implies (force (and (sparse-vectorp a)
                       (sparse-vectorp b)
                       (sparse-vectorp c)))
           (r1cs-constraintp (r1cs-constraint a b c)))
  :hints (("Goal" :in-theory (enable r1cs-constraintp
                                     r1cs-constraint
                                     r1cs-constraintp-aux))))

;; A true list of r1cs-constraints
(defun r1cs-constraint-listp (constraints)
  (declare (xargs :guard t))
  (if (atom constraints)
      (equal constraints nil)
    (and (r1cs-constraintp (first constraints))
         (r1cs-constraint-listp (rest constraints)))))

(defthm r1cs-constraint-listp-of-append
  (equal (r1cs-constraint-listp (append x y))
         (and (r1cs-constraint-listp (true-list-fix x))
              (r1cs-constraint-listp y)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-listp))))

;; A good constraint is one whose a, b, and c vectors are all good.
(defun good-r1cs-constraintp (constraint allowed-vars)
  (declare (xargs :guard (and (r1cs-constraintp constraint)
                              (var-listp allowed-vars))))
  (and (good-sparse-vectorp (r1cs-constraint->a constraint) allowed-vars)
       (good-sparse-vectorp (r1cs-constraint->b constraint) allowed-vars)
       (good-sparse-vectorp (r1cs-constraint->c constraint) allowed-vars)))

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
  ((prime primep)
   (vars var-listp)
   (constraints r1cs-constraint-listp))
  :require ((constraints-ok (good-r1cs-constraint-listp constraints
                                                        vars)))
  :pred r1csp
  ;; We have our own xdoc topic called r1cs:
  :suppress-xdoc t)

;; Since checking the guards is very slow when the prime is large:
(in-theory (disable (:e r1cs)))

;; Compute the dot product of the vector of coefficients and the vector of
;; values, where each value is either obtained by looking up a variable in the
;; valuation or is the special constant 1.  Since the representation is sparse,
;; we map over all the pairs in the vector and take the sum of the
;; corresponding products.
(defund dot-product (vec valuation prime)
  (declare (xargs :guard (and (sparse-vectorp vec)
                              (primep prime)
                              (r1cs-valuationp valuation prime)
                              (good-sparse-vectorp vec (strip-cars valuation)))
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
  (implies (posp prime)
           (fep (dot-product vec valuation prime) prime))
  :hints (("Goal" :expand (good-sparse-vectorp vec (strip-cars valuation))
           :in-theory (e/d (dot-product r1cs-valuationp sparse-vectorp valuation-bindsp)
                           (acl2::remove-equal-of-cons)))))

(verify-guards dot-product
  :hints (("Goal" :in-theory (e/d (valuation-bindsp)
                                  (strip-cars acl2::floor-mod-elim-rule)))))

(defthm dot-product-of-append
  (implies (posp prime)
           (equal (dot-product (append vec1 vec2) valuation prime)
                  (add (dot-product vec1 valuation prime)
                       (dot-product vec2 valuation prime)
                       prime)))
  :hints (("Goal" :in-theory (enable dot-product append))))

;; Check whether the VALUATION satisfies the CONSTRAINT.
(defund r1cs-constraint-holdsp (constraint valuation prime)
  (declare (xargs :guard (and (primep prime)
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
  (declare (xargs :guard (and (primep prime)
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

(defthm r1cs-constraints-holdp-of-cons
  (equal (r1cs-constraints-holdp (cons a x) valuation prime)
         (and (r1cs-constraint-holdsp a valuation prime)
              (r1cs-constraints-holdp x valuation prime)))
  :hints (("Goal" :in-theory (enable r1cs-constraints-holdp))))

(defthm r1cs-constraints-holdp-of-reverse-list
  (equal (r1cs-constraints-holdp (acl2::reverse-list x) valuation prime)
         (r1cs-constraints-holdp x valuation prime))
  :hints (("Goal" :in-theory (enable acl2::reverse-list
                                     r1cs-constraints-holdp))))

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
