; Rank-1 constraint systems, represented in dense form
;
; Copyright (C) 2019-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; A formalization of rank-1 constraint systems (R1CSes) in dense form (with
;; zeros explicitly represented in the vectors).

;; TODO: Adapt this to allow coefficients such as -1 that are not field
;; elements (see what was done for the sparse representation).

;; See also ../sparse/r1cs.lisp.

(include-book "std/util/defaggregate" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; A true list of variables, with no duplicates
(defun var-listp (vars)
  (declare (xargs :guard t))
  (and (symbol-listp vars)
       (no-duplicatesp-eq vars)))

;; A coefficient is an element of the field.  TODO: Consider changing the
;; representation to allow negative numbers to represent very large
;; coefficients.
(defun coefficientp (coeff prime)
  (declare (xargs :guard (primep prime)))
  (fep coeff prime))

;; A true list of coefficients.
(defun coefficient-listp (coeffs prime)
  (declare (xargs :guard (primep prime)))
  (if (atom coeffs)
      (equal coeffs nil)
    (and (coefficientp (first coeffs) prime)
         (coefficient-listp (rest coeffs) prime))))

;; A true list of field elements.
(defun fe-listp (elems prime)
  (declare (xargs :guard (primep prime)))
  (if (atom elems)
      (equal elems nil)
    (and (fep (first elems) prime)
         (fe-listp (rest elems) prime))))

;; A constraint in an R1CS consists of 3 vectors: a, b, and c, which must all
;; have the same length.
(std::defaggregate r1cs-constraint
 ((a (integer-listp a))
  (b (integer-listp a))
  (c (integer-listp a)))
 :require ((constraint-lengths-match
            (and (equal (len a)
                        (len b))
                 (equal (len b)
                        (len c)))))
 :pred r1cs-constraintp)

;; A list of r1cs-constraints
(defun r1cs-constraint-listp (constraints)
  (declare (xargs :guard t))
  (if (atom constraints)
      (equal constraints nil)
    (and (r1cs-constraintp (first constraints))
         (r1cs-constraint-listp (rest constraints)))))

;; A good constraint is one whose a, b, and c vectors all contain coefficients
;; less than the prime.
(defun good-r1cs-constraintp (constraint prime)
  (declare (xargs :guard (primep prime)))
  (and (r1cs-constraintp constraint)
       (coefficient-listp (r1cs-constraint->a constraint) prime)
       (coefficient-listp (r1cs-constraint->b constraint) prime)
       (coefficient-listp (r1cs-constraint->c constraint) prime)))

;; A list of good-r1cs-constraints
(defun good-r1cs-constraint-listp (constraints prime)
  (declare (xargs :guard (primep prime)))
  (if (atom constraints)
      (equal constraints nil)
    (and (good-r1cs-constraintp (first constraints) prime)
         (good-r1cs-constraint-listp (rest constraints) prime))))

;; The length of a constraint is the length of any of its coefficient lists
;; (which must all have the same length).
(defun r1cs-constraint-length (constraint)
  (declare (xargs :guard (r1cs-constraintp constraint)))
  (len (r1cs-constraint->a constraint)))

(defun constraints-have-lengthp (len constraints)
  (declare (xargs :guard (r1cs-constraint-listp constraints)))
  (if (endp constraints)
      t
    (and (equal len (r1cs-constraint-length (first constraints)))
         (constraints-have-lengthp len (rest constraints)))))

;; An R1CS consists of a prime, vars (input vars, intermediate vars, and output vars), and a list of constraints.
;; TODO: Consider indicating which vars are inputs and which are outputs.
(std::defaggregate r1cs
  ((prime primep)
   (vars var-listp)
   (constraints r1cs-constraint-listp))
  :require ((no-duplicatesp-in-r1c-vars (no-duplicatesp-equal vars))
            (constraint-lengths-ok (constraints-have-lengthp
                                    (+ 1 ; for the single 1 that we prepend to the var vector
                                       (len vars))
                                    constraints))
            (constraints-ok (good-r1cs-constraint-listp constraints prime)))
  :pred r1csp)

;; A valuation is a map from variables to their values.
(defund r1cs-valuationp (valuation prime)
  (declare (xargs :guard (primep prime)))
  (and (alistp valuation)
       (var-listp (strip-cars valuation))
       (fe-listp (strip-cdrs valuation) prime)))

(defthm r1cs-valuationp-forward-to-alistp
  (implies (r1cs-valuationp valuation prime)
           (alistp valuation))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

;; Lookup the values of the vars in the valuation
(defun lookup-vars (vars valuation)
  (declare (xargs :guard (and (var-listp vars)
                              (alistp valuation)
                              (subsetp-eq vars (strip-cars valuation)))))
  (if (endp vars)
      nil
    (cons (lookup-equal (first vars) valuation)
          (lookup-vars (rest vars) valuation))))

(defthm len-of-lookup-vars
  (equal (len (lookup-vars vars valuation))
         (len vars))
  :hints (("Goal" :in-theory (enable lookup-vars))))

;; Check whether VALUATION binds VAR.
(defun valuation-bindsp (valuation var)
  (declare (xargs :guard (and (symbolp var)
                              (alistp valuation))))
  (member-equal var (strip-cars valuation)))

(defthm fep-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime)
                (valuation-bindsp valuation var))
           (fep (lookup-equal var valuation) prime))
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm integerp-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime) ;prime is a free var
                (valuation-bindsp valuation var))
           (integerp (lookup-equal var valuation)))
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm rationalp-of-lookup-equal
  (implies (and (r1cs-valuationp valuation prime) ;prime is a free var
                (valuation-bindsp valuation var))
           (rationalp (lookup-equal var valuation)))
  :hints (("Goal" :in-theory (enable r1cs-valuationp))))

(defthm fe-listp-of-lookup-vars
  (implies (and (r1cs-valuationp valuation prime)
                (subsetp-eq vars (strip-cars valuation)))
           (fe-listp (lookup-vars vars valuation) prime))
  :hints (("Goal" :in-theory (enable lookup-vars))))

;; The "constraint vector" contains the values of the VARS (looked up in the
;; VALUATION), preceded by a single constant 1.
(defund make-constraint-vector (valuation vars)
  (declare (xargs :guard (and (alistp valuation)
                              (var-listp vars)
                              (subsetp-eq vars (strip-cars valuation)))))
  (cons 1 (lookup-vars vars valuation)))

(defthm len-of-make-constraint-vector
  (equal (len (make-constraint-vector valuation vars))
         (+ 1 (len vars)))
  :hints (("Goal" :in-theory (enable make-constraint-vector))))

(defthm fe-listp-of-make-constraint-vector
  (implies (and (r1cs-valuationp valuation prime)
                (var-listp vars)
                (subsetp-eq vars (strip-cars valuation))
                (primep prime))
           (fe-listp (make-constraint-vector valuation vars) prime))
  :hints (("Goal" :in-theory (enable make-constraint-vector))))

;; Multiply each value in the vector by its corresponding coefficient, and take
;; the sum (mod the prime).
(defund dot-product (coeffs vector prime)
  (declare (xargs :guard (and (primep prime)
                              (coefficient-listp coeffs prime)
                              (fe-listp vector prime)
                              (= (len coeffs)
                                 (len vector)))))
  (if (endp coeffs)
      0
    (add (mul (first coeffs)
              (first vector)
              prime)
         (dot-product (rest coeffs) (rest vector) prime)
         prime)))

(defthm fep-of-dot-product
  (implies (and (coefficient-listp coeffs prime)
                (fe-listp vector prime)
                (equal (len coeffs) (len vector))
                (primep prime))
           (fep (dot-product coeffs vector prime) prime))
  :hints (("Goal" :in-theory (enable dot-product))))

;; Check whether the VALUATION satisfies the CONSTRAINT.  The coefficient lists
;; (a,b,c) in each constraint are paired with the constraint vector (always
;; containing a single 1 followed by the values of the variables, in the order
;; in which the variables appear in VARS).
(defund r1cs-constraint-holdsp (constraint valuation vars prime)
  (declare (xargs :guard (and (primep prime)
                              (good-r1cs-constraintp constraint prime)
                              (r1cs-valuationp valuation prime)
                              (var-listp vars)
                              (subsetp-eq vars (strip-cars valuation))
                              (equal (r1cs-constraint-length constraint) (+ 1 (len vars))))))
  (let ((vector (make-constraint-vector valuation vars)))
    ;; The constraint is (a dot x) * (b dot x) - (c dot x) = 0, where x
    ;; contains a single constant 1 , followed by the values of the variabels.
    ;; This is equivalent to (a dot x) * (b dot x) = (c dot x).
    (equal (mul (dot-product (r1cs-constraint->a constraint)
                             vector
                             prime)
                (dot-product (r1cs-constraint->b constraint)
                             vector
                             prime)
                prime)
           (dot-product (r1cs-constraint->c constraint)
                        vector
                        prime))))

;; Check whether the valuation satisfies all of the constraints.
(defun r1cs-constraints-holdp (constraints valuation vars prime)
  (declare (xargs :guard (and (primep prime)
                              (good-r1cs-constraint-listp constraints prime)
                              (r1cs-valuationp valuation prime)
                              (var-listp vars)
                              (subsetp-eq vars (strip-cars valuation))
                              (constraints-have-lengthp (+ 1 (len vars)) constraints))))
  (if (endp constraints)
      t
    (and (r1cs-constraint-holdsp (first constraints) valuation vars prime)
         (r1cs-constraints-holdp (rest constraints) valuation vars prime))))

(local
 (defthm symbol-listp-when-var-listp
   (implies (var-listp vars)
            (symbol-listp vars))))

(local
 (defthm true-listp-when-var-listp
   (implies (var-listp vars)
            (true-listp vars))))

;; Check whether a valuation satisifies an R1CS.
(defun r1cs-holdsp (r1cs valuation)
  (declare (xargs :guard (and (r1csp r1cs)
                              (r1cs-valuationp valuation (r1cs->prime r1cs))
                              ;; all of the variables in the r1cs should be
                              ;; bound in the valuation:
                              (subsetp-eq (r1cs->vars r1cs) (strip-cars valuation)))
                  :guard-hints (("Goal" :in-theory (enable R1CSP)))))
  (r1cs-constraints-holdp (r1cs->constraints r1cs)
                          valuation
                          (r1cs->vars r1cs)
                          (r1cs->prime r1cs)))
