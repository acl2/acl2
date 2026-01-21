; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define an operation to negate an R1CS vector.
; The operation goes through the vector and negates each coefficient;
; the monomials are left in the same order, with the coefficients negated.

(define vector-neg ((vec r1cs::sparse-vectorp))
  :returns (vec-neg r1cs::sparse-vectorp :hyp :guard)
  (cond ((endp vec) nil)
        (t (b* ((elem (car vec)))
             (cons (list (- (first elem))
                         (second elem))
                   (vector-neg (cdr vec))))))
  ///

  (defret consp-of-vector-neg
    (equal (consp vec-neg)
           (consp vec))))

; Attempting to prove directly the non-local theorem about vector-neg below
; leads to subgoals that look a more complicated than expected,
; presumably due to the prime field rules re-arranging things
; in ways that do not seem in line with the way one would prove the theorem;
; the main issue is probably the use of - in the definition above,
; as opposed to the use of pfield::neg in the non-local theorem below.
; (Just enabling pfield::neg, and also pfield::add as it may result
; from rules that reliminate pfield::neg in favor of pfield::add,
; does not lead to any immediate proof either.)

; Instead of figuring out and tweaking the use of the rules,
; we introduce an alternative definition of the function that uses pfield::neg,
; we prove this alternative definition equivalent to the one above,
; we prove the desired theorem for the alternative definition,
; and we easily transfer the result to the definition above.

; Note that the local function below is not guard-verified,
; because pfield::neg can only be applied to a field element,
; but (first elem) is not necessarily that.
; We would have to add a stronger guard to the definition above
; if we wanted to use pfield::neg instead of -
; (which would be an equally good way to define the function above).
; It is to avoid this that we use - above
; and that we introduce the alternative definition below.
; Since the function below is only a local device for the proof,
; it does not matter that it is not guard-verified.

(local
 (defun vector-neg-alt (vec p)
   (cond ((endp vec) nil)
         (t (b* ((elem (car vec)))
              (cons (list (pfield::neg (first elem) p)
                          (second elem))
                    (vector-neg-alt (cdr vec) p)))))))

(defruledl dot-product-of-vector-neg-to-dot-product-of-vector-neg-alt
  (implies (and (posp p)
                (r1cs::sparse-vectorp vec))
           (equal (r1cs::dot-product (vector-neg vec) asg p)
                  (r1cs::dot-product (vector-neg-alt vec p) asg p)))
  :enable (vector-neg
           vector-neg-alt
           r1cs::dot-product
           pfield::neg))

(defruledl dot-product-of-vector-neg-alt-to-neg-of-dot-product
  (implies (and (posp p)
                (r1cs::sparse-vectorp vec))
           (equal (r1cs::dot-product (vector-neg-alt vec p) asg p)
                  (pfield::neg (r1cs::dot-product vec asg p) p)))
  :enable (vector-neg-alt r1cs::dot-product))

(defruled dot-product-of-vector-neg-to-neg-of-dot-product
  (implies (and (posp p)
                (r1cs::sparse-vectorp vec))
           (equal (r1cs::dot-product (vector-neg vec) asg p)
                  (pfield::neg (r1cs::dot-product vec asg p) p)))
  :enable (dot-product-of-vector-neg-to-dot-product-of-vector-neg-alt
           dot-product-of-vector-neg-alt-to-neg-of-dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We define a variant of the above operation
; that reduces the negates coefficients modulo the prime.
; The dot product is the same,
; because coefficients are semantically reduced modulo the prime.
; The difference between the two kinds of negated vectors is just syntactic;
; nonetheless, it is useful for constructing gadgets in ACL2
; that are syntactically equally to given gadgets.

(define vector-neg-prime ((vec r1cs::sparse-vectorp) (p primep))
  :returns (vec-neg r1cs::sparse-vectorp :hyp :guard)
  (cond ((endp vec) nil)
        (t (b* ((elem (car vec)))
             (cons (list (mod (- (first elem)) p)
                         (second elem))
                   (vector-neg-prime (cdr vec) p)))))
  ///

  (defret consp-of-vector-neg-prime
    (equal (consp vec-neg)
           (consp vec))))

(defruled dot-product-of-vector-neg-prime-to-dot-product-of-vector-neg
  (implies (and (posp p)
                (r1cs::sparse-vectorp vec))
           (equal (r1cs::dot-product (vector-neg-prime vec p) asg p)
                  (r1cs::dot-product (vector-neg vec) asg p)))
  :enable (vector-neg-prime
           vector-neg
           r1cs::dot-product))

(defruled dot-product-of-vector-neg-prime-to-neg-of-dot-product
 (implies (and (posp p)
               (r1cs::sparse-vectorp vec))
          (equal (r1cs::dot-product (vector-neg-prime vec p) asg p)
                 (pfield::neg (r1cs::dot-product vec asg p) p)))
 :enable (dot-product-of-vector-neg-prime-to-dot-product-of-vector-neg
          dot-product-of-vector-neg-to-neg-of-dot-product))
