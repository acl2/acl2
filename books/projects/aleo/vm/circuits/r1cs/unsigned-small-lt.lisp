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

(include-book "pow2sum-vectors")
(include-book "unsigned-small-sub-opt")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget calculates whether two unsigned integers,
; expressed in little endian bits xs and ys,
; satisfy the less-than relation, i.e.
;   x(0) + 2.x(1) + ... < y(0) + 2.y(1) + ...
; In order for this to work, the unsigned integers must be relatively small,
; in the sense that their bit length n plus one
; is less than the prime's bit length:
; the reason is that we perform essentially a subtraction with an offset,
; which may yield a result that takes n+1 bits,
; and so the prime p must have more thatn n+1 bits.

; The subtraction is performed similarly to unsigned-small-sub-opt,
; but the 2^n addend here appears at the end instead of in between.
; Thus, we define the vector with the 2^n at the end,
; and prove it equivalent to the vector in unsigned-small-sub-opt.

(define unsigned-small-lt-vector ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (p primep))
  :guard (equal (len ys) (len xs))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (append (pow2sum-vector xs 0)
          (pow2sum-neg-prime-vector ys 0 p)
          (list (list (expt 2 (len xs)) 1))))

(defruled unsigned-small-lt-vector-to-unsigned-small-sub-opt-vector
  (implies (posp p)
           (equal (r1cs::dot-product
                   (unsigned-small-lt-vector xs ys p) asg p)
                  (r1cs::dot-product
                   (unsigned-small-sub-opt-vector xs ys p) asg p)))
  :enable (unsigned-small-lt-vector
           unsigned-small-sub-opt-vector
           r1cs::dot-product))

; We define the less-than gadget similarly to unsigned-small-sub-opt,
; but we split the low n bits zs of the result from the high bit z.
; In fact, zs are auxiliary variables, while z is the output variable.

(define unsigned-small-lt-gadget ((xs symbol-listp)
                                  (ys symbol-listp)
                                  (zs symbol-listp)
                                  (z symbolp)
                                  (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (boolean-check-gadget z p)
          (list (r1cs::make-r1cs-constraint
                 :a (unsigned-small-lt-vector xs ys p)
                 :b (list (list 1 1))
                 :c (pow2sum-vector (append zs (list z)) 0)))))

; We show the equivalence of unsigned-small-lt to unsigned-small-sub-opt.
; But since the result bits are organized a little differently,
; we need an auxiliary lemma to relate the boolean constraints of the gadgets.

(defruled unsigned-small-lt-gadget-to-unsigned-small-sub-opt-gadget
  (implies (posp p)
           (equal (r1cs::r1cs-constraints-holdp
                   (unsigned-small-lt-gadget xs ys zs z p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-sub-opt-gadget xs ys (append zs (list z)) p)
                   asg
                   p)))
  :do-not-induct t
  :enable (r1cs::r1cs-constraint-holdsp
           unsigned-small-lt-gadget
           unsigned-small-sub-opt-gadget
           unsigned-small-lt-vector-to-unsigned-small-sub-opt-vector)
  :prep-lemmas
  ((defrule lemma
     (implies (posp p)
              (equal (r1cs::r1cs-constraints-holdp
                      (boolean-check-gadget-list (append zs (list z)) p)
                      asg
                      p)
                     (r1cs::r1cs-constraints-holdp
                      (append (boolean-check-gadget-list zs p)
                              (boolean-check-gadget z p))
                      asg
                      p)))
     :enable (r1cs::r1cs-constraint-holdsp
              boolean-check-gadget-list))))

; Finally we prove the soundness theorem for the unsigned-small-lt gadget.
; If the gadget holds, then z is 0 iff x < y.

(defruled unsigned-small-lt-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-lt-gadget xs ys zs z p) asg p)
                               (and (bitp z$)
                                    (equal (< (lebits=>nat xs$)
                                              (lebits=>nat ys$))
                                           (equal z$ 0)))))))
  :do-not-induct t
  :enable (unsigned-small-lt-gadget-to-unsigned-small-sub-opt-gadget
           unsigned-small-sub-opt-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append))
