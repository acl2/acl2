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

(local (include-book "../library-extensions/arithmetic"))

(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget adds a field element x to the little endian value of bits ys
; and equates that to the little endian value of bits zs:
;   (z(0) + 2*z(1) + ... + 2^(n-1)*z(n-1)) (1) =
;   (x + y(0) + 2*y(1) + ... + 2^(m-1)*y(m-1))
; We constrain n to be below the bit size of the prime,
; and m to be below one less than the bit size of the prime.
; We cannot state any syntactic constraints on the variable x
; that would limit its field value,
; so a constraint is given on its actual value in the correctness theorem:
; the constraint is that
; its bit size is below one less than the bit size of the prime,
; i.e. the same constraint on the ys bits.
; This way, we add two numbers
; whose bit size is one less than the bit size of the prime;
; the bit size of the result is one more than the maximum of the two bit sizes,
; and so it is below the bit size of the prime,
; and its value is representable in the prime field.

(define field-bits-add-bits-gadget ((x symbolp)
                                    (ys symbol-listp)
                                    (zs symbol-listp)
                                    (p primep))
  :guard (and (< (1+ (len ys)) (integer-length p))
              (< (len zs) (integer-length p)))
  (declare (ignore p))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (pow2sum-vector zs 0)
         :b (list (list 1 1))
         :c (cons (list 1 x)
                  (pow2sum-vector ys 0)))))

; Soundness and completeness.
; As mentioned above, we have a hypothesis saying that
; the value of x is sufficiently small that
; adding it to the value of the ys bits stays within the field.
; The constraint on the length of xs also ensures that
; their value is representable in the field.

(defruled field-bits-add-bits-gadget-to-add
  (implies (and (primep p)
                (symbolp x)
                (symbol-listp ys)
                (symbol-listp zs)
                (< (1+ (len ys)) (integer-length p))
                (< (len zs) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((x$ (lookup-equal x asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp ys$)
                           (bit-listp zs$)
                           (< (1+ (integer-length x$))
                              (integer-length p)))
                      (equal (r1cs::r1cs-constraints-holdp
                              (field-bits-add-bits-gadget x ys zs p) asg p)
                             (equal (lebits=>nat zs$)
                                    (+ x$ (lebits=>nat ys$)))))))
  :do-not-induct t
  :enable (field-bits-add-bits-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product-of-append
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::add
           positive->=-expt2-of-integer-length-minus-1))
