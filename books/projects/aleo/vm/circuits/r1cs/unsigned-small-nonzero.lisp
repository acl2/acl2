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

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget checks whether an unsigned integer,
; expressed as its bits xs in little endian order,
; is not zero.
; We assume that the unsigned integer is small (relatively speaking),
; i.e. that its number of bits is less than the number of bits of the prime;
; this means that the value of the unsigned integer,
; expressed as weighted sum of powers of two,
; fits in the field.

; This gadget consists of a single constraint
;  (x(0) + 2.x(1) + ...) (i) = (1)
; where i is an auxiliary variable that,
; in order for the constraint to be satisfied,
; must be the inverse of the value of the integer (as a field element).

; Note that this gadget does not calculate
; whether the integer is zero or not;
; it enforces it to be non-zero.

(define unsigned-small-nonzero-gadget ((xs symbol-listp) (i symbolp) (p primep))
  :guard (< (len xs) (integer-length p))
  (declare (ignore p))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (pow2sum-vector xs 0)
         :b (list (list 1 i))
         :c (list (list 1 1)))))

; The (soundness) proof is unremarkable.

(defruled unsigned-small-nonzero-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbolp i)
                (< (len xs) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg i))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-nonzero-gadget xs i p) asg p)
                               (not (equal (lebits=>nat xs$) 0))))))
  :do-not-induct t
  :enable (unsigned-small-nonzero-gadget
           r1cs::r1cs-constraint-holdsp
           pow2sum-vector-to-mod-of-lebits=>nat
           r1cs::dot-product))
