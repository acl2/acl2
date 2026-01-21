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
(local (include-book "../library-extensions/digits"))

;; (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget multiplies two natural numbers, expressed in bits,
; putting the result into a field element.
; The sum of the numbers of bits of the two operands
; must be less than the bit length of the prime,
; so that the exact product fits in a field element.

(define bits-mul-field-gadget ((xs symbol-listp)
                               (ys symbol-listp)
                               (z symbolp)
                               (p primep))
  :guard (< (+ (len xs) (len ys))
            (integer-length p))
  (declare (ignore p))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (pow2sum-vector xs 0)
         :b (pow2sum-vector ys 0)
         :c (list (list 1 z)))))

; We prove that the gadget is equivalent to
; z being the product of xs and ys,
; where xs and ys are in little endian order.

(defruled bits-mul-field-gadget-to-equal-of-mul
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (< (+ (len xs) (len ys))
                   (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (bits-mul-field-gadget xs ys z p) asg p)
                             (equal z$ (* (lebits=>nat xs$)
                                          (lebits=>nat ys$)))))))
  :do-not-induct t
  :use ((:instance times-expt2-upper-bound
                   (a (lebits=>nat (lookup-equal-list xs asg)))
                   (b (lebits=>nat (lookup-equal-list ys asg)))
                   (n (len xs))
                   (m (len ys)))
        (:instance expt2-mono
                   (a (+ (len xs) (len ys)))
                   (b (1- (integer-length p)))))
  :enable (bits-mul-field-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pfield::mul
           positive->=-expt2-of-integer-length-minus-1))

; The size in bits of the resulting field element
; does not exceed the sum of the lengths of the two operands.
; This is an additional property of this gadget,
; which is useful to prove properties of gadgets
; that include this gadget as a sub-gadget.

(defruled bits-mul-field-gadget-integer-length
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (< (+ (len xs) (len ys))
                   (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (bits-mul-field-gadget xs ys z p) asg p)
                               (<= (integer-length z$)
                                   (+ (len xs) (len ys)))))))
  :do-not-induct t
  :cases ((<= (lookup-equal z asg) (1- (expt 2 (+ (len xs) (len ys))))))
  :use (bits-mul-field-gadget-to-equal-of-mul
        (:instance times-expt2-upper-bound
                   (a (lebits=>nat (lookup-equal-list xs asg)))
                   (b (lebits=>nat (lookup-equal-list ys asg)))
                   (n (len xs))
                   (m (len ys)))
        (:instance integer-length-mono
                   (a (lookup-equal z asg))
                   (b (1- (expt 2 (+ (len xs) (len ys)))))))
  :enable integer-length-of-expt2-minus-1
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)))
