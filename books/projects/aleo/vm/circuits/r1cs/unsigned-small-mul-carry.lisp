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

(include-book "unsigned-small-mul")

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget multiplies two unsigned integers,
; represented as bits xs and ys with the same length n,
; and puts the result into the bits zlow and zhigh, each of length n.
; So zlow can be thought of the n-bit result, and zhigh as the n-bit carry.
; This corresponds to the snarkVM code in the mul_with_carry() function,
; for Case 1 as described in the comments in that function.

; Formally, this gadget is defined just like the base gadget unsigned-small-mul,
; but with zs replaced with (append zlow zhigh);
; recall that all the bits here are in little endian order.

(define unsigned-small-mul-carry-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zvar symbolp)
                                         (zlow symbol-listp)
                                         (zhigh symbol-listp)
                                         (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zlow) (len xs))
              (equal (len zhigh) (len xs))
              (< (+ (len zlow) (len zhigh))
                 (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-mul-gadget xs ys zvar (append zlow zhigh) p))

; We prove soundness and completeness,
; This follows faily easily from the correctness theorem of unsigned-small-mul.
; We need the rule about lebits=>nat and append, unsurprisingly.

(defruled unsigned-small-mul-carry-gadget-correct
  (implies (and (primep p)
                (< (* 2 (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp zvar)
                (symbol-listp zlow)
                (symbol-listp zhigh)
                (equal (len ys) (len xs))
                (equal (len zlow) (len xs))
                (equal (len zhigh) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg zvar)
                (r1cs::valuation-binds-allp asg zlow)
                (r1cs::valuation-binds-allp asg zhigh))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zvar$ (lookup-equal zvar asg))
                (zlow$ (lookup-equal-list zlow asg))
                (zhigh$ (lookup-equal-list zhigh asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-mul-carry-gadget
                               xs ys zvar zlow zhigh p)
                              asg
                              p)
                             (and (equal zvar$
                                         (+ (lebits=>nat zlow$)
                                            (* (expt 2 (len xs))
                                               (lebits=>nat zhigh$))))
                                  (bit-listp zlow$)
                                  (bit-listp zhigh$)
                                  (equal zvar$
                                         (* (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :enable (unsigned-small-mul-carry-gadget
           unsigned-small-mul-gadget-correct
           lookup-equal-list-of-append
           acl2::lebits=>nat-of-append))
