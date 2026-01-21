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

(include-book "boolean-xor")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget calculates the bitwise 'xor' of two integers.
; It is the same for signed and unsigned intgers.

(define integer-xor-gadget ((xs symbol-listp)
                            (ys symbol-listp)
                            (zs symbol-listp)
                            (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (boolean-xor-gadget-list xs ys zs p))

(defruled integer-xor-to-bitxor-list
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (integer-xor-gadget xs ys zs p) asg p)
                             (equal zs$ (bitxor-list xs$ ys$))))))
  :enable (integer-xor-gadget
           boolean-xor-gadget-list-to-bitxor-list))
