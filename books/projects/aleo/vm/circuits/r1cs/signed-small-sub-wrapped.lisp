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

(include-book "unsigned-small-sub-wrapped")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the same as unsigned-small-sub-wrapped (same snarkVM code),
; because of the properties of two's complement arithmetic.

(define signed-small-sub-wrapped-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (z symbolp)
                                         (one symbolp)
                                         (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-sub-wrapped-gadget xs ys zs z one p))

; The soundness proof follows from the one of unsigned-small-sub-wrapped,
; and from the definition of lebits=>int.
; The modulo operation on the (possibly negative) minuend x and subtrahend y
; yields a value that is always non-negative;
; so we need to apply the modulo operation to the results z too,
; in order to equate them.
; This is essentially the specification of signed wrapped subtraction:
; that the modulo of the result is the modulo of the difference.
; Maybe there is a better formulation of this specification.

(defruled signed-small-sub-wrapped-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-sub-wrapped-gadget
                                 xs ys zs z one p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (mod (lebits=>int zs$)
                                                (expt 2 (len zs)))
                                           (mod (- (lebits=>int xs$)
                                                   (lebits=>int ys$))
                                                (expt 2 (len zs)))))))))
  :do-not-induct t
  :use unsigned-small-sub-wrapped-gadget-soundness
  :enable (signed-small-sub-wrapped-gadget
           lebits=>int))
