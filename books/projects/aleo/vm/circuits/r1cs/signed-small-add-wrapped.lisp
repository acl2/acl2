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

(include-book "unsigned-small-add-wrapped")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the same as unsigned-small-add-wrapped (same snarkVM code),
; because of the properties of two's complement arithmetic.

(define signed-small-add-wrapped-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (zs symbol-listp)
                                         (z symbolp)
                                         (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-add-wrapped-gadget xs ys zs z p))

; The soundness proof follows from the one of unsigned-small-add-wrapped,
; and from the definition of lebits=>int.
; The modulo operation on the (possibly negative) addends x and y
; yields a value that is always non-negative;
; so we need to apply the modulo operation to the results z too,
; in order to equate them.
; This is essentially the specification of signed wrapped addition:
; that the modulo of the result is the modulo of the sum.
; Maybe there is a better formulation of this specification.

(defruled signed-small-add-wrapped-gadget-soundness
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-add-wrapped-gadget xs ys zs z p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (mod (lebits=>int zs$)
                                                (expt 2 (len zs)))
                                           (mod (+ (lebits=>int xs$)
                                                   (lebits=>int ys$))
                                                (expt 2 (len zs)))))))))
  :do-not-induct t
  :use unsigned-small-add-wrapped-gadget-soundness
  :enable (signed-small-add-wrapped-gadget
           lebits=>int))
