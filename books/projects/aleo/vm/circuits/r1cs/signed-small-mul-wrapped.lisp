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

(include-book "unsigned-small-mul-wrapped")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the same as unsigned-small-mul-wrapped (same snarkVM code),
; because of the properties of two's complement arithmetic.

(define signed-small-mul-wrapped-gadget ((xs symbol-listp)
                                         (ys symbol-listp)
                                         (lowlow symbolp)
                                         (highlow symbolp)
                                         (lowhigh symbolp)
                                         (zs symbol-listp)
                                         (zs-high symbol-listp)
                                         (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-high) (1+ (floor (len xs) 2)))
              (< (len (append zs zs-high)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-mul-wrapped-gadget xs ys lowlow highlow lowhigh zs zs-high p))

; The soundness proof follows from the one of unsigned-small-mul-wrapped,
; and from the definition of lebits=>int.
; The modulo operation on the (possibly negative) addends x and y
; yields a value that is always non-negative;
; so we need to apply the modulo operation to the results z too,
; in order to equate them.
; This is essentially the specification of signed wrapped addition:
; that the modulo of the result is the modulo of the sum.
; Maybe there is a better formulation of this specification.

(defruled signed-small-mul-wrapped-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp lowlow)
                (symbolp highlow)
                (symbolp lowhigh)
                (symbol-listp zs)
                (symbol-listp zs-high)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (equal (len zs-high) (1+ (floor (len xs) 2)))
                (< (len (append zs zs-high)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-mul-wrapped-gadget
                                 xs ys lowlow highlow lowhigh zs zs-high p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (mod (lebits=>int zs$)
                                                (expt 2 (len xs)))
                                           (mod (* (lebits=>int xs$)
                                                   (lebits=>int ys$))
                                                (expt 2 (len xs)))))))))
  :do-not-induct t
  :use unsigned-small-mul-wrapped-gadget-soundness
  :enable (signed-small-mul-wrapped-gadget
           lebits=>int))
