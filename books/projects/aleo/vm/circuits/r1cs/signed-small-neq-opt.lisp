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

(include-book "unsigned-small-neq-opt")

(include-book "../library-extensions/digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is an optimized version of signed-small-neq,
; which omits the constraint to make z a boolean.
; That constraint is unnecessary, because the other two constraints
; imply that r must be either 0 or 1,
; similarly to field-neq.

(define signed-small-neq-opt-gadget ((xs symbol-listp)
                                     (ys symbol-listp)
                                     (z symbolp)
                                     (w symbolp)
                                     (one symbolp)
                                     (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-neq-opt-gadget xs ys z w one p))

(defruled signed-small-neq-opt-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal (len ys) (len xs))
                (< (len xs) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-neq-opt-gadget xs ys z w one p)
                                asg
                                p)
                               (equal z$ (if (equal (lebits=>int xs$)
                                                    (lebits=>int ys$))
                                             0
                                           1))))))
  :do-not-induct t
  :enable signed-small-neq-opt-gadget
  :use unsigned-small-neq-opt-gadget-soundness)
