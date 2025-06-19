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

(include-book "unsigned-small-neq")

(include-book "../library-extensions/digits")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget checks whether two signed integers are not equal.
; The integers are given as bits xs and ys of the same length.
; The result is z: 1 if xs and ys differ; 0 if xs and ys are equal.

; This gadget is identical to unsigned-small-neq,
; but here we interpret the integers via lebits=>int
; instead of via lebits=>nat as in unsigned-small-neq.
; This interpretation does not appear in the gadget definition,
; but in the soundness theorem below.

(define signed-small-neq-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (z symbolp)
                                 (w symbolp)
                                 (one symbolp)
                                 (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-neq-gadget xs ys z w one p))

; Soundness follows directly from the soundness of unsigned-small-neq,
; and from the injectivity of lebits=>int and lebits=>nat.

(defruled signed-small-neq-gadget-soundness
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
                                (unsigned-small-neq-gadget xs ys z w one p)
                                asg
                                p)
                               (equal z$ (if (equal (lebits=>int xs$)
                                                    (lebits=>int ys$))
                                             0
                                           1))))))
  :do-not-induct t
  :enable signed-small-neq-gadget
  :use unsigned-small-neq-gadget-soundness)
