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

(include-book "unsigned-small-sub-wrapped-const-var")

(include-book "../library-extensions/digits")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/r1cses"))

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a variant of the signed-small-sub-wrapped gadget
; in which the first operand is a constant,
; expressed as a list of constant bits.
; The definitions and theorems are essentially the same,
; except for having the bits cs instead of the variables xs.

(define signed-small-sub-wrapped-const-var-gadget ((cs bit-listp)
                                                   (ys symbol-listp)
                                                   (zs symbol-listp)
                                                   (z symbolp)
                                                   (one symbolp)
                                                   (p primep))
  :guard (and (consp cs)
              (equal (len ys) (len cs))
              (equal (len zs) (len cs))
              (< (1+ (len cs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-sub-wrapped-const-var-gadget cs ys zs z one p))

(defruled signed-small-sub-wrapped-const-var-gadget-soundness
  (implies (and (primep p)
                (bit-listp cs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp one)
                (consp cs)
                (equal (len ys) (len cs))
                (equal (len zs) (len cs))
                (< (1+ (len cs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one))
           (b* ((ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-sub-wrapped-const-var-gadget
                                 cs ys zs z one p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (mod (lebits=>int zs$)
                                                (expt 2 (len zs)))
                                           (mod (- (lebits=>int cs)
                                                   (lebits=>int ys$))
                                                (expt 2 (len zs)))))))))
  :do-not-induct t
  :use unsigned-small-sub-wrapped-const-var-gadget-soundness
  :enable (signed-small-sub-wrapped-const-var-gadget
           lebits=>int))
