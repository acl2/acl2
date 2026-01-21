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

(include-book "unsigned-small-add")
(include-book "zero")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is based on unsigned-small-add-gadget.
; The bits that form the sum in that gadget are split into
; the low n bits zs and the high bit z.
; This gadget adds a zero check for z,
; which means that we check that the sum of the n-bit xs and ys
; fits in n bits.
; Here we assume, as in unsigned-small-add,
; that n is sufficiently small w.r.t. the bit length of p.

(define unsigned-small-add-checked-gadget ((xs symbol-listp)
                                           (ys symbol-listp)
                                           (zs symbol-listp)
                                           (z symbolp)
                                           (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (unsigned-small-add-gadget xs ys (append zs (list z)) p)
          (zero-gadget z)))

; We prove soundness and completeness.
; The gadget is equivalent to
; (1) the zs being bits,
; (2) z being 0, and
; (3) zs being the sum of xs and ys.

(defruled unsigned-small-add-checked-gadget-correct
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
                (zs$ (lookup-equal-list zs asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-add-checked-gadget xs ys zs z p)
                              asg
                              p)
                             (and (bit-listp zs$)
                                  (equal z$ 0)
                                  (equal (lebits=>nat zs$)
                                         (+ (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :enable (unsigned-small-add-checked-gadget
           unsigned-small-add-gadget-correct
           zero-gadget-to-equal-0
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append))
