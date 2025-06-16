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

(include-book "unsigned-medium-mul-carry")
(include-book "zero")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is based on unsigned-medium-mul-carry-gadget.
; This gadget adds a zero check for the carry bits,
; which means that we check that the product of the n-bit xs and ys
; fits in n bits.
; Here we assume, as in unsigned-medium-mul.lisp,
; that n is sufficiently small w.r.t. the bit length of p.
; This is a 'medium' size;
; see unsigned-small-mul-checked.lisp for 'small' size.

(define unsigned-medium-mul-checked-gadget ((xs symbol-listp)
                                            (ys symbol-listp)
                                            (low-low symbolp)
                                            (high-low symbolp)
                                            (low-high symbolp)
                                            (high-high symbolp)
                                            (zs symbol-listp)
                                            (zs-carry-low symbol-listp)
                                            (zs-carry-high symbol-listp)
                                            (p primep))
  :guard (and (< 0 (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-carry-low) (1+ (floor (len xs) 2)))
              (equal (len zs-carry-high) (len xs))
              (< (len (append zs zs-carry-low)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (unsigned-medium-mul-carry-gadget xs
                                            ys
                                            low-low
                                            high-low
                                            low-high
                                            high-high
                                            zs
                                            zs-carry-low
                                            zs-carry-high
                                            p)
          (zero-gadget-list zs-carry-low)
          (zero-gadget-list zs-carry-high)))

; We prove soundness.
; The gadget implies that
; (1) the zs are bits, and
; (2) the zs is the product of xs and ys.

(defruled unsigned-medium-mul-checked-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp low-low)
                (symbolp high-low)
                (symbolp low-high)
                (symbolp high-high)
                (symbol-listp zs)
                (symbol-listp zs-carry-low)
                (symbol-listp zs-carry-high)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (equal (len zs-carry-low) (1+ (floor (len xs) 2)))
                (equal (len zs-carry-high) (len xs))
                (< (len (append zs zs-carry-low)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-carry-low)
                (r1cs::valuation-binds-allp asg zs-carry-high))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-medium-mul-checked-gadget
                                 xs ys low-low high-low low-high high-high
                                 zs zs-carry-low zs-carry-high p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (lebits=>nat zs$)
                                           (* (lebits=>nat xs$)
                                              (lebits=>nat ys$))))))))
  :do-not-induct t
  :use unsigned-medium-mul-carry-gadget-soundness
  :enable (unsigned-medium-mul-checked-gadget
           zero-gadget-list-to-all-equal-0))
