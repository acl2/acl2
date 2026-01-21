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

(include-book "unsigned-small-mul-carry")
(include-book "zero")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is based on unsigned-small-mul-carry-gadget.
; This gadget adds a zero check for the high half of zs (high-zs),
; which means that we check that the product of the n-bit xs and ys
; fits in n bits.
; Here we assume, as in unsigned-small-mul(-carry).lisp,
; that n is sufficiently small w.r.t. the bit length of p.

(define unsigned-small-mul-checked-gadget ((xs symbol-listp)
                                           (ys symbol-listp)
                                           (zvar symbolp)
                                           (zs symbol-listp)
                                           (carry symbol-listp)
                                           (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len carry) (len xs))
              (< (* 2 (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (unsigned-small-mul-carry-gadget xs ys zvar zs carry p)
          (zero-gadget-list carry)))

; We prove soundness.
; The gadget implies that
; (1) the zs are bits, and
; (2) the zs is the product of xs and ys.

(defruled unsigned-small-mul-checked-soundness
  (implies (and (primep p)
                (< (* 2 (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp zvar)
                (symbol-listp zs)
                (symbol-listp carry)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (equal (len carry) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg zvar)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg carry))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-mul-checked-gadget
                                 xs ys zvar zs carry p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (lebits=>nat zs$)
                                           (* (lebits=>nat xs$)
                                              (lebits=>nat ys$))))))))
  :do-not-induct t
  :enable (unsigned-small-mul-checked-gadget
           unsigned-small-mul-carry-gadget-correct
           zero-gadget-list-to-all-equal-0))
