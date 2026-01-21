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

(include-book "unsigned-small-sub")
(include-book "one")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the checked version of unsigned small subtraction.
; It is similar to unsigned-small-add-checked in structure:
; it consists of unsigned-small-sub,
; where it splits the result bits into the low n and high one,
; and of a one gadget that requires the high bit to be 1.

; Recall that the correctness theorem for unsigned-small-sub says that
; that gadget is equivalent to zs.z = xs - ys + 2^64.
; If z is 1, it cancels with 2^64, leaving zs = xs - ys.

(define unsigned-small-sub-checked-gadget ((xs symbol-listp)
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
  (append (unsigned-small-sub-gadget xs ys (append zs (list z)) one p)
          (one-gadget z)))

(defruled unsigned-small-sub-checked-gadget-correct
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
                (z$ (lookup-equal z asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-sub-checked-gadget
                               xs ys zs z one p)
                              asg
                              p)
                             (and (bit-listp zs$)
                                  (equal z$ 1)
                                  (equal (lebits=>nat zs$)
                                         (- (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :enable (unsigned-small-sub-checked-gadget
           unsigned-small-sub-gadget-correct
           unsigned-small-sub-opt-gadget-correct
           one-gadget-to-equal-1
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append))
