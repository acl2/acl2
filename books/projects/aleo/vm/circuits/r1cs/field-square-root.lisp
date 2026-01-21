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

(include-book "bits-lte-const-check")
(include-book "boolean-check")
(include-book "field-square")
(include-book "pow2sum")

(local (include-book "../library-extensions/digits"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget constrains y to be the non-negative square root of x,
; assuming that x is a square.
; In a prime field, an element has
; either no square roots
; or one 0 square root (if the element is 0),
; or two non-zero roots of opposite sign;
; in a prime field, the sign really indicates whether the element is
; in the lower or upper "half":
;
;   0 1 2 ... (p-1)/2 (p-1)/2+1 ... p-1
;     --------------- -----------------
;     lower/positive  upper/negative
;     half            half
;
; As with regular integers, 0 is neither positive nor negative.
; Thus, if we are interested in a square root that is either 0 or positive,
; we describe that as non-negative root, as done above.

; This gadget uses the square constraint to require y to be a square root,
; but that may be either positive or negative if not 0.
; Thus, the gadget includes further constraints to turn y into bits ys,
; and to check that their integer (not prime field) value
; is in the lower/positive half or 0,
; i.e. that it is <= (p-1)/2.
; We assume that p is odd, i.e. not 2, so (p-1)/2 is a positive integer.

(define field-square-root-bound ((p primep))
  :guard (oddp p)
  :returns (bound posp
                  :hyp :guard
                  :rule-classes (:rewrite :type-prescription))
  (/ (1- p) 2)
  :prepwork ((local (in-theory (enable oddp)))
             (local (include-book "arithmetic-3/top" :dir :system))))

(define field-square-root-rlen ((p primep))
  :guard (oddp p)
  :returns (rlen natp)
  (bits-lte-const-check-rlen (nat=>lebits* (field-square-root-bound p)))
  :guard-hints (("Goal" :in-theory (enable nat=>lebits*-msb-is-1)))
  :prepwork
  ((local (in-theory (disable natp)))
   (defrulel natp-when-posp (implies (posp x) (natp x)))))

(define field-square-root-gadget ((x symbolp)
                                  (y symbolp)
                                  (ys symbol-listp)
                                  (rs symbol-listp)
                                  (p primep))
  :guard (and (oddp p)
              (equal (len ys) (integer-length p))
              (equal (len rs) (field-square-root-rlen p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (field-square-gadget y x)
          (boolean-check-gadget-list ys p)
          (pow2sum-gadget y ys)
          (bits-lte-const-check-gadget
           ys (nat=>lebits* (field-square-root-bound p)) rs p))
  :prepwork
  ((local (in-theory (e/d (field-square-root-rlen nat=>lebits*-msb-is-1)
                          (natp))))
   (defrulel natp-when-posp
     (implies (posp x)
              (natp x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; If the gadget holds, then y is a non-negative square root of x.
; We express it by saying it that
; (1) the square of y is x and
; (2) y does not exceed (p-1)/2.
; We should probably rephrase this in terms of
; a function that returns the non-negative square root if given a square.
; This function does not need to be executable,
; since we use it for specification.
; At the time we do not quite seem to have such a function in the ACL2 library,
; but we plan to add one and to use it here.

(defruled field-square-root-soundness
  (implies (and (primep p)
                (oddp p)
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp rs)
                (equal (len ys) (integer-length p))
                (equal (len rs) (field-square-root-rlen p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-square-root-gadget x y ys rs p) asg p)
                      (and (equal (pfield::mul y$ y$ p) x$)
                           (<= y$ (field-square-root-bound p))))))
  :do-not-induct t
  :enable (field-square-root-gadget
           field-square-gadget-correctness
           boolean-check-gadget-list-to-bit-listp
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           field-square-root-rlen
           nat=>lebits*-msb-is-1)
  :use (:instance bits-lte-const-check-soundness
                  (xs ys)
                  (cs (nat=>lebits* (field-square-root-bound p)))))
