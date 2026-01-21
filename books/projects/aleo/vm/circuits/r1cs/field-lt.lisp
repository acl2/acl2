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

(include-book "field-to-bits")
(include-book "bits-lt")
(include-book "bits-lt-prime")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field less-than gadget calculates whether
; a field X is less than a field Y or not.
; The gadget works by decomposing X and Y into bits XS and YS,
; while using XRS and YRS, respectively, as intermediate variables that ensure
; the decompositions XS and YS represent numbers less than the prime P,
; and then doing a bitwise comparison between XS and YS;
; the result is the last bit in RS
; (see the bitwise comparison gadget bits-lt-gadget).

(define field-lt-gadget ((x symbolp)
                             (xs symbol-listp)
                             (xrs symbol-listp)
                             (y symbolp)
                             (ys symbol-listp)
                             (yrs symbol-listp)
                             (ds symbol-listp)
                             (rs symbol-listp)
                             (u symbolp) ; unit var
                             (p primep))
  :guard (and (oddp p)
              (equal (len xs) (integer-length p))
              (equal (len xrs) (bits-lt-prime-rlen p))
              (equal (len ys) (integer-length p))
              (equal (len yrs) (bits-lt-prime-rlen p))
              (equal (len ds) (integer-length p))
              (equal (len rs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (field-to-bits-gadget x xs xrs u p)
          (field-to-bits-gadget y ys yrs u p)
          (bits-lt-gadget xs ys ds rs p)))

(defruled field-lt-gadget-soundness
  (implies (and (symbolp x)
                (symbol-listp xs)
                (symbol-listp xrs)
                (symbolp y)
                (symbol-listp ys)
                (symbol-listp yrs)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (integer-length p))
                (equal (len xrs) (bits-lt-prime-rlen p))
                (equal (len ys) (integer-length p))
                (equal (len yrs) (bits-lt-prime-rlen p))
                (equal (len ds) (integer-length p))
                (equal (len rs) (integer-length p))
                (primep p)
                (oddp p)
                (symbolp u)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg xrs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg yrs)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg u))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (rs$ (lookup-equal-list rs asg))
                (u$ (lookup-equal u asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-lt-gadget x xs xrs y ys yrs ds rs u p) asg p)
                      (implies (equal u$ 1)
                               (iff (< x$ y$)
                                    (equal (car (last rs$)) 1))))))
  :do-not-induct t
  :use ((:instance field-to-bits-soundness
                   (x x) (xs xs) (rs xrs) (u u) (p p))
        (:instance field-to-bits-soundness
                   (x y) (xs ys) (rs yrs) (u u) (p p))
        (:instance bits-lt-gadget-to-<-lendian-iff-bit1
                   (xs xs) (ys ys) (ds ds) (rs rs) (p p)))
  :enable (field-lt-gadget))
