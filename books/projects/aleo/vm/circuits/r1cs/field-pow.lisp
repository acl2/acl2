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
(include-book "field-pow-bits")

(local (in-theory (disable integer-length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; field**field gadget, using the new field-to-bits sub-gadget

; This splits the exponent into bits and then uses field-pow-bits-gadget.

; Note that ys and the other sequences are in little endian order,
; as in the field-pow-bits gadget.
; This facilitates the proofs,
; because we don't need to take reversing into account
; to use the soundness proof of the field-pow-bits gadget.

(define field-pow-gadget
  ((x symbolp) ; base (field var)
   (y symbolp) ; exponent (field var)
   ;; see filed-pow-bits.lisp for more detail
   ;; on these var lists:
   (ys symbol-listp) ; exponent bit vars split from y
                     ; in little-endian, meaning (car ys) is the 1s bit
   (zs symbol-listp) ; internal bits of field-to-bits gadget
   (ss symbol-listp) ; squares bit vars
   (ps symbol-listp) ; products bit vars
   (rs symbol-listp) ; results field vars, the last
                     ; of which is the return value var
   (unitvar symbolp)
   (p primep))
  :returns (constraints r1cs::r1cs-constraint-listp
                        :hyp :guard
                        :hints (("Goal" :cases ((consp ys)))))

  :guard (and (oddp p)
              (equal (len ys) (integer-length p))
              (equal (len zs) (bits-lt-prime-rlen p))
              (equal (len rs) (len ys))
              (equal (len ss) (1- (len ys)))
              (equal (len ps) (1- (len ys))))

  ; x does not need to be bitified.
  ; Let n > 0 be the number of bits of p.
  ; There are n vars for y's bits.

  (append
   (field-to-bits-gadget y ys zs unitvar p)
   (field-pow-bits-gadget x ys ss ps rs p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness is proved from the soundness theorems of the sub-gadgets.

(defruled field-pow-soundness
  (implies (and (primep p)
                (oddp p)
                (symbolp unitvar)
                (symbolp x)
                (symbolp y)
                (symbol-listp ys)
                (equal (len ys) (integer-length p))
                (symbol-listp zs)
                (equal (len zs) (bits-lt-prime-rlen p))
                (symbol-listp rs)
                (equal (len rs) (len ys))
                (symbol-listp ss)
                (equal (len ss) (1- (len ys)))
                (symbol-listp ps)
                (equal (len ps) (1- (len ys)))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg unitvar)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg ps))
           (b* ((unitvar$ (lookup-equal unitvar asg))
                (x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-pow-gadget x y ys zs ss ps rs unitvar p) asg p)
                      (implies (equal unitvar$ 1)
                               (equal (car rs$)
                                      (pfield::pow x$ y$ p))))))
  :do-not-induct t
  :enable (field-pow-gadget)
  :use ((:instance field-to-bits-soundness
                   (x y) (xs ys) (rs zs) (u unitvar))
        field-pow-bits-soundness))
