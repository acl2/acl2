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

(include-book "bits-mul-field")
(include-book "field-bits-add-bits")
(include-book "unsigned-small-lt")
(include-book "zero")

(local (include-book "../library-extensions/arithmetic"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (in-theory (disable integer-length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget divides two unsigned integers,
; calculating their quotient and remainder.
; The dividend and divisor are expressed in bits, xs and ys.
; The gadget introduces bits qs and rs for quotient and remainder,
; and sets up the well-known Euclidean equation
;   <dividend> = <divisor> * <quotient> + <remainder>
; It does so using two gadgets,
; one that multiplies ys by qs and puts the result into a field element m,
; and one the adds m to the remainder rs and puts the result into xs.
; Finally it constrains the remainder rs to be less than the divisor ys,
; by calculating the result of the comparison into d (with auxiliary ds),
; and constraining it to be 0.
; The zero gadget is the one with the public unit variable
; that must be assumed to be 0.

; An earlier version of this gadget started with a sub-gadget
; to check that the divisor is not 0.
; However, that check was subsumed by the constraint that
; the remainder is less than the divisor,
; which implies that the divisor is greater than 0.
; Thus, that redundant sub-gadget was removed, optimizing the construction.

(define unsigned-small-div-gadget ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (qs symbol-listp)
                                   (rs symbol-listp)
                                   (m symbolp)
                                   (ds symbol-listp)
                                   (d symbolp)
                                   (u symbolp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ds) (len xs))
              (consp xs)
              (< (1+ (* 2 (len xs))) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list qs p)
          (boolean-check-gadget-list rs p)
          (bits-mul-field-gadget qs ys m p)
          (field-bits-add-bits-gadget m rs xs p)
          (unsigned-small-lt-gadget rs ys ds d p)
          (zero-unit-gadget d u p)))

; We show that the gadget indeed implies
; the Euclidian formulation of division.

(defruled unsigned-small-div-gadget-euclidian
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (equal (len ys) (len xs))
                (equal (len qs) (len xs))
                (equal (len rs) (len xs))
                (equal (len ds) (len xs))
                (consp xs)
                (< (1+ (* 2 (len xs))) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (qs$ (lookup-equal-list qs asg))
                (rs$ (lookup-equal-list rs asg))
                (u$ (lookup-equal u asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal u$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-div-gadget
                                 xs ys qs rs m ds d u p)
                                asg
                                p)
                               (and (bit-listp qs$)
                                    (bit-listp rs$)
                                    (not (equal (lebits=>nat ys$) 0))
                                    (equal (lebits=>nat xs$)
                                           (+ (* (lebits=>nat qs$)
                                                 (lebits=>nat ys$))
                                              (lebits=>nat rs$)))
                                    (< (lebits=>nat rs$)
                                       (lebits=>nat ys$)))))))
  :do-not-induct t
  :enable (unsigned-small-div-gadget
           boolean-check-gadget-list-to-bit-listp
           bits-mul-field-gadget-to-equal-of-mul
           field-bits-add-bits-gadget-to-add
           zero-unit-gadget-to-equal-0)
  :use ((:instance bits-mul-field-gadget-integer-length
                   (xs qs) (ys ys) (z m))
        (:instance unsigned-small-lt-gadget-soundness
                   (xs rs) (ys ys) (zs ds) (z d))))

; We prove the soundness of the gadget by saying that
; its satisfaction implies
; that qs is indeed the quotient,
; as expressed by truncate or floor,
; and that rs is indeed the remainder,
; as expressed by rem or mod.
; The proof is very simple, using arithmetic theorems
; that relates the Euclidian formulation to floor and rem.

(defruled unsigned-small-div-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp m)
                (symbol-listp ds)
                (symbolp d)
                (symbolp u)
                (equal (len ys) (len xs))
                (equal (len qs) (len xs))
                (equal (len rs) (len xs))
                (equal (len ds) (len xs))
                (consp xs)
                (< (1+ (* 2 (len xs))) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg u))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (qs$ (lookup-equal-list qs asg))
                (rs$ (lookup-equal-list rs asg))
                (u$ (lookup-equal u asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal u$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-div-gadget
                                 xs ys qs rs m ds d u p)
                                asg
                                p)
                               (and
                                (equal (lebits=>nat qs$)
                                       (truncate (lebits=>nat xs$)
                                                 (lebits=>nat ys$)))
                                (equal (lebits=>nat qs$)
                                       (floor (lebits=>nat xs$)
                                              (lebits=>nat ys$)))
                                (equal (lebits=>nat rs$)
                                       (rem (lebits=>nat xs$)
                                            (lebits=>nat ys$)))
                                (equal (lebits=>nat rs$)
                                       (mod (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :use (unsigned-small-div-gadget-euclidian
        (:instance truncate-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg))))
        (:instance floor-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg))))
        (:instance rem-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg))))
        (:instance mod-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg)))))
  :disable (truncate floor rem mod))
