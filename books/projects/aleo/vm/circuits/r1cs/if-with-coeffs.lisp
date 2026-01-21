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

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/bind-free-rules" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/prime-fields/minus1" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A ternary conditional gadget,
; which constrains w to be either j.y or k.z,
; (for any field elements j and k)
; based on whether x (assumed boolean) is 1 or 0.

; The main version of this gadget has different vars y and z.
; There is also a version that simplifies the constraint when y and z are the
; same var (but with different coefficients).

; Although this gadget does not follow directly from a single Aleo instruction,
; since multiplying by a coefficient would be a separate instruction,
; this gadget does come up as a component when decomposing more complex
; gadgets.  (Actually, the THEN and ELSE clauses could be entire linear
; combinations, but we will handle that later using PFCS.)

; Also note, this gadget might not yield the same constraint as snarkVM when
; j=0 and/or k=0, but that guard will complicate things here.
; We might want to define more specialized gadgets for these cases.

; There is a single constraint equivalent to
;   (x) (jy + k(p-1)z) = (w + k(p-1)z)
; i.e.
;   (x) (jy - kz) = (w - kz)
; Thus, if x = 0, we have w - kz = 0, i.e. w = kz;
; while, if x = 1, we have jy - kz = w - kz, i.e. w = jy.

(define if-with-coeffs-gadget ((x symbolp) ; condition bit var
                               (j (pfield::fep j p)) ; coeff of y
                               (y symbolp) ; THEN var
                               (k (pfield::fep k p)) ; coeff of z
                               (z symbolp) ; ELSE var
                               (w symbolp) ; value var
                               (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list j y)
                  (list (pfield::mul k (1- p) p) z))
         :c (list (list 1 w)
                  (list (pfield::mul k (1- p) p) z)))))

; The gadget is equivalent to its specification,
; written in terms of the built-in function IF.
; assuming that x is boolean.

(defruled if-with-coeffs-gadget-to-if
  (implies (and (symbolp x)
                (pfield::fep j p)
                (symbolp y)
                (pfield::fep k p)
                (symbolp z)
                (symbolp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (w$ (lookup-equal w asg)))
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-with-coeffs-gadget x j y k z w p) asg p)
                             (equal w$ (if (= x$ 1)
                                           (pfield::mul j y$ p)
                                         (pfield::mul k z$ p)))))))
  :enable (if-with-coeffs-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialized version of the IF gadget
; with the THEN and ELSE vars being the same,
; although with different coefficients.

; This version of a ternary conditional gadget,
; constrains w to be either j.y or k.y,
; (for any field elements j and k),
; based on whether x (assumed boolean) is 1 or 0.

; There is a single constraint equivalent to
;   (x) (jy + k(p-1)y) = (w + k(p-1)y)
; i.e.
;   (x) ((j - k).y) = (w - k.y)
; Thus, if x = 0, we have (w - ky) = 0, i.e. w = ky;
; while, if x = 1, we have (j - k)y = w - ky, i.e. w = jy.

; There is one refinement when j=k;
; in this case the :b linear combination is simplified to the empty lc.

; Also note, this gadget might not yield the same constraint as SnarkVM when
; j=0 and/or k=0, but that guard will complicate things here.
; We might want to define more specialized gadgets for these cases.

(define if-with-coeffs-samevar-gadget ((x symbolp) ; condition bit var
                                       (j (pfield::fep j p)) ; THEN coeff of y
                                       (y symbolp) ; THEN var and ELSE var
                                       (k (pfield::fep k p)) ; ELSE coeff of y
                                       (w symbolp) ; value var
                                       (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (if (= j k)
                (list )
              (list (list (pfield::sub j k p) y)))
         :c (list (list 1 w)
                  (list (pfield::mul k (1- p) p) y)))))

; The gadget is equivalent to its specification,
; written in terms of the built-in function IF.
; assuming that x is boolean.

(defruled if-with-coeffs-samevar-gadget-to-if
  (implies (and (symbolp x)
                (pfield::fep j p)
                (symbolp y)
                (pfield::fep k p)
                (symbolp w)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg w))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (w$ (lookup-equal w asg)))
             (implies (bitp x$)
                      (equal (r1cs::r1cs-constraints-holdp
                              (if-with-coeffs-samevar-gadget x j y k w p) asg p)
                             (equal w$ (if (= x$ 1)
                                           (pfield::mul j y$ p)
                                         (pfield::mul k y$ p)))))))
  :enable (if-with-coeffs-samevar-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))
