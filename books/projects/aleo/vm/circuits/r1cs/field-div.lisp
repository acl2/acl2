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

(include-book "field-inverse")
(include-book "field-mul")

(local (include-book "std/lists/list-fix" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field division gadget consists of two constraints
;   (y) (w) = (1)
;   (x) (w) = (z)
; where x is the dividend, y is the divisor, z is the quotient,
; and w is an intermediate variable constrained to be the inverse of y,
; so that multiplying x by w yields x divided by y.
; The calculation works assuming that y is not 0.
; We build this gadget from the field inversion and multiplication gadgets.

(define field-div-gadget ((x symbolp) (y symbolp) (z symbolp) (w symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (field-inverse-gadget y w)
          (field-mul-gadget x w z)))

(defruled field-div-gadget-soundness
  (implies (and (symbolp x)
                (symbolp y)
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
                (z$ (lookup-equal z asg)))
             (implies (not (equal y$ 0))
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-div-gadget x y z w) asg p)
                               (equal z$ (pfield::div x$ y$ p))))))
  :enable (field-div-gadget
           field-inverse-gadget-to-equal-inverse
           field-mul-gadget-correctness
           pfield::div)
  :disable pfield::equal-of-inv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Experiment: try a specification that uses defresult to handle the errors.

(include-book "kestrel/fty/integer-result" :dir :system)
; defines integer-resultp
; (in ACL2 package, which is imported into the current package)

; This should be in prime-field-rules.
(defrule fep-of-div
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p)
                (not (= y 0)))
           (pfield::fep (pfield::div x y p) p)))

; This is the specification of the field division opcode,
; handling the case of division by zero by returning an Err,
; matching the developer view of the semantics of the opcode.
(define field-div-spec (x y p)
  :guard (and (primep p)
              (pfield::fep x p)
              (pfield::fep y p))
  :returns (z-or-err integer-resultp)
  (if (= y 0)
      (reserr 0)
    (pfield::div x y p)))

; Explicate the domain and range of the spec function.
; Spec function does not return an error:
(defruled field-div-spec-returns-fep-for-y-not-equal-zero
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p))
           (iff (pfield::fep (field-div-spec x y p) p)
                (not (equal y 0))))
  :enable (field-div-spec))

; Spec function does return an error:
(defruled field-div-spec-returns-err-for-y-equal-zero
  (implies (and (primep p)
                (pfield::fep x p)
                (pfield::fep y p))
           (iff (reserrp (field-div-spec x y p))
                (equal y 0)))
  :enable (field-div-spec))

(defruled field-div-gadget-soundness-new
  (implies (and (symbolp x)
                (symbolp y)
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
                (z$ (lookup-equal z asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-div-gadget x y z w) asg p)
                      (and (not (equal y$ 0))
                           (equal z$ (field-div-spec x$ y$ p))))))
  :use ((:instance field-inverse-gadget-soundness (x y) (y w)))
  ; It would be good if we could prove this without rewriting everything down
  ; to math...
  :enable (field-div-gadget
           field-inverse-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           field-mul-gadget
           field-div-spec field-inverse
           pfield::div pfield::mul)
  :disable pfield::equal-of-inv
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

; Completeness will need an existential on w.
