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

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The field inverse gadget consists of a single constraint
;   (x) (y) = (1)
; where x is the input and y is the output, i.e. the inverse of x.
; If x is not 0, then the constraint is satisfied iff y is 1/x.
; If x is 0, the constraint is unsatisfiable;
; the fact that x is not 0 is a precondition for this gadget.

(define field-inverse-gadget ((x symbolp) (y symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 y))
         :c (list (list 1 1)))))

(defruled field-inverse-gadget-to-equal-inverse
  (implies (and (symbolp x)
                (symbolp y)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg)))
             (implies (not (equal x$ 0))
                      (equal (r1cs::r1cs-constraints-holdp
                              (field-inverse-gadget x y) asg p)
                             (equal y$ (pfield::inv x$ p))))))
  :enable (field-inverse-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Experiment: try a specification that uses defresult to handle the errors.

(include-book "kestrel/fty/integer-result" :dir :system)
; defines integer-resultp
; (in ACL2 package, which is imported into the current package)

; This should be in prime-field-rules.
(defrule fep-of-inv
  (implies (and (primep p)
                (pfield::fep x p)
                (not (= x 0)))
           (pfield::fep (pfield::inv x p) p)))

; This is the specification of the field inverse opcode,
; handling the case of inverse of zero by returning an Err,
; matching the developer view of the semantics of the opcode.
(define field-inverse (x p)
  :guard (and (primep p)
              (pfield::fep x p))
  :returns (y-or-err integer-resultp)
  (if (= x 0)
      (reserr 0)
    (pfield::inv x p)))

; Explicate the domain and range of the spec function.
; Spec function does not return an error:
(defruled field-inverse-returns-fep-for-x-not-equal-zero
  (implies (and (primep p)
                (pfield::fep x p))
           (iff (pfield::fep (field-inverse x p) p)
                (not (equal x 0))))
  :enable (field-inverse))

; Spec function does return an error:
(defruled field-inverse-returns-err-for-x-equal-zero
  (implies (and (primep p)
                (pfield::fep x p))
           (iff (reserrp (field-inverse x p))
                (equal x 0)))
  :enable (field-inverse))

(defruled field-inverse-gadget-soundness
  (implies (and (symbolp x)
                (symbolp y)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-inverse-gadget x y) asg p)
                      (and (not (equal x$ 0))
                           (equal y$ (field-inverse x$ p))))))
  :enable (field-inverse-gadget r1cs::r1cs-constraint-holdsp r1cs::dot-product
           field-inverse))
