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

(include-book "field-pow-bits-const")

(local (include-book "../library-extensions/digits"))

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel consp-of-cdr-of-nat=>lebits*
  (implies (and (natp n)
                (>= n 2))
           (consp (cdr (nat=>lebits* n))))
  :enable (nat=>lebits*
           acl2::nat=>lendian*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget raises a field variable to a constant exponent.
; The exponent must be an integer above 1;
; the cases of the exponent being 0 or 1 are easily handled separately,
; but in the future we may actually extend this gadget to handle those cases.
; This is a relatively thin wrapper of the field-pow-bits-const gadget,
; where we convert the constant exponent c to bits cs
; and then we use that gadget.

(define field-pow-const-slen ((c posp))
  :guard (not (equal c 1))
  :returns (slen natp :hyp :guard :rule-classes (:rewrite :type-prescription))
  (field-pow-bits-const-slen (nat=>lebits* c)))

(define field-pow-const-rlen ((c posp))
  :guard (not (equal c 1))
  :returns (rlen natp :hyp :guard :rule-classes (:rewrite :type-prescription))
  (1- (len (nat=>lebits* c))))

(define field-pow-const-gadget ((x symbolp)
                                (c posp)
                                (ss symbol-listp)
                                (rs symbol-listp)
                                (p primep))
  :guard (and (not (equal c 1))
              (equal (len ss) (field-pow-const-slen c))
              (equal (len rs) (field-pow-const-rlen c)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (field-pow-bits-const-gadget x (nat=>lebits* c) ss rs p)
  :prepwork ((local (in-theory (e/d (field-pow-const-slen
                                     field-pow-const-rlen
                                     nat=>lebits*-msb-is-1
                                     consp-of-cdr-of-nat=>lebits*)
                                    (last))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Soundness is proved from the one of the wrapped gadget.

(defruled field-pow-const-soundness
  (implies (and (primep p)
                (symbolp x)
                (posp c)
                (not (equal c 1))
                (symbol-listp ss)
                (equal (len ss) (field-pow-const-slen c))
                (symbol-listp rs)
                (equal (len rs) (field-pow-const-rlen c))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((x$ (lookup-equal x asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-pow-const-gadget x c ss rs p) asg p)
                      (equal (car rs$)
                             (pfield::pow x$ c p)))))
  :do-not-induct t
  :use (:instance field-pow-bits-const-soundness (cs (nat=>lebits* c)))
  :enable (field-pow-const-gadget
           field-pow-const-slen
           field-pow-const-rlen
           nat=>lebits*-msb-is-1)
  :disable last)
