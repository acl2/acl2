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
(include-book "field-const-pow-bits")

(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defrulel integer-length-lower-bound
;;   (implies (and (posp p)
;;                 (> p 4))
;;            (> (integer-length p) 2))
;;   :rule-classes :linear
;;   :enable integer-length)

;; (defruledl ys-at-least-3
;;   (implies (and (posp p)
;;                 (>= p 4)
;;                 (equal (len ys) (integer-length p)))
;;            (and (consp ys)
;;                 (consp (cdr ys))
;;                 (consp (cddr ys))))
;;   :disable len
;;   :use lemma
;;   :prep-lemmas
;;   ((defruled lemma
;;      (implies (> (len ys) 2)
;;               (and (consp ys)
;;                    (consp (cdr ys))
;;                    (consp (cddr ys)))))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ; This gadget raises a constant field element to a variable field element.
;; ; First we decompose the exponent into bits
;; ; and then we use the gadget that raises the constant to the exponent in bits.
;; ; Note that we use zs for the rs variables of the field-to-bits gadget,
;; ; while we use ss and rs for
;; ; the homonymous variables of field-const-pow-bits gadget.

;; (define field-const-pow-gadget ((x (pfield::fep x p))
;;                                 (unitvar symbolp)
;;                                 (y symbolp)
;;                                 (ys symbol-listp)
;;                                 (zs symbol-listp)
;;                                 (ss symbol-listp)
;;                                 (rs symbol-listp)
;;                                 (p primep))
;;   :guard (and (> p 4)
;;               (equal (len ys) (integer-length p))
;;               (equal (len zs) (bits-lt-prime-rlen p))
;;               (equal (len ss) (1- (len ys)))
;;               (equal (len rs) (1- (len ys))))
;;   :returns (constraints r1cs::r1cs-constraint-listp
;;                         :hyp :guard
;;                         :hints (("Goal" :use ys-at-least-3)))
;;   (append (field-to-bits-gadget y ys zs unitvar p)
;;           (field-const-pow-bits-gadget x unitvar ys ss rs p))
;;   :guard-hints (("Goal" :use ys-at-least-3)))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ; Soundess is proved by putting together
;; ; the soundness theorems of the two sub-gadgets.

;; (defruled field-const-pow-soundness
;;   (implies (and (primep p)
;;                 (> p 4)
;;                 (pfield::fep x p)
;;                 (symbolp unitvar)
;;                 (symbolp y)
;;                 (symbol-listp ys)
;;                 (equal (len ys) (integer-length p))
;;                 (symbol-listp zs)
;;                 (equal (len zs) (bits-lt-prime-rlen p))
;;                 (symbol-listp ss)
;;                 (equal (len ss) (1- (len ys)))
;;                 (symbol-listp rs)
;;                 (equal (len rs) (1- (len ys)))
;;                 (r1cs::r1cs-valuationp asg p)
;;                 (r1cs::valuation-bindsp asg unitvar)
;;                 (r1cs::valuation-bindsp asg y)
;;                 (r1cs::valuation-binds-allp asg ys)
;;                 (r1cs::valuation-binds-allp asg zs)
;;                 (r1cs::valuation-binds-allp asg ss)
;;                 (r1cs::valuation-binds-allp asg rs))
;;            (b* ((unitvar$ (lookup-equal unitvar asg))
;;                 (y$ (lookup-equal y asg))
;;                 (rs$ (lookup-equal-list rs asg)))
;;              (implies (r1cs::r1cs-constraints-holdp
;;                        (field-const-pow-gadget x unitvar y ys zs ss rs p) asg p)
;;                       (implies (equal unitvar$ 1)
;;                                (equal (car rs$)
;;                                       (pfield::pow x y$ p))))))
;;   :do-not-induct t
;;   :enable (field-const-pow-gadget)
;;   :disable len
;;   :use ((:instance field-to-bits-soundness (x y) (xs ys) (rs zs) (u unitvar))
;;         field-const-pow-bits-soundness
;;         ys-at-least-3))
