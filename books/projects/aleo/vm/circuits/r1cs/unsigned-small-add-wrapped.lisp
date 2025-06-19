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

(include-book "unsigned-small-add")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget is the same as unsigned-small-add,
; but we interpret it differently:
; it puts the wrapped sum of xs and ys into zs,
; with z as an auxiliary variable that holds the carry
; (unlike unsigned-small-add-checked, it does not constrain z to be 0).

(define unsigned-small-add-wrapped-gadget ((xs symbol-listp)
                                           (ys symbol-listp)
                                           (zs symbol-listp)
                                           (z symbolp)
                                           (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-add-gadget xs ys (append zs (list z)) p))

; We prove the soundness of the gadget.
; It is in the formulation of this proof that we explicate
; our different interpretation of this gadget
; compared to unsigned-small-add-gadget.
; We say that if the gadget holds,
; then zs is the modular addition of xs and ys.

; The key of the proof is that
; we use the correctness theorem of unsigned-small-add-gadget
; to obtain the fact that zs and z are the (exact) sum of xs and ys,
; then we apply mod to both sizes (see lemma just below),
; and then the conclusion follows.

(defruledl lemma
  (implies (equal x y)
           (equal (mod x a)
                  (mod y a))))

(defruled unsigned-small-add-wrapped-gadget-soundness
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-add-wrapped-gadget xs ys zs z p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (lebits=>nat zs$)
                                           (mod (+ (lebits=>nat xs$)
                                                   (lebits=>nat ys$))
                                                (expt 2 (len zs)))))))))
  :do-not-induct t
  :use (:instance lemma
                  (a (expt 2 (len xs)))
                  (x (lebits=>nat
                      (lookup-equal-list (append zs (list z)) asg)))
                  (y (+ (lebits=>nat (lookup-equal-list xs asg))
                        (lebits=>nat (lookup-equal-list ys asg)))))
  :enable (unsigned-small-add-wrapped-gadget
           unsigned-small-add-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons)
  :disable bitp)
