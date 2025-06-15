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

(include-book "unsigned-small-sub")
(include-book "one")

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the wrapped version of unsigned small subtraction.
; It is similar to unsigned-small-add-wrapped in structure:
; it is the same as unsigned-small-sub,
; but we split the result bits into the low n and high one.

(define unsigned-small-sub-wrapped-gadget ((xs symbol-listp)
                                           (ys symbol-listp)
                                           (zs symbol-listp)
                                           (z symbolp)
                                           (one symbolp)
                                           (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (unsigned-small-sub-gadget xs ys (append zs (list z)) one p))

; The proof is also quite analogous to unsigned-small-add-checked,
; including the local lemma whose :use hints provides a key proof step.

(defruledl lemma
  (implies (equal x y)
           (equal (mod x a)
                  (mod y a))))

(defruled unsigned-small-sub-wrapped-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp z)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-sub-wrapped-gadget
                                 xs ys zs z one p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (lebits=>nat zs$)
                                           (mod (- (lebits=>nat xs$)
                                                   (lebits=>nat ys$))
                                                (expt 2 (len zs)))))))))
  :do-not-induct t
  :use (:instance lemma
                  (a (expt 2 (len xs)))
                  (x (lebits=>nat
                      (lookup-equal-list (append zs (list z)) asg)))
                  (y (+ (expt 2 (len xs))
                        (lebits=>nat (lookup-equal-list xs asg))
                        (- (lebits=>nat (lookup-equal-list ys asg))))))
  :enable (unsigned-small-sub-wrapped-gadget
           unsigned-small-sub-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons)
  :disable bitp)
