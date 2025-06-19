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

(include-book "boolean-check")
(include-book "pow2sum")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is an optimized version of the unsigned-small-add-check gadget.
; Since the high bit z is constrained to be 0 in that gadget,
; we can avoid the bit altogether, saving one variable.
; The soundness and completeness theorem shows that this is correct.

; However, as we plan to have gadgets
; return error indications instead of being unsatisfied
; when certain operations run into errors (e.g. checked sum doesn't fit),
; we will want to use z as the error bit.
; Nonetheless, this optimized gadget may be useful
; in contexts where we don't need to return errors
; (because the failure cannot be recovered,
; unlike a checked sum in a branch of a conditional).

(define unsigned-small-add-checked-opt-gadget ((xs symbol-listp)
                                               (ys symbol-listp)
                                               (zs symbol-listp)
                                               (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (list (r1cs::make-r1cs-constraint
                 :a (append (pow2sum-vector xs 0)
                            (pow2sum-vector ys 0))
                 :b (list (list 1 1))
                 :c (pow2sum-vector zs 0)))))

(defruled unsigned-small-add-opt-gadget-correct
  (implies (and (primep p)
                (< (1+ (len xs)) (integer-length p))
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-add-checked-opt-gadget
                               xs ys zs p)
                              asg
                              p)
                             (and (bit-listp zs$)
                                  (equal (lebits=>nat zs$)
                                         (+ (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :use ((:instance plus-expt2-upper-bound
                   (n (len xs))
                   (a (lebits=>nat (lookup-equal-list xs asg)))
                   (b (lebits=>nat (lookup-equal-list ys asg))))
        (:instance expt2-mono
                   (a (1+ (len xs)))
                   (b (1- (integer-length p)))))
  :enable (unsigned-small-add-checked-opt-gadget
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraint-holdsp
           pow2sum-vector-to-mod-of-lebits=>nat
           r1cs::dot-product-of-append
           r1cs::dot-product
           pfield::add
           lebits=>nat-less-when-len-less
           positive->=-expt2-of-integer-length-minus-1))
