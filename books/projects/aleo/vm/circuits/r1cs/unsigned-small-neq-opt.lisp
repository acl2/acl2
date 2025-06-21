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

(include-book "pow2sum")

(local (include-book "../library-extensions/digits"))

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is an optimized version of unsigned-small-neq,
; which omits the constraint to make z a boolean.
; That constraint is unnecessary, because the other two constraints
; imply that r must be either 0 or 1,
; similarly to field-neq.

(define unsigned-small-neq-opt-gadget ((xs symbol-listp)
                                       (ys symbol-listp)
                                       (z symbolp)
                                       (w symbolp)
                                       (one symbolp)
                                       (p primep))
  :guard (and (equal (len ys) (len xs))
              (< (len xs) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (append (pow2sum-vector xs 0) (pow2sum-neg-prime-vector ys 0 p))
         :b (list (list 1 w))
         :c (list (list 1 z)))
        (r1cs::make-r1cs-constraint
         :a (append (pow2sum-vector xs 0) (pow2sum-neg-prime-vector ys 0 p))
         :b (list (list (1- p) z)
                  (list 1 one))
         :c nil)))

(defruled unsigned-small-neq-opt-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp z)
                (symbolp w)
                (symbolp one)
                (equal (len ys) (len xs))
                (< (len xs) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg z)
                (r1cs::valuation-bindsp asg w)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (z$ (lookup-equal z asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-neq-opt-gadget xs ys z w one p)
                                asg
                                p)
                               (equal z$ (if (equal (lebits=>nat xs$)
                                                    (lebits=>nat ys$))
                                             0
                                           1))))))
  :do-not-induct t
  :enable (unsigned-small-neq-opt-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
           pfield::add)
  :use ((:instance lemma (z (lookup-equal z asg)))
        (:instance acl2::lebits=>nat-injectivity
                   (digits1 (lookup-equal-list xs asg))
                   (digits2 (lookup-equal-list ys asg)))
        (:instance lebits=>nat-less-when-len-less
                   (bs (lookup-equal-list xs asg)))
        (:instance lebits=>nat-less-when-len-less
                   (bs (lookup-equal-list ys asg))))
  :disable acl2::lebits=>nat-injectivity
  :prep-lemmas
  ((defrule lemma
     (implies (and (primep p)
                   (pfield::fep z p))
              (implies (equal (+ 1 (pfield::neg z P)) P)
                       (equal z 1)))
     :rule-classes nil
     :enable pfield::neg)))
