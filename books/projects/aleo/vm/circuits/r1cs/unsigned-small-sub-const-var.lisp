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

(include-book "unsigned-small-sub-opt-const-var")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a variant of the unsigned-small-sub gadget
; in which the first operand is a constant,
; expressed as a list of constant bits.
; The definitions and theorems are essentially the same,
; except for having the bits cs instead of the variables xs.

; The A vector is a bit different.
; The powers-of-two weighted sum for xs is absent from the vector.
; Instead, the final 1 (see the unsigned-small-sub gadget)
; is increased by the value of the cs bits.
; This is how the gadget comes out of snarkVM.

(define unsigned-small-sub-const-var-vector ((cs bit-listp)
                                             (ys symbol-listp)
                                             (one symbolp)
                                             (p primep))
  :guard (and (equal (len ys) (len cs))
              (consp cs))
  :returns (vec r1cs::sparse-vectorp :hyp :guard
                :hints (("Goal"
                         :in-theory (enable pow2sum-neg-prime-vector
                                            vector-neg-prime)
                         :expand ((pow2sum-vector ys 0)))))
  (b* ((c (lebits=>nat cs))
       (vec-ys (pow2sum-neg-prime-vector ys 0 p))
       (first-vec-ys (car vec-ys))
       (rest-vec-ys (cdr vec-ys)))
    (append (list first-vec-ys)
            (list (list (1- (expt 2 (len cs))) one))
            rest-vec-ys
            (list (list (1+ c) 1)))))

(defruledl vector-equivalence
  (implies (and (primep p)
                (bit-listp cs)
                (symbol-listp ys)
                (symbolp one)
                (consp cs)
                (equal (len ys) (len cs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg one))
           (b* ((one$ (lookup-equal one asg)))
             (implies (equal one$ 1)
                      (equal (r1cs::dot-product
                              (unsigned-small-sub-const-var-vector cs ys one p)
                              asg
                              p)
                             (r1cs::dot-product
                              (unsigned-small-sub-opt-const-var-vector cs ys p)
                              asg
                              p)))))
  :induct (len ys)
  :enable (unsigned-small-sub-const-var-vector
           unsigned-small-sub-opt-const-var-vector
           r1cs::dot-product)
  :prep-lemmas
  ((defrule lemma
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (posp p))
              (equal (pfield::add (1+ a) (pfield::add (1- b) c p) p)
                     (pfield::add a (pfield::add b c p) p)))
     :enable pfield::add
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))))

(define unsigned-small-sub-const-var-gadget ((cs bit-listp)
                                             (ys symbol-listp)
                                             (zs symbol-listp)
                                             (one symbolp)
                                             (p primep))
  :guard (and (equal (len ys) (len cs))
              (equal (len zs) (1+ (len cs)))
              (< (1+ (len cs)) (integer-length p))
              (consp cs))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (list (r1cs::make-r1cs-constraint
                 :a (unsigned-small-sub-const-var-vector cs ys one p)
                 :b (list (list 1 1))
                 :c (pow2sum-vector zs 0)))))

(defruledl gadget-equivalence
  (implies (and (primep p)
                (bit-listp cs)
                (symbol-listp ys)
                (symbolp one)
                (consp cs)
                (equal (len ys) (len cs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1))
           (equal (r1cs::r1cs-constraints-holdp
                   (unsigned-small-sub-const-var-gadget cs ys zs one p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-sub-opt-const-var-gadget cs ys zs p) asg p)))
  :enable (unsigned-small-sub-const-var-gadget
           unsigned-small-sub-opt-const-var-gadget
           vector-equivalence
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp))

(defruled unsigned-small-sub-const-var-gadget-correct
  (implies (and (primep p)
                (bit-listp cs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp one)
                (consp cs)
                (equal (len ys) (len cs))
                (equal (len zs) (1+ (len cs)))
                (< (1+ (len cs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg one))
           (b* ((ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp ys$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-sub-const-var-gadget
                               cs ys zs one p)
                              asg
                              p)
                             (and (bit-listp zs$)
                                  (equal (lebits=>nat zs$)
                                         (+ (- (lebits=>nat cs)
                                               (lebits=>nat ys$))
                                            (expt 2 (len cs)))))))))
  :enable (gadget-equivalence
           unsigned-small-sub-opt-const-var-gadget-correct))
