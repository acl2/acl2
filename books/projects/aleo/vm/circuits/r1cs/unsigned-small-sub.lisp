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

(include-book "unsigned-small-sub-opt")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the non-optimized gadget for unsigned subtraction from snarkVM,
; mentioned in unsigned-small-sub-opt.lisp.
; The difference with the optimized and simpler gadget defined there
; is that the A vector, instead of the simpler form
;      x(0) + 2*x(1) + ... + 2^(n-1)*x(n-1) + 2^n
;    - y(0) - 2*y(1) - ... - 2^(n-1)*y(n-1) +
; has the form
;      x(0) + 2*x(1) + ... + 2^(n-1)*x(n-1) +
;    - y(0) + (2^n-1)*w - 2*y(1) - ... - 2^(n-1)*y(n-1) + 1
; where w is a public variable that should be assumed to be 1.
; That is, the sequence of y(i) addends is "interrupted"
; by 2^n-1 (assuming w = 1), and there is a 1 at the end.
; This is equivalent to the 2^n in the simpler optimized gadget.
; The reason for this greater complexity in the gadget from snarkVM
; derives from the way the snarkVM code is written,
; which maximizes its own simplicity, at a slight cost for the generated R1CS.

; Here we formalize the gadget as it is generated from snarkVM.
; It has the same form as the optimized one, except for the A vector.
; We prove the two A vectors equivalent,
; then we prove the two gadgets equivalent from there,
; then we prove the correctness of the snarkVM gadget
; from the correctness of the optimized gadget and from the gadget equivalence.

; Note that we need the hypothesis that n (the number of bits of xs and ys)
; is at least one, otherwise the positioning of the (2^n-1)*w
; just after the first addend does not make sense if there are no addends.

(define unsigned-small-sub-vector ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (one symbolp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (consp xs))
  :returns (vec r1cs::sparse-vectorp :hyp :guard
                :hints (("Goal"
                         :in-theory (enable pow2sum-neg-prime-vector
                                            vector-neg-prime)
                         :expand ((pow2sum-vector ys 0)))))
  (b* ((vec-xs (pow2sum-vector xs 0))
       (vec-ys (pow2sum-neg-prime-vector ys 0 p))
       (first-vec-ys (car vec-ys))
       (rest-vec-ys (cdr vec-ys)))
    (append vec-xs
            (list first-vec-ys)
            (list (list (1- (expt 2 (len xs))) one))
            rest-vec-ys
            (list (list 1 1)))))

(defruledl vector-equivalence
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg one))
           (b* ((one$ (lookup-equal one asg)))
             (implies (equal one$ 1)
                      (equal (r1cs::dot-product
                              (unsigned-small-sub-vector xs ys one p) asg p)
                             (r1cs::dot-product
                              (unsigned-small-sub-opt-vector xs ys p) asg p)))))
  :induct (len ys)
  :enable (unsigned-small-sub-vector
           unsigned-small-sub-opt-vector
           r1cs::dot-product
           r1cs::dot-product-of-append)
  :prep-lemmas
  ((defrule lemma
     (implies (integerp a)
              (equal (pfield::add 1 (pfield::add a b p) p)
                     (pfield::add (1+ a) b p)))
     :enable pfield::add)))

(define unsigned-small-sub-gadget ((xs symbol-listp)
                                   (ys symbol-listp)
                                   (zs symbol-listp)
                                   (one symbolp)
                                   (p primep))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (1+ (len xs)))
              (< (1+ (len xs)) (integer-length p))
              (consp xs))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (list (r1cs::make-r1cs-constraint
                 :a (unsigned-small-sub-vector xs ys one p)
                 :b (list (list 1 1))
                 :c (pow2sum-vector zs 0)))))

(defruledl gadget-equivalence
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg one)
                (equal (lookup-equal one asg) 1))
           (equal (r1cs::r1cs-constraints-holdp
                   (unsigned-small-sub-gadget xs ys zs one p) asg p)
                  (r1cs::r1cs-constraints-holdp
                   (unsigned-small-sub-opt-gadget xs ys zs p) asg p)))
  :enable (unsigned-small-sub-gadget
           unsigned-small-sub-opt-gadget
           vector-equivalence
           r1cs::r1cs-constraints-holdp
           r1cs::r1cs-constraint-holdsp))

(defruled unsigned-small-sub-gadget-correct
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (equal (len zs) (1+ (len xs)))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (equal (r1cs::r1cs-constraints-holdp
                              (unsigned-small-sub-gadget xs ys zs one p) asg p)
                             (and (bit-listp zs$)
                                  (equal (lebits=>nat zs$)
                                         (+ (- (lebits=>nat xs$)
                                               (lebits=>nat ys$))
                                            (expt 2 (len xs)))))))))
  :enable (gadget-equivalence
           unsigned-small-sub-opt-gadget-correct))
