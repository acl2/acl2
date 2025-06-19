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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a variant of the unsigned-small-sub-opt gadget
; in which the first operand is a constant,
; expressed as a list of constant bits.
; The definitions and theorems are essentially the same,
; except for having the bits cs instead of the variables xs.

(define unsigned-small-sub-opt-const-var-vector ((cs bit-listp)
                                                 (ys symbol-listp)
                                                 (p primep))
  :guard (equal (len ys) (len cs))
  :returns (vec r1cs::sparse-vectorp :hyp :guard)
  (append (list (list (lebits=>nat cs) 1))
          (list (list (expt 2 (len ys)) 1))
          (pow2sum-neg-prime-vector ys 0 p)))

(define unsigned-small-sub-opt-const-var-gadget ((cs bit-listp)
                                                 (ys symbol-listp)
                                                 (zs symbol-listp)
                                                 (p primep))
  :guard (and (equal (len ys) (len cs))
              (equal (len zs) (1+ (len cs)))
              (< (1+ (len cs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append (boolean-check-gadget-list zs p)
          (list (r1cs::make-r1cs-constraint
                 :a (unsigned-small-sub-opt-const-var-vector cs ys p)
                 :b (list (list 1 1))
                 :c (pow2sum-vector zs 0)))))

(defruled unsigned-small-sub-opt-const-var-gadget-correct
  (implies (and (primep p)
                (bit-listp cs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len cs))
                (equal (len zs) (1+ (len cs)))
                (< (1+ (len cs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (bit-listp ys$)
                      (equal
                       (r1cs::r1cs-constraints-holdp
                        (unsigned-small-sub-opt-const-var-gadget cs ys zs p)
                        asg
                        p)
                       (and (bit-listp zs$)
                            (equal (lebits=>nat zs$)
                                   (+ (- (lebits=>nat cs)
                                         (lebits=>nat ys$))
                                      (expt 2 (len cs)))))))))
  :do-not-induct t
  :use ((:instance diff-offset-expt2-upper-bound
                   (n (len cs))
                   (a (lebits=>nat cs))
                   (b (lebits=>nat (lookup-equal-list ys asg))))
        (:instance expt2-mono
                   (a (len zs))
                   (b (1- (integer-length p)))))
  :enable (unsigned-small-sub-opt-const-var-gadget
           unsigned-small-sub-opt-const-var-vector
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraint-holdsp
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-neg-prime-vector-to-mod-of-lebits=>nat
           r1cs::dot-product-of-append
           r1cs::dot-product
           pfield::add
           lebits=>nat-less-when-len-less
           positive->=-expt2-of-integer-length-minus-1)
  :disable acl2::<-of-expt-and-expt-same-base)
