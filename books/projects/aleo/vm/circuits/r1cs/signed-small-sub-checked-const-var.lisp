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

(include-book "unsigned-small-sub-wrapped-const-var")
(include-book "boolean-and-notright")
(include-book "boolean-nor")
(include-book "boolean-xor")
(include-book "unsigned-small-sub-wrapped")
(include-book "zero")

(include-book "../library-extensions/digits")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a variant of the unsigned-small-sub-checked gadget
; in which the first operand is a constant,
; expressed as a list of constant bits.
; The definitions and theorems are essentially the same,
; except for having the bits cs instead of the variables xs.

(define signed-small-sub-checked-const-var-gadget ((cs bit-listp)
                                                   (ys symbol-listp)
                                                   (zs symbol-listp)
                                                   (carry symbolp)
                                                   (zy-diff-sign symbolp)
                                                   (over/under-flow symbolp)
                                                   (one symbolp)
                                                   (p primep))
  :guard (and (consp cs)
              (equal (len ys) (len cs))
              (equal (len zs) (len cs))
              (< (1+ (len cs)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append
   (unsigned-small-sub-wrapped-const-var-gadget cs ys zs carry one p)
   (boolean-xor-gadget (car (last zs)) (car (last ys)) zy-diff-sign p)
   (if (equal (car (last cs)) 0)
       (boolean-and-notright-gadget (car (last ys))
                                    zy-diff-sign
                                    over/under-flow
                                    one
                                    p)
     (boolean-nor-gadget (car (last ys)) zy-diff-sign over/under-flow p))
   (zero-gadget over/under-flow)))

(local
 (defmacro hyps ()
   '(and (bit-listp cs)
         (bit-listp ys)
         (bit-listp zs)
         (bitp carry)
         (consp cs)
         (equal (len ys) (len cs))
         (equal (len zs) (len cs))
         (equal (+ (lebits=>nat cs)
                   (- (lebits=>nat ys))
                   (expt 2 (len cs)))
                (+ (lebits=>nat zs)
                   (* carry (expt 2 (len cs))))))))

(defruledl carry-neq-zs-msb-when-cs-nonneg-and-ys-nonneg
  (implies (hyps)
           (implies (and (equal (car (last cs)) 0)
                         (equal (car (last ys)) 0))
                    (or (and (equal (car (last zs)) 0)
                             (equal carry 1))
                        (and (equal (car (last zs)) 1)
                             (equal carry 0)))))
  :do-not-induct t
  :use (lemma1 lemma2)

  :prep-lemmas

  ((defruled lemma1
     (implies (hyps)
              (implies (and (equal (car (last cs)) 0)
                            (equal (car (last ys)) 0)
                            (equal carry 0))
                       (equal (car (last zs)) 1)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits ys))
           (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits zs))))

   (defruled lemma2
     (implies (hyps)
              (implies (and (equal (car (last cs)) 0)
                            (equal (car (last ys)) 0)
                            (equal carry 1))
                       (equal (car (last zs)) 0)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits cs))
           (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits zs))))))

(defruledl carry-neq-zs-msb-when-cs-neg-and-ys-neg
  (implies (hyps)
           (implies (and (equal (car (last cs)) 1)
                         (equal (car (last ys)) 1))
                    (or (and (equal (car (last zs)) 0)
                             (equal carry 1))
                        (and (equal (car (last zs)) 1)
                             (equal carry 0)))))
  :do-not-induct t
  :use (lemma1 lemma2)

  :prep-lemmas

  ((defruled lemma1
     (implies (hyps)
              (implies (and (equal (car (last cs)) 1)
                            (equal (car (last ys)) 1)
                            (equal carry 0))
                       (equal (car (last zs)) 1)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits cs))
           (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits zs))))

   (defruled lemma2
     (implies (hyps)
              (implies (and (equal (car (last cs)) 1)
                            (equal (car (last ys)) 1)
                            (equal carry 1))
                       (equal (car (last zs)) 0)))
     :do-not-induct t
     :cases ((bitp (car (last zs))))
     :disable bitp
     :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))
           (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits zs))))))

(defrulel carry-0-when-cs-nonneg-and-ys-neg
  (implies (hyps)
           (implies (and (equal (car (last cs)) 0)
                         (equal (car (last ys)) 1))
                    (equal carry 0)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-upper-bound-when-msb-is-0 (bits cs))
        (:instance lebits=>nat-lower-bound-when-msb-is-1 (bits ys))))

(defrulel carry-1-when-cs-neg-and-ys-nonneg
  (implies (hyps)
           (implies (and (equal (car (last cs)) 1)
                         (equal (car (last ys)) 0))
                    (equal carry 1)))
  :rule-classes nil
  :do-not-induct t
  :use ((:instance lebits=>nat-lower-bound-when-msb-is-1 (bits cs))
        (:instance lebits=>nat-upper-bound-when-msb-is-0 (bits ys))))

(defruledl consp-of-ys-and-zs
  (implies (and (consp cs)
                (equal (len ys) (len cs))
                (equal (len zs) (len cs)))
           (and (consp ys)
                (consp zs))))

(defruled signed-small-sub-checked-const-var-gadget-soundness
  (implies (and (primep p)
                (< (1+ (len cs)) (integer-length p))
                (bit-listp cs)
                (symbol-listp ys)
                (symbol-listp zs)
                (symbolp carry)
                (symbolp zy-diff-sign)
                (symbolp over/under-flow)
                (symbolp one)
                (consp cs)
                (equal (len ys) (len cs))
                (equal (len zs) (len cs))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg zy-diff-sign)
                (r1cs::valuation-bindsp asg over/under-flow)
                (r1cs::valuation-bindsp asg one))
           (b* ((ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (carry$ (lookup-equal carry asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp cs)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-sub-checked-const-var-gadget
                                 cs ys zs carry
                                 zy-diff-sign over/under-flow
                                 one p)
                                asg p)
                               (and (bit-listp zs$)
                                    (bitp carry$)
                                    (equal (lebits=>int zs$)
                                           (- (lebits=>int cs)
                                              (lebits=>int ys$))))))))
  :do-not-induct t
  :use (consp-of-ys-and-zs
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list zs asg)))
        (:instance carry-neq-zs-msb-when-cs-nonneg-and-ys-nonneg
                   (cs cs)
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-neq-zs-msb-when-cs-neg-and-ys-neg
                   (cs cs)
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-0-when-cs-nonneg-and-ys-neg
                   (cs cs)
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg)))
        (:instance carry-1-when-cs-neg-and-ys-nonneg
                   (cs cs)
                   (ys (lookup-equal-list ys asg))
                   (zs (lookup-equal-list zs asg))
                   (carry (lookup-equal carry asg))))
  :enable (signed-small-sub-checked-const-var-gadget
           unsigned-small-sub-wrapped-const-var-gadget
           unsigned-small-sub-const-var-gadget-correct
           lookup-equal-list-of-append
           lookup-equal-list
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           boolean-xor-gadget-to-bitxor
           boolean-nor-gadget-to-bitnor
           lookup-equal-of-car
           lookup-equal-list-of-last
           bitxor
           bitnor
           boolean-and-notright-gadget-to-booland-boolnot
           zero-gadget-to-equal-0
           lebits=>int)
  :prep-lemmas
  ((defrule fwd-lemma
     (implies (and (bit-listp bits) (consp bits))
              (bitp (car (last bits))))
     :rule-classes :forward-chaining)))
