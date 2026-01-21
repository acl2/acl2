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

(include-book "field-square")
(include-book "field-mul")

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/digits"))

(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget raises a field element to
; the powers-of-two weighted sum of a non-empty sequence of bits
; that is constant and known.
; That is, given a field element,
; and a non-empty sequence of known constant bits c(0), c(1), ..., c(n-1),
; this gadget computes
;   x ^ (c(0) + 2 * c(1) + 4 * c(2) + ... + 2^(n-1) * c(n-1)).
; Note that n may have any value, also much higher than
; the number of bits of the prime p:
; the exponent is an integer (not a field element),
; and exponentiation in prime fields is well-defined
; for any integer exponent.

; The gadget calculates the result
; by going through the bits of the exponent
; and squaring and multiplying in the well-known way.
; The bits are processed in big endian order, i.e. from c(n-1) to c(0).
; The construction is similar to the one when the exponent bits are not constant
; (see the field-pow-bits gadget),
; but the fact that the bits are constant means that
; the constraints may be further optimized,
; actually making this gadget more complex to formalize and verify
; compared to the one (field-pow-bits) where the bits are variable.

; The unoptimized construction is as in field-pow-bits, i.e.
;
;   r(n) = 1
;
;   s(n-1) = r(n) * r(n)
;   p(n-1) = x * s(n-1)
;   r(n-1) = IF c(n-1) THEN p(n-1) ELSE s(n-1)
;
;   s(n-2) = r(n-1) * r(n-1)
;   p(n-2) = x * s(n-2)
;   r(n-2) = IF c(n-2) THEN p(n-2) ELSE s(n-2)
;
;   ...
;
;   s(0) = r(1) * r(1)
;   p(0) = x * s(0)
;   r(0) = IF c(0) THEN p(0) ELSE s(0)
;
; But besides the same optimization that eliminates r(n), s(n-1), and p(n-1),
; there are further optimizations here.
; First, we do not need the IF-THEN-ELSEs,
; because the conditions c(i) are known:
; thus, each r(i) can be alternatively defined in two ways:
;
;   r(i) = x * s(i), where s(i) = r(i-1) * r(i-1), if c(i) = 1
;   r(i) = r(i-1) * r(i-1), if c(0) = 0
;
; If c(i) = 1, there is an extra constraint and extra variable s(i),
; both absent if c(i) = 0.

; Furthermore, note that so long as c(i) is 0 starting from c(n-1),
; even r(i) can be optimized away.

; To simplify the construction slightly,
; we assume that c(n-1) = 1, i.e. the most significant bit is 1.
; This is not an actual limitation,
; because if c(n-1) = 0 instead,
; then we can just find the largest m < n such that c(m-1) = 1,
; work with the bits c(m-1) to c(0),
; and then lift things to the additional bits c(n-1) = ... = c(m)= 0.
; There has to be at least one 1 c(m) bit,
; otherwise all the bits are 0 and any x raised to 0 yields 1:
; thus, this case can be dealt with separately.

; Consider the following uniform definition first:
;
;   r(n) = 1
;
;   c(n-1) = 0 ==>
;     r(n-1) = r(n) * r(n)
;   c(n-1) = 1 ==>
;     s(n-1) = r(n) * r(n)
;     r(n-1) = x * s(n-1)
;
;   c(n-2) = 0 ==>
;     r(n-2) = r(n-1) * r(n-1)
;   c(n-2) = 1 ==>
;     s(n-2) = r(n-1) * r(n-1)
;     r(n-2) = x * s(n-2)
;
;   c(n-3) = 0 ==>
;     r(n-3) = r(n-2) * r(n-2)
;   c(n-3) = 1 ==>
;     s(n-3) = r(n-2) * r(n-2)
;     r(n-3) = x * s(n-3)
;
;   ...
;
;   c(0) = 0 ==>
;     r(0) = r(1) * r(1)
;   c(0) = 1 ==>
;     s(0) = r(1) * r(1)
;     r(0) = x * s(0)
;
; Since c(n-1) is assumed to be 1,
; we can eliminate the 0 case for c(n-1),
; and we can make some simplifications:
;
;   r(n) = 1
;
;   c(n-1) = 1 ==>
;     s(n-1) = r(n) * r(n) = 1 * 1 = 1
;     r(n-1) = x * s(n-1) = x * 1 = x
;
;   c(n-2) = 0 ==>
;     r(n-2) = r(n-1) * r(n-1) = x * x
;   c(n-2) = 1 ==>
;     s(n-2) = r(n-1) * r(n-1) = x * x
;     r(n-2) = x * s(n-2)
;
;   c(n-3) = 0 ==>
;     r(n-3) = r(n-2) * r(n-2)
;   c(n-3) = 1 ==>
;     s(n-3) = r(n-2) * r(n-2)
;     r(n-3) = x * s(n-3)
;
;   ...
;
;   c(0) = 0 ==>
;     r(0) = r(1) * r(1)
;   c(0) = 1 ==>
;     s(0) = r(1) * r(1)
;     r(0) = x * s(0)
;
; This means that we do not need r(n) and s(n-1) and r(n-1),
; and the constraints can be just
;
;   c(n-2) = 0 ==>
;     r(n-2) = x * x
;   c(n-2) = 1 ==>
;     s(n-2) = x * x
;     r(n-2) = x * s(n-2)
;
;   c(n-3) = 0 ==>
;     r(n-3) = r(n-2) * r(n-2)
;   c(n-3) = 1 ==>
;     s(n-3) = r(n-2) * r(n-2)
;     r(n-3) = x * s(n-3)
;
;   ...
;
;   c(0) = 0 ==>
;     r(0) = r(1) * r(1)
;   c(0) = 1 ==>
;     s(0) = r(1) * r(1)
;     r(0) = x * s(0)
;
; where the constraints for n-2 are a little different,
; but then all the ones for n-3 to 0 are uniform.

; Besides assuming that c(n-1) = 1,
; we also assume that n >= 2, i.e. there are two or more exponent bits.
; Otherwise, the value of the exponent is just 1,
; and this case can be dealt with separately.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We first introduce a function to calculate how many s variables there are.
; These are one less than the number of 1 bits in cs.
; The list cs is in little endian order,
; so its normal processing by cdr'ing is actually in big endian order
; (i.e. we process the last bit, the the second-to-last, etc. until the first).
; The guard only requires that there is at least one bit:
; we count the number of 1 bits, ignoring the last one
; (which, as explained above, will be 1 anyhow).

(define field-pow-bits-const-slen ((cs bit-listp))
  :guard (consp cs)
  :returns (len natp
                :hyp (bit-listp cs)
                :rule-classes (:rewrite :type-prescription))
  (cond ((not (mbt (consp cs))) 0)
        ((not (consp (cdr cs))) 0)
        (t (if (equal (car cs) 1)
               (1+ (field-pow-bits-const-slen (cdr cs)))
             (field-pow-bits-const-slen (cdr cs))))))

; We construct the gadget as explained above.
; All the bits (values and variables) are in little endian order.
; As we recursively append the constraints in reverse order,
; we reverse the list resulting from the recursion.

; Note that the guard requires the last bit of cs to be 1,
; and that there are at least two bits in cs.
; We also constraint the lengths of the ss and rs variables in the guard.

; Note also that we always cdr on cs and rs in the recursion,
; but we cdr on ss only when the first bit of cs is 1,
; in which case we use the first variable in ss for the extra constraint.

(define field-pow-bits-const-gadget ((x symbolp)
                                     (cs bit-listp)
                                     (ss symbol-listp)
                                     (rs symbol-listp)
                                     (p primep))
  :guard (and (equal (car (last cs)) 1)
              (consp (cdr cs))
              (equal (len ss) (field-pow-bits-const-slen cs))
              (equal (len rs) (1- (len cs))))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (rev (field-pow-bits-const-gadget-aux x cs ss rs p))

  :prepwork
  ((define field-pow-bits-const-gadget-aux ((x symbolp)
                                            (cs bit-listp)
                                            (ss symbol-listp)
                                            (rs symbol-listp)
                                            (p primep))
     :guard (and (equal (car (last cs)) 1)
                 (consp (cdr cs))
                 (equal (len ss) (field-pow-bits-const-slen cs))
                 (equal (len rs) (1- (len cs))))
     :returns (constrs r1cs::r1cs-constraint-listp
                       :hyp :guard
                       :hints
                       (("Goal"
                         :in-theory (enable field-pow-bits-const-slen))))
     (cond ((not (mbt (consp cs))) nil)
           ((not (mbt (consp (cdr cs)))) nil)
           ((not (consp (cddr cs)))
            (if (equal (car cs) 1)
                (append (field-mul-gadget x (car ss) (car rs))
                        (field-square-gadget x (car ss)))
              (field-square-gadget x (car rs))))
           (t (b* ((r (car rs))
                   (r-prev (cadr rs)))
                (if (equal (car cs) 1)
                    (b* ((s (car ss)))
                      (append (field-mul-gadget s x r)
                              (field-square-gadget r-prev s)
                              (field-pow-bits-const-gadget-aux x
                                                               (cdr cs)
                                                               (cdr ss)
                                                               (cdr rs)
                                                               p)))
                  (append (field-square-gadget r-prev r)
                          (field-pow-bits-const-gadget-aux x
                                                           (cdr cs)
                                                           ss
                                                           (cdr rs)
                                                           p))))))
     :guard-hints (("Goal" :in-theory (enable field-pow-bits-const-slen))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Because of the difference, noted above,
; between the constraints for n-2 and the constraints for n-3 through 0,
; it seems easier to introduce two recursive functions
; that represent the calculation.

; The first one calculates just the rs values,
; actually an extra rs value, corresponding to n-1.
; So this computes an rs valueit for each cs bit (see len-of-rs1 theorem below).

(local
 (define rs1 ((x (pfield::fep x p)) (cs bit-listp) (p primep))
   :returns (rs (pfield::fe-listp rs p) :hyp (and (primep p)
                                                  (pfield::fep x p)))
   (cond ((not (consp cs)) nil)
         ((not (consp (cdr cs)))
          (if (equal (car cs) 1)
              (list x)
            (list 1)))
         (t (b* ((rs (rs1 x (cdr cs) p))
                 (r-prev (car rs)))
              (if (equal (car cs) 1)
                  (b* ((s (pfield::mul r-prev r-prev p))
                       (r (pfield::mul x s p)))
                    (cons r rs))
                (b* ((r (pfield::mul r-prev r-prev p)))
                  (cons r rs))))))
   ///
   (defret len-of-rs1
     (equal (len rs)
            (len cs)))))

; We can prove the correctness of this function by induction.
; We show that the first rs value is the result of the exponentiation.
; The extra rs value facilitates the proof,
; because it makes the calculation more uniform;
; in contrast, the gadget skips the rs value for n-1.

(defruledl rs1-correctness
  (implies (and (primep p)
                (pfield::fep x p)
                (bit-listp cs)
                (consp cs))
           (b* ((rs (rs1 x cs p)))
             (equal (car rs)
                    (pfield::pow x (lebits=>nat cs) p))))
  :enable rs1
  :hints ('(:use induction-step))

  :prep-lemmas

  ((defruled induction-step-with-cons
     (implies (and (primep p)
                   (pfield::fep x p)
                   (bitp c)
                   (bit-listp cs))
              (implies (equal (car (rs1 x cs p))
                              (pfield::pow x (lebits=>nat cs) p))
                       (equal (car (rs1 x (cons c cs) p))
                              (pfield::pow x (lebits=>nat (cons c cs)) p))))
     :enable (rs1 acl2::lebits=>nat-of-cons)
     :prep-lemmas
     ((defrule lemma
        (implies (and (integerp p)
                      (< 1 p)
                      (natp a)
                      (pfield::fep x p))
                 (equal (pfield::pow x (* 2 a) p)
                        (pfield::mul (pfield::pow x a p)
                                     (pfield::pow x a p)
                                     p)))
        :use (:instance pfield::pow-of-+ (a x) (b a) (c a) (p p))
        :cases ((equal (* 2 a) (+ a a)))
        :disable pfield::pow-of-+)))

   (defruled induction-step
     (implies (and (primep p)
                   (pfield::fep x p)
                   (bit-listp cs))
              (implies (equal (car (rs1 x (cdr cs) p))
                              (pfield::pow x (lebits=>nat (cdr cs)) p))
                       (equal (car (rs1 x cs p))
                              (pfield::pow x (lebits=>nat cs) p))))
     :use (:instance induction-step-with-cons (c (car cs)) (cs (cdr cs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Next we introduce a similar function that calculates both ss and rs,
; where the rs is without extra bits.
; This is close to what the gadget does.

(local
 (define ss-rs ((x (pfield::fep x p)) (cs bit-listp) (p primep))
   :guard (and (equal (car (last cs)) 1)
               (consp (cdr cs)))
   :returns (mv (ss (pfield::fe-listp ss p) :hyp (primep p))
                (rs (pfield::fe-listp rs p) :hyp (and (primep p)
                                                      (pfield::fep x p))))
   (cond ((not (mbt (consp (cdr cs)))) (mv nil nil))
         ((not (consp (cddr cs)))
          (if (equal (car cs) 1)
              (mv (list (pfield::mul x x p))
                  (list (pfield::mul x (pfield::mul x x p) p)))
            (mv nil
                (list (pfield::mul x x p)))))
         (t (b* (((mv ss rs) (ss-rs x (cdr cs) p))
                 (r-prev (car rs)))
              (if (equal (car cs) 1)
                  (b* ((s (pfield::mul r-prev r-prev p))
                       (r (pfield::mul x s p)))
                    (mv (cons s ss) (cons r rs)))
                (b* ((r (pfield::mul r-prev r-prev p)))
                  (mv ss (cons r rs)))))))
   ///

   (more-returns
    (ss true-listp :rule-classes :type-prescription))

   (defret len-of-ss-rs.rs
     (equal (len rs)
            (1- (len cs)))
     :hyp (consp cs))

   (more-returns
    (rs consp
        :hyp (and (equal (car (last cs)) 1)
                  (consp (cdr cs)))
        :rule-classes :type-prescription))

   (defret len-of-ss-rs.ss
     (equal (len ss)
            (field-pow-bits-const-slen cs))
     :hyp (and (bit-listp cs)
               (consp (cdr cs)))
     :hints (("Goal"
              :induct t
              :in-theory (enable field-pow-bits-const-slen))))))

; Now we prove the key relation between the two recursive calculations,
; namely that their first rs values are equal.
; These are the exponentiation: see theorem rs1-correctness above,
; so that is all that we need for the correctness of the gadget.

; First we show that the two functions calculate the same rs values,
; except for th extra one.

(defruledl rs1-vs-ss-rs
  (implies (equal (car (last cs)) 1)
           (equal (mv-nth 1 (ss-rs x cs p))
                  (butlast (rs1 x cs p) 1)))
  :induct (len cs)
  :enable (rs1 ss-rs)
  :disable (bitp
            butlast
            acl2::take-of-cons
            pfield::mul-associative
            pfield::mul-commutative-2)
  :prep-books ((include-book "std/lists/butlast" :dir :system)))

; This is a simple lemma about lists,
; saying that if a non-empty list is the same as
; another one with the last element removed,
; the the car's are the same.

(defruledl car-when-butlast
  (implies (and (consp l1)
                (equal l1 (butlast l2 1)))
           (equal (car l1)
                  (car l2))))

; Putting the above two together, we get the key relation we are after.

(defruledl car-of-ss-rs-is-car-of-rs1
  (implies (and (equal (car (last cs)) 1)
                (consp (cdr cs)))
           (equal (car (mv-nth 1 (ss-rs x cs p)))
                  (car (rs1 x cs p))))
  :use (rs1-vs-ss-rs consp-of-ss-rs.rs)
  :enable car-when-butlast)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we show that the gadget calculates the same thing as
; the function ss-rs above.
; Note the custom induction scheme,
; that cdr's on ss only if the first bit of cs is 0.
; Note also the :expand hint, motivated by the fact that
; just enabling ss-rs seems to lead to a long or nonterminating proof;
; the one expansion expressed by the :expand hint is in fact
; all that we need for the proof by induction.

(defruledl field-pow-bits-const-gadget-aux-implies-ss-rs
  (implies (and (symbolp x)
                (bit-listp cs)
                (equal (car (last cs)) 1)
                (consp (cdr cs))
                (symbol-listp ss)
                (equal (len ss) (field-pow-bits-const-slen cs))
                (symbol-listp rs)
                (equal (len rs) (1- (len cs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((x$ (lookup-equal x asg))
                (ss$ (lookup-equal-list ss asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-pow-bits-const-gadget-aux x cs ss rs p)
                       asg p)
                      (b* (((mv ss1$ rs1$) (ss-rs x$ cs p)))
                        (and (equal ss1$ ss$)
                             (equal rs1$ rs$))))))
  :induct (ind cs ss rs)
  :hints ('(:expand (ss-rs (lookup-equal x asg) cs p)))
  :enable (field-pow-bits-const-gadget-aux
           field-mul-gadget-correctness
           field-square-gadget-correctness
           lookup-equal-list
           field-pow-bits-const-slen)
  :disable cons-equal
  :prep-books ((include-book "std/lists/len" :dir :system)
               (include-book "arithmetic/top" :dir :system))
  :prep-lemmas
  ((defun ind (cs ss rs)
     (cond ((or (endp cs) (endp (cdr cs)) (endp (cddr cs))
                (endp rs) (endp (cdr rs)))
            nil)
           (t (if (equal (car cs) 1)
                  (if (endp ss)
                      nil
                    (ind (cdr cs) (cdr ss) (cdr rs)))
                (ind (cdr cs) ss (cdr rs))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Finally we put everything together to prove the soundness of the gadget.
; The gadget implies the calculation in ss-rs,
; whose first rs value is the same as calculated by rs1,
; whose correctness theorem asserts the desired property for the gadget.

(defruled field-pow-bits-const-soundness
  (implies (and (symbolp x)
                (bit-listp cs)
                (equal (car (last cs)) 1)
                (consp (cdr cs))
                (symbol-listp ss)
                (equal (len ss) (field-pow-bits-const-slen cs))
                (symbol-listp rs)
                (equal (len rs) (1- (len cs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((x$ (lookup-equal x asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (r1cs::r1cs-constraints-holdp
                       (field-pow-bits-const-gadget x cs ss rs p)
                       asg p)
                      (equal (car rs$)
                             (pfield::pow x$ (lebits=>nat cs) p)))))
  :do-not-induct t
  :use (field-pow-bits-const-gadget-aux-implies-ss-rs
        (:instance rs1-correctness (x (lookup-equal x asg))))
  :enable (field-pow-bits-const-gadget
           car-of-ss-rs-is-car-of-rs1))
