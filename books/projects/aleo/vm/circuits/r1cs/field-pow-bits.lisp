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

(include-book "if")
(include-book "field-square")
(include-book "field-mul")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/digits"))

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget raises a field element to
; the powers-of-two weighted sum of a non-empty sequence of bits.
; That is, given a field element,
; and a non-empty sequence of bits y(0), y(1), ..., y(n-1),
; this gadget computes
;   x ^ (y(0) + 2 * y(1) + 4 * y(2) + ... + 2^(n-1) * y(n-1)).
; Note that n may have any value, also much higher than
; the number of bits of the prime p:
; the exponent is an integer (not a field element),
; and exponentiation in prime fields is well-defined
; for any integer exponent.

; The gadget calculates the result
; by going through the bits of the exponent
; and squaring and multiplying in the well-known way.
; It is easier to explain the construction in a uniform way,
; and then show how it is slightly optimized in the actual gadget.

; This is the unoptimized calculation:
;
;   r(n) = 1
;
;   s(n-1) = r(n) * r(n)
;   p(n-1) = x * s(n-1)
;   r(n-1) = IF y(n-1) THEN p(n-1) ELSE s(n-1)
;
;   s(n-2) = r(n-1) * r(n-1)
;   p(n-2) = x * s(n-2)
;   r(n-2) = IF y(n-2) THEN p(n-2) ELSE s(n-2)
;
;   ...
;
;   s(0) = r(1) * r(1)
;   p(0) = x * s(0)
;   r(0) = IF y(0) THEN p(0) ELSE s(0)
;
; That is, starting from 1 in r(n),
; for each bit i we calculate
; the square s(i),
; the product p(i),
; and the result r(i).
; The final result is r(0), which is x raised to
; y = y(0) + 2 * y(1) + 4 * y(2) + ... + 2^(n-1) * y(n-1).

; The above equations can be slightly optimized
; by propagating and folding r(n) = 1 in the first triple of equations:
;
;   r(n) = 1
;
;   s(n-1) = r(n) * r(n) = 1 * 1 = 1
;   p(n-1) = x * s(n-1) = x * 1 = x
;   r(n-1) = IF y(n-1) THEN p(n-1) ELSE s(n-1) = IF y(n-1) THEN x ELSE 1
;
; The other constraints are unchanged.
; So we reduce the first 4 constraints
; (the one for r(n) and the first triple)
; to just one constraint for r(n-1) that only depends on y(n-1) and x,
; and omit s(n-1) and p(n-1):
;
;   r(n-1) = IF y(n-1) THEN x ELSE 1

; We calculate the constraints recursively with field-pow-bits-gadget-aux,
; but in the reverse order of above, and then field-pow-bits-gadget reverses
; them to get the order above.
;
; To facilitate recursively calculating the constraints in the reverse order,
; and to facilitate proofs about the computation,
; the variables in the lists ys, ss, ps, and rs, are all in the reverse order
; of their occurrence in the constraints above.
; E.g., the bit vars in the list ys are in little-endian form.
;
; Note that there are as many vars in rs as ys,
; but one less var in ss and ps than in ys.

(define field-pow-bits-gadget ((x symbolp)
                               (ys symbol-listp)
                               (ss symbol-listp)
                               (ps symbol-listp)
                               (rs symbol-listp)
                               (p primep))
  :guard (and (consp ys)
              (equal (len rs) (len ys))
              (equal (len ss) (1- (len ys)))
              (equal (len ps) (1- (len ys))))
  :returns (constraints r1cs::r1cs-constraint-listp :hyp :guard)
  (rev (field-pow-bits-gadget-aux x ys ss ps rs p))
  :prepwork
  ((define field-pow-bits-gadget-aux ((x symbolp)
                                      (ys symbol-listp)
                                      (ss symbol-listp)
                                      (ps symbol-listp)
                                      (rs symbol-listp)
                                      (p primep))
     :guard (and (consp ys)
                 (equal (len rs) (len ys))
                 (equal (len ss) (1- (len ys)))
                 (equal (len ps) (1- (len ys))))
     :returns (constraints r1cs::r1cs-constraint-listp :hyp :guard)
     (cond ((not (mbt (consp ys))) nil)
           ((endp (cdr ys))
            ;; Field::ternary in the snarkVM code:
            (if1-gadget (car ys) x (car rs) p))
           (t (append
               ;; Field::ternary in the snarkVM code:
               (if-gadget (car ys) (car ps) (car ss) (car rs) p)
               ;; &(&output * self) expression in the SnarkVM code,
               ;; [ but the multiplicands are coming out reversed,
               ;;   so we switch x and (car ss) here... this is a
               ;;   candidate for normalizing.]
               (field-mul-gadget (car ss) x (car ps))
               ;; output = output.square(); in the SnarkVM code:
               (field-square-gadget (cadr rs) (car ss))
               ;; recursion:
               (field-pow-bits-gadget-aux
                x (cdr ys) (cdr ss) (cdr ps) (cdr rs) p)))))))

; We introduce a function that describes
; the recursive computation of the ss, ps, and rs values from x and ys.
; In the function name, 'spr' refers to Square, Product, and Result.

(local
 (define spr ((x (pfield::fep x p)) (ys bit-listp) (p primep))
   :guard (consp ys)
   :returns (mv (ss (pfield::fe-listp ss p) :hyp (primep p))
                (ps (pfield::fe-listp ps p) :hyp (primep p))
                (rs (pfield::fe-listp rs p) :hyp (and (primep p)
                                                      (pfield::fep x p))))
   (cond ((not (mbt (consp ys))) (mv nil nil nil))
         ((endp (cdr ys)) (mv nil
                              nil
                              (list (if (equal (car ys) 1)
                                        x
                                      1))))
         (t (b* (((mv cdr-ss cdr-ps cdr-rs) (spr x (cdr ys) p))
                 (cadr-rs (car cdr-rs))
                 (car-ss (pfield::mul cadr-rs cadr-rs p))
                 (car-ps (pfield::mul car-ss x p))
                 (car-rs (if (equal (car ys) 1)
                             car-ps
                           car-ss)))
              (mv (cons car-ss cdr-ss)
                  (cons car-ps cdr-ps)
                  (cons car-rs cdr-rs)))))
   ///

   (defret len-of-spr-ss
     (equal (len ss)
            (1- (len ys)))
     :hyp (consp ys))

   (defret len-of-spr-ps
     (equal (len ps)
            (1- (len ys)))
     :hyp (consp ys))

   (defret len-of-spr-rs
     (equal (len rs)
            (len ys)))

   (defret consp-of-spr-rs
     (equal (consp rs)
            (consp ys)))))

; The following theorem links the gadget definition
; to the calculation described by the function spr.

(defruledl field-pow-bits-gadget-aux-to-spr
  (implies (and (symbolp x)
                (symbol-listp ys)
                (symbol-listp ss)
                (symbol-listp ps)
                (symbol-listp rs)
                (consp ys)
                (equal (len ss) (1- (len ys)))
                (equal (len ps) (1- (len ys)))
                (equal (len rs) (len ys))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg ps)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((x$ (lookup-equal x asg))
                (ys$ (lookup-equal-list ys asg))
                (ss$ (lookup-equal-list ss asg))
                (ps$ (lookup-equal-list ps asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (bit-listp ys$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-pow-bits-gadget-aux x ys ss ps rs p)
                                asg p)
                               (b* (((mv ss1$ ps1$ rs1$) (spr x$ ys$ p)))
                                 (and (equal ss$ ss1$)
                                      (equal ps$ ps1$)
                                      (equal rs$ rs1$)))))))
  :induct (ind ys ss ps rs)
  :enable (field-pow-bits-gadget-aux
           if1-gadget-to-if1
           if-gadget-to-if
           field-mul-gadget-correctness
           field-square-gadget-correctness
           if1
           spr
           lookup-equal-list)
  :disable (; for speed:
            cons-equal
            bitp
            default-car
            default-cdr
            acl2::len-when-not-consp-cheap
            len-of-lookup-equal-list
            append
            acl2::append-when-not-consp
            default-+-1
            default-+-2
            acl2::subsetp-member)
  :prep-lemmas
  ((defun ind (ys ss ps rs)
     (cond ((or (endp ys)
                (endp ss)
                (endp ps)
                (endp rs))
            nil)
           (t (ind (cdr ys) (cdr ss) (cdr ps) (cdr rs)))))))

; The following theorem shows that the recursive calculation is correct.
; That is, the function spr calculates the ss, ps, and rs sequences
; in a way that the car of rs is the power of x to the value of the ys bits.

(defruledl spr-correctness
  (implies (and (pfield::fep x p)
                (bit-listp ys)
                (primep p)
                (consp ys))
           (b* (((mv & & rs) (spr x ys p)))
             (equal (car rs)
                    (pfield::pow x (lebits=>nat ys) p))))
  :enable (spr len-lemma)
  :hints ('(:use induction-step))

  :prep-lemmas

  ((defruled induction-step-with-cons
     (implies (and (pfield::fep x p)
                   (bitp y)
                   (bit-listp ys)
                   (primep p))
              (implies (equal (car (mv-nth 2 (spr x ys p)))
                              (pfield::pow x (lebits=>nat ys) p))
                       (equal (car (mv-nth 2 (spr x (cons y ys) p)))
                              (pfield::pow x (lebits=>nat (cons y ys)) p))))
     :enable (spr acl2::lebits=>nat-of-cons)
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
     (implies (and (pfield::fep x p)
                   (bit-listp ys)
                   (primep p))
              (implies (equal (car (mv-nth 2 (spr x (cdr ys) p)))
                              (pfield::pow x (lebits=>nat (cdr ys)) p))
                       (equal (car (mv-nth 2 (spr x ys p)))
                              (pfield::pow x (lebits=>nat ys) p))))
     :use (:instance induction-step-with-cons (y (car ys)) (ys (cdr ys))))

   (defruled len-lemma
     (equal (equal (len l) 1)
            (and (consp l)
                 (not (consp (cdr l))))))))

; The soundness theorem for the gadget is proved
; by putting together the two previous theorems.

(defruled field-pow-bits-soundness
  (implies
   (and (symbolp x)
        (symbol-listp ys)
        (symbol-listp ss)
        (symbol-listp ps)
        (symbol-listp rs)
        (consp ys)
        (equal (len ss) (1- (len ys)))
        (equal (len ps) (1- (len ys)))
        (equal (len rs) (len ys))
        (primep p)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg x)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg ss)
        (r1cs::valuation-binds-allp asg ps)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((x$ (lookup-equal x asg))
        (ys$ (lookup-equal-list ys asg))
        (rs$ (lookup-equal-list rs asg)))
     (implies (bit-listp ys$)
              (implies (r1cs::r1cs-constraints-holdp
                        (field-pow-bits-gadget x ys ss ps rs p)
                        asg p)
                       (equal (car rs$)
                              (pfield::pow x$ (lebits=>nat ys$) p))))))
  :enable field-pow-bits-gadget
  :use (field-pow-bits-gadget-aux-to-spr
        (:instance spr-correctness
                   (x (lookup-equal x asg))
                   (ys (lookup-equal-list ys asg)))))
