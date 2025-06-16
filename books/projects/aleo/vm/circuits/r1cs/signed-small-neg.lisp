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

(include-book "boolean-and")
(include-book "signed-small-sub-wrapped-const-var")
(include-book "zero")

(local (include-book "../library-extensions/bit-lists"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The snarkVM of this gadget performs a two's complement calculation:
; it negates the bits of the operand xs,
; and then it adds one to that, using checked addition.
; The resulting R1CS constraints,
; presumably due to the inherent optimizations with snarkVM's calculations,
; consists of one constraint for signed wrapped subtraction,
; one constraint for the boolean 'and' of the sign bits of operand and result,
; and one constraing requiring that boolean 'and' to be 0.

; This could be slightly optimized.
; Instead of introducing a variable for the 'and'
; and constraining it to be 0,
; we could directly constraint the 'and' (i.e. the product) to be 0.

(define signed-small-neg-gadget ((xs symbol-listp)
                                 (ys symbol-listp)
                                 (carry symbolp)
                                 (both-neg symbolp)
                                 (one symbolp)
                                 (p primep))
  :guard (and (consp xs)
              (equal (len ys) (len xs))
              (< (1+ (len xs)) (integer-length p)))
  :returns (constraints r1cs::r1cs-constraint-listp
                        :hyp :guard
                        :hints (("Goal" :cases ((consp ys)))))
  (append
   (signed-small-sub-wrapped-const-var-gadget
    (repeat (len xs) 0) xs ys carry one p)
   (boolean-and-gadget (car (last xs)) (car (last ys)) both-neg)
   (zero-gadget both-neg)))

; The reason why the gadget is sound is not too difficult,
; but involves the consideration of a few different cases.
; It starts with the soundness of the sub wrapped sub-gadget,
; which tells us that
;    I(y) mod 2^n = (-I(x)) mod 2^n
; where n is the size in bits of xs (and ys), and I is lebits=>int.
; We capture this into a macro.

(local
 (defmacro start ()
   `(and (bit-listp xs)
         (bit-listp ys)
         (consp xs)
         (consp ys)
         (equal (len ys) (len xs))
         (equal (mod (lebits=>int ys) (expt 2 (len xs)))
                (mod (- (lebits=>int xs)) (expt 2 (len xs)))))))

; From the other constraints we know that xs and ys are not both negative.
; So there are three cases to consider.

; The first case is that both xs and ys are non-negative,
; i.e. their sign bits are both 0.
; In this case, the formula from the sub wrapped sub-gadget above reduces to
;   N(y) mod 2^n = (-N(x)) mod 2^n
; where N is lebits=>nat.
; That implies
;   N(y) = 2^n - N(x)
; which can only hold if N(y) = N(x) = 0,
; because N(y) < 2^(n-1) while 2^n - N(x) > 2^(n-1).
; Thus, I(y) = N(y) = 0 = -0 = -N(x) = -I(x).
; If we use arithmetic-5 to try and prove this,
; at some point we reach a subgoal with the contradictory hypothesis
;   N(x) + N(y) = 2^n
; which is contradictory because both N(x) and N(y) are below 2^(n-1),
; and thus their sum cannot reach 2^n.

(defruledl case-xs-nonneg-and-ys-nonneg
  (implies (and (start)
                (equal (car (last xs)) 0)
                (equal (car (last ys)) 0))
           (equal (lebits=>int ys)
                  (- (lebits=>int xs))))
  :do-not-induct t
  :use (:instance plus-of-bounded-less-than-twice-bound
                  (x (lebits=>nat xs))
                  (y (lebits=>nat ys))
                  (c (expt 2 (1- (len xs)))))
  :expand (expt 2 (len xs))
  :enable (lebits=>int
           lebits=>nat-upper-bound-when-msb-is-0)
  :prep-books ((include-book "arithmetic-5/top" :dir :system))
  :prep-lemmas
  ((defruled plus-of-bounded-less-than-twice-bound
     (implies (and (natp x)
                   (natp y)
                   (natp c)
                   (< x c)
                   (< y c))
              (< (+ x y) (* 2 c))))))

; The second case is that xs is non-negative and ys is negative.
; In this case, the formula from the sub wrapped sub-gadget above reduces to
;   (N(y) - 2^n) mod 2^n = (-N(x)) mod 2^n
; which implies
;   N(y) = 2^n - N(x)
; which implies
;   I(y) = N(y) - 2^n = -N(x) = -I(x)
; If we try to prove this with arithmetic-5,
; we obtain a subgoal saying N(y) = 0,
; which cannot be because the sign bit of y is 1.
; So we prove a rewrite rule that turns N(y) = 0
; into the fact that y consists of all 0s,
; and a rewrite rule saying that the last bit of all 0 bits is 0.

(defruledl bits-lemma
  (implies (bit-listp bits)
           (equal (equal (lebits=>nat bits) 0)
                  (equal bits (repeat (len bits) 0))))
  :enable (lebits=>nat type-lemma)
  :use (:instance digits-lemma (base 2) (digits bits))
  :prep-lemmas
  ((defruled digits-lemma
     (implies (acl2::dab-digit-listp base digits)
              (equal (equal (acl2::lendian=>nat base digits) 0)
                     (equal digits (repeat (len digits) 0))))
     :enable (acl2::lendian=>nat repeat))
   (defruled type-lemma
     (implies (bit-listp x)
              (acl2::dab-digit-listp 2 x))
     :enable (acl2::dab-digit-listp))))

(defrulel car-of-last-of-repeat-of-all-0
  (implies (> (nfix n) 0)
           (equal (car (last (repeat n 0))) 0))
  :enable repeat)

(defruledl case-xs-nonneg-and-ys-neg
  (implies (and (start)
                (equal (car (last xs)) 0)
                (equal (car (last ys)) 1))
           (equal (lebits=>int ys)
                  (- (lebits=>int xs))))
  :do-not-induct t
  :enable (lebits=>int
           bits-lemma
           car-of-last-of-repeat-of-all-0)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

; The third case is that xs is negative and ys is non-negative.
; In this case, the formula from the sub wrapped sub-gadget above reduces to
;   N(y) mod 2^n = (-(N(x) - 2^n)) mod 2^n
; which implies
;   N(y) = 2^n - N(x)
; which implies
;   I(y) = N(y) = -(N(x) - 2^n) = -I(x)
; After attempting to prove with arithmetic-5,
; it turned out that it can be proved using mod and expt from arithmetic-light,
; but we also need the bits-lemma from above.

(defruledl case-xs-neg-and-ys-nonneg
  (implies (and (start)
                (equal (car (last xs)) 1)
                (equal (car (last ys)) 0))
           (equal (lebits=>int ys)
                  (- (lebits=>int xs))))
  :do-not-induct t
  :enable (lebits=>int
           bits-lemma)
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system)
               (include-book "kestrel/arithmetic-light/mod" :dir :system)))

; We finally prove soundness, using the lemmas above.
; But we also need a lemma to derive (consp ys) from (consp xs).
; We need the fact that the sign bits of xs and ys are bits,
; in order for boolean-and-gadget-to-bitand to fire,
; so we have two :use hints to insert these facts.

(defruledl consp-of-ys
  (implies (and (consp xs)
                (equal (len ys) (len xs)))
           (consp ys)))

(defruled signed-small-neg-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp carry)
                (symbolp both-neg)
                (symbolp one)
                (consp xs)
                (equal (len ys) (len xs))
                (< (1+ (len xs)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg both-neg)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (signed-small-neg-gadget
                                 xs ys carry both-neg one p)
                                asg p)
                               (and (bit-listp ys$)
                                    (equal (lebits=>int ys$)
                                           (- (lebits=>int xs$))))))))
  :do-not-induct t
  :use ((:instance signed-small-sub-wrapped-const-var-gadget-soundness
                   (cs (repeat (len xs) 0))
                   (ys xs)
                   (zs ys)
                   (z carry)
                   (one one)
                   (p p))
        consp-of-ys
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list xs asg)))
        (:instance bitp-of-car-of-last-when-bit-listp
                   (bits (lookup-equal-list ys asg)))
        (:instance case-xs-nonneg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance case-xs-nonneg-and-ys-neg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance case-xs-neg-and-ys-nonneg
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))))
  :enable (signed-small-neg-gadget
           boolean-and-gadget-to-bitand
           bitand
           zero-gadget-to-equal-0
           lookup-equal-of-car
           lookup-equal-list-of-last)
  :disable acl2::bitp-of-car-when-bit-listp)
