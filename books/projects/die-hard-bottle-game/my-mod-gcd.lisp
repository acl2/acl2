; Copyright (C) 2005, Regents of the University of Texas
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "my-mod-gcd")

(in-package "ACL2")

(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "arithmetic/mod-gcd" :dir :system)

; My goal is to prove

#|
(defthm equal-ring-products
  (implies (and (natp i)
                (natp j)
                (natp p)
                (natp q)
                (< 0 q))
           (equal (equal (nonneg-int-mod (* i p) q)
                         (nonneg-int-mod (* j p) q))
                  (equal (nonneg-int-mod (* i (nonneg-int-gcd p q)) q)
                         (nonneg-int-mod (* j (nonneg-int-gcd p q)) q)))))
|#

; I asked John Cowles for help with a slightly simpler version of this,
; where the gcd of p and q is 1.  He provided me with the
; following proof sketch:

; [Cowles wrote, 29 Dec 2005]

;   Here is an abstract version of the argument stated in terms of the
;   congruence relation mod q. I believe a version of this argument can
;   be carried out using the events in mod-gcd.lisp in the ACL2
;   arithmetic directory. Please ask if you want a better outline of the
;   proof.

;   Recall two integers i and j are congruent mod q iff q divides i-j,
;   i.e.  (mod (- i j) q) = 0 iff (exists integer d)[(- i j) = (* q d)]
;   iff (mod i q) = (mod j q).

;   Recall that the congruence relation mod q is really a congruence
;   relation with respect to integer addition and multiplication.

;   Since (equal (mod (* i p) q)
;                (mod (* j p) q)),
;   then (* i p) is congruent to (* j p)(mod q).

;   Since (equal (gcd p q) 1), there is an integer a such that that (* p
;   a) is congruent to 1 (mod q). That is, a acts like a multiplicative
;   inverse for p (mod q). [This follows because the gcd of any two
;   integers can be written as a linear combination of the integers.]

;   Then      (* i p) is congruent to (* j p)(mod q)
;   implies   (* i p a) is congruent to (* j p a)(mod q)
;   implies   (* i (* p a)) is congruent to (* j (* p a))(mod q)
;   implies   (* i 1) is congruent to (* j 1)(mod q)
;   implies   i is congruent to j (mod q)

; I tried to formalize this proof by defining an equivalence relation,
; eqmod, that was

; (equal (nonneg-int-mod x (modulus))
;        (nonneg-int-mod y (modulus)))

; where (modulus) is some positive integer.  This doesn't work because
; (defcong eqmod eqmod (+ i j) 1) isn't a theorem unless I know i and
; j are naturals.  I really need congruence lemmas that provide
; hypotheses.  I can't fake it by coercing the x and y of eqmod to
; naturals because by the time eqmod gets its arguments, non-integers
; will have been swallowed by the (+ i j).

; I see no viable approach but to work this as rewrite rules targeting
; nonneg-int-mod expressions.

(defun
   induct-on-nonneg-int ( j )
   (if (zp j)
       t
       (induct-on-nonneg-int (- j 1))))

; The next four theorems allow us to simplify (+ x (* j n)) mod n to x
; mod n, for various combinations of placements of n.

(defthm Nonneg-int-mod-+-*-1
  (implies (and (natp j)
		(natp n)
                (< 0 n)
                (natp x))
	   (equal (nonneg-int-mod (+ x (* j n)) n)
		  (nonneg-int-mod x n)))
  :hints (("Goal"
           :induct (induct-on-nonneg-int j))))

(defthm Nonneg-int-mod-+-*-2
  (implies (and (natp j)
		(natp n)
                (< 0 n)
                (natp x)
                (natp y))
	   (equal (nonneg-int-mod (+ x y (* j n)) n)
		  (nonneg-int-mod (+ x y) n)))
  :hints (("Goal"
           :in-theory (disable Nonneg-int-mod-+-*-1)
           :use (:instance Nonneg-int-mod-+-*-1
                           (x (+ x y))))))

(defthm Nonneg-int-mod-+-*-3
  (implies (and (natp j)
		(natp n)
                (< 0 n)
                (natp x))
	   (equal (nonneg-int-mod (+ x (* n j)) n)
		  (nonneg-int-mod x n))))

(defthm Nonneg-int-mod-+-*-4
  (implies (and (natp j)
		(natp n)
                (< 0 n)
                (natp x)
                (natp y))
	   (equal (nonneg-int-mod (+ x y (* n j)) n)
		  (nonneg-int-mod (+ x y) n))))

(defthm Nonneg-int-mod-+-*-5
  (implies (and (natp j1)
                (natp j2)
		(natp n)
                (< 0 n)
                (natp x))
	   (equal (nonneg-int-mod (+ x (* j1 n j2)) n)
		  (nonneg-int-mod x n)))
  :hints (("Goal" :in-theory (disable Nonneg-int-mod-+-*-3)
           :use (:instance Nonneg-int-mod-+-*-3 (j (* j1 j2))))))


(defthm nonneg-int-mod-bound
  (implies (and (natp n)
                (< 0 n))
           (< (nonneg-int-mod x n) n))
  :rule-classes (:generalize))

; I call this the weak theorem because it's really an equivalence, but
; I haven't proved the other direction, yet.

(defthm eqmod-+-congruence-weak
  (implies (and (natp x)
                (natp y)
                (natp z)
                (equal (nonneg-int-mod x n)
                       (nonneg-int-mod y n)))
           (equal
            (equal (nonneg-int-mod (+ x z) n)
                   (nonneg-int-mod (+ y z) n))
            t))
  :rule-classes nil)

; Note:  The theorem above is essentially
; (defcong equal-mod-n equal-mod-n (+ x z) 1)
; except it has the hypotheses that x, z, and n are nats.

; The other direction can be proved using weak congruence and the fact
; that each element, x, of the ring has an additive inverse in the
; ring.  Suppose the additive inverse of x is written -x.  Then here
; is a proof sketch for the other direction.

; Proof: Instantiate weak congruence, letting x be (+ x z), y be (+ y
; z), and z be -z.  The equivalence in the hypothesis is thus x + z =
; y + z (mod n).  The conclusion is x + z - z = y + z - z (mod n),
; which simplifies to x = y (mod n).  Q.E.D.

; To carry out this proof we need to develop the additive inverse.

; This function takes a nat, x, and produces its negative in the ring
; mod n.

(defun nonneg-minus (x n)
  (if (zp (nonneg-int-mod x n))
      0
    (- n (nonneg-int-mod x n))))

(defthm natp-nonneg-minus
  (implies (and (natp n)
                (< 0 n))
           (and (integerp (nonneg-minus x n))
                (<= 0 (nonneg-minus x n))))
  :rule-classes :type-prescription)

(defthm nonneg-minus-bound
  (implies (and (natp n)
                (< 0 n))
           (< (nonneg-minus x n) n))
  :rule-classes (:linear :generalize))

(defthm nonneg-int-mod-+--1
  (implies (and (natp i)
                (natp k)
                (natp n)
                (< 0 n)
                (<= (* n k) i))
           (equal (nonneg-int-mod (+ i (- (* k n))) n)
                  (nonneg-int-mod i n)))
  :hints (("Goal" :induct (induct-on-nonneg-int k))))

(defthm nonneg-int-mod-+--2
  (implies (and (natp (+ i (- j)))
                (natp k)
                (natp n)
                (< 0 n)
                (<= (* n k) (+ i (- j))))
           (equal (nonneg-int-mod (+ i (- j) (- (* k n))) n)
                  (nonneg-int-mod (+ i (- j)) n)))
  :hints (("Goal" :in-theory (disable nonneg-int-mod-+--1)
           :use (:instance nonneg-int-mod-+--1 (i (+ i (- j)))))))

(defthm nonneg-int-mod-+--3
  (implies (and (natp (+ i j))
                (natp k)
                (natp n)
                (< 0 n)
                (<= (* n k) (+ i j)))
           (equal (nonneg-int-mod (+ i j (- (* k n))) n)
                  (nonneg-int-mod (+ i j) n)))
  :hints (("Goal" :in-theory (disable nonneg-int-mod-+--1)
           :use (:instance nonneg-int-mod-+--1 (i (+ i j))))))

; I am not sure how this should be stored or used.

(defthm nonneg-minus-lemma
  (implies (and (natp i)
                (natp j)
                (natp n)
                (< 0 n)
                (<= j i))
           (equal (nonneg-int-mod (+ i (nonneg-minus j n)) n)
                  (nonneg-int-mod (- i j) n))))

(in-theory (disable nonneg-minus))

; Now I prove strong congruence.  Note that it requires two additional
; hypotheses, that n is a positive natural.  We will always have
; these.

(defthm eqmod-+-congruence-strong
  (implies (and (natp x)
                (natp y)
                (natp z)
                (natp n)
                (< 0 n))
           (equal
            (equal (nonneg-int-mod (+ x z) n)
                   (nonneg-int-mod (+ y z) n))
            (equal (nonneg-int-mod x n)
                   (nonneg-int-mod y n))))
  :hints (("Goal"
           :in-theory (disable nonneg-minus-lemma)
           :use ((:instance nonneg-minus-lemma (i (+ x z)) (j z))
                 (:instance nonneg-minus-lemma (i (+ y z)) (j z))
                 (:instance eqmod-+-congruence-weak)
                 (:instance eqmod-+-congruence-weak
                            (x (+ x z))
                            (y (+ y z))
                            (z (nonneg-minus z n)))))))

(defthm nonneg-minus-n-n
  (equal (nonneg-minus n n) 0)
  :hints (("Goal" :in-theory (enable nonneg-minus))))

(defun signify (x n)
  (if (integerp x)
      (if (< x 0)
          (nonneg-minus (- x) n)
        x)
    0))

#|
; I believe that

; ??? (include-book "ihs/quotient-remainder-lemmas" :dir :system)
; ??? (in-theory (disable quotient-remainder-functions))

(defthm integerp-+
  (implies (integerp i)
           (equal (integerp (+ i j))
                  (or (integerp j)
                      (not (acl2-numberp j))))))

(defthm nonneg-int-mod-is-mod
  (implies (and (integerp x)
                (natp n)
                (< 0 n))
           (equal (nonneg-int-mod (signify x n) n)
                  (mod x n)))
  :otf-flg t)

|#

(defthm eqmod-*-congruence-weak
  (implies (and (natp x)
                (natp y)
                (natp z)
                (natp n)
                (< 0 n)
                (equal (nonneg-int-mod x n)
                       (nonneg-int-mod y n)))
           (equal (nonneg-int-mod (* x z) n)
                  (nonneg-int-mod (* y z) n))))


(defthm note-1
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal (nonneg-int-gcd p q)
                  (+ (* p
                        (nonneg-int-gcd-multiplier1 p q))
                     (* q
                        (nonneg-int-gcd-multiplier2 p q)))))
  :hints (("Goal" :in-theory (enable Linear-combination-for-nonneg-int-gcd)))
  :rule-classes nil)

(defun fixnonneg (x n)
  (if (< x 0)
      (nonneg-minus (- x) n)
    x))

(defthm natp-fixnonneg
  (implies (and (integerp x)
                (natp q)
                (< 0 q))
           (natp (fixnonneg x q))))

(in-theory (disable eqmod-*-congruence-weak))

(defthm nonneg-minus-lemma-x
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                (< 0 n)
                (natp (+ x y)))
           (equal (nonneg-int-mod (+ x (fixnonneg y n)) n)
                  (nonneg-int-mod (+ x y) n))))

(defthm nonneg-minus-lemma-for-*
  (implies (and (natp x)
                (natp y)
                (natp z)
                (natp n)
                (< 0 n)
                (natp (+ z (* x (- y)))))
           (equal (nonneg-int-mod (+ z (* x (nonneg-minus y n))) n)
                  (nonneg-int-mod (+ z (* x (- y))) n)))
  :otf-flg t
  :hints
  (("Goal" :in-theory (enable nonneg-minus))
   ("Subgoal 2.1''"
    :in-theory (disable nonneg-int-mod-+--2
                        nonneg-int-mod-+-*-1)
    :use ((:instance nonneg-int-mod-+--2
                     (i z)
                     (j (* i x))
                     (k (* j x)))
          (:instance nonneg-int-mod-+-*-1
                     (x (+ z (- (* i x))))
                     (n n)
                     (j x))))
   ("Subgoal 1.1.1''"
    :in-theory (disable nonneg-int-mod-+--1)
    :use ((:instance nonneg-int-mod-+--1
                     (i (+ i (* j n)))
                     (k (* l x))
                     (n n))))))

(defthm nonneg-minus-lemma-y
  (implies (and (natp x)
                (integerp y)
                (integerp z)
                (natp n)
                (< 0 n)
                (natp (+ z (* x y))))
           (equal (nonneg-int-mod (+ z (* x (fixnonneg y n))) n)
                  (nonneg-int-mod (+ z (* x y)) n))))

(defthm nonneg-int-mod-+-*-gen-1
  (implies (and (natp x)
                (integerp y)
                (natp n)
                (< 0 n)
                (natp (+ x (* y n))))
           (equal (nonneg-int-mod (+ x (* y n)) n)
                  (nonneg-int-mod x n)))
  :hints (("Goal" :cases ((< y 0) (<= 0 y)))
          ("Subgoal 2''"
           :use (:instance nonneg-int-mod-+--1
                           (i x)
                           (k (- y)))
           :in-theory (disable nonneg-int-mod-+--1))))

(defthm nonneg-int-mod-+-*-gen-2
  (implies (and (natp x)
                (integerp y)
                (natp n)
                (< 0 n)
                (natp (+ x (* y n))))
           (equal (nonneg-int-mod (+ x (* n y)) n)
                  (nonneg-int-mod x n)))
  :hints (("Goal" :cases ((< y 0) (<= 0 y)))
          ("Subgoal 2''"
           :use (:instance nonneg-int-mod-+--1
                           (i x)
                           (k (- y)))
           :in-theory (disable nonneg-int-mod-+--1))))

(defthm case-split-on-natp-+
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q)
                (integerp a)
                (integerp b)
                (natp (+ (* p a)
                         (* q b))))
           (or (and (< a 0)
                    (< 0 b))
               (and (<= 0 a)
                    (<= 0 b))
               (and (< b 0)
                    (< 0 a))))
  :rule-classes nil)

(defthm note-2
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal (nonneg-int-mod (nonneg-int-gcd p q) q)
                  (nonneg-int-mod
                   (+ (* p
                         (fixnonneg (nonneg-int-gcd-multiplier1 p q) q))
                      (* q
                         (fixnonneg (nonneg-int-gcd-multiplier2 p q) q)))
                   q)))
  :hints (("Goal"
           :in-theory (enable Linear-combination-for-nonneg-int-gcd)
           :use ((:theorem (natp (nonneg-int-gcd p q)))
                 (:instance case-split-on-natp-+
                            (a (nonneg-int-gcd-multiplier1 p q))
                            (b (nonneg-int-gcd-multiplier2 p q))))))
  :rule-classes nil)

(defthm nonnegative-integer-quotient-nonneg-int-mod
  (implies (and (natp x)
                (natp n)
                (< 0 n)
                (equal (nonneg-int-mod x n) 0))
           (equal (* (nonnegative-integer-quotient x n) n) x))
  :rule-classes nil)

(defthm note-3
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal p (* (nonnegative-integer-quotient p (nonneg-int-gcd p q))
                       (nonneg-int-gcd p q))))
  :hints (("Goal"
           :use ((:instance nonnegative-integer-quotient-nonneg-int-mod
                            (x p)
                            (n (nonneg-int-gcd p q))))))
  :rule-classes nil)

(in-theory (disable fixnonneg))

(defthm note-2x
  (implies (and (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal (nonneg-int-mod (nonneg-int-gcd p q) q)
                  (nonneg-int-mod
                   (* p (fixnonneg (nonneg-int-gcd-multiplier1 p q) q))
                   q)))
  :hints (("Goal" :use note-2))
  :rule-classes nil)

(defthm main-lemma-lhs-implies-rhs
  (implies (and (natp i)
                (natp j)
                (natp p)
                (natp q)
                (< 0 p)
                (< 0 q)
                (equal (nonneg-int-mod (* i p) q)
                       (nonneg-int-mod (* j p) q)))
           (equal (nonneg-int-mod (* i (nonneg-int-gcd p q)) q)
                  (nonneg-int-mod (* j (nonneg-int-gcd p q)) q)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (note-2x
          (:instance eqmod-*-congruence-weak
                     (x (nonneg-int-gcd p q))
                     (y (* p (fixnonneg (nonneg-int-gcd-multiplier1 p q) q)))
                     (z i)
                     (n q))
          (:instance eqmod-*-congruence-weak
                     (x (nonneg-int-gcd p q))
                     (y (* p (fixnonneg (nonneg-int-gcd-multiplier1 p q) q)))
                     (z j)
                     (n q))
          (:instance eqmod-*-congruence-weak
                     (x (* i p))
                     (y (* j p))
                     (z (fixnonneg (nonneg-int-gcd-multiplier1 p q) q))
                     (n q))))))

(defthm main-lemma-rhs-implies-lhs
  (implies (and (natp i)
                (natp j)
                (natp p)
                (natp q)
                (< 0 p)
                (< 0 q)
                (equal (nonneg-int-mod (* i (nonneg-int-gcd p q)) q)
                       (nonneg-int-mod (* j (nonneg-int-gcd p q)) q)))
           (equal (nonneg-int-mod (* i p) q)
                  (nonneg-int-mod (* j p) q)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-GCD)
    :use (note-3
          (:instance eqmod-*-congruence-weak
                     (x (* i (nonneg-int-gcd p q)))
                     (y (* j (nonneg-int-gcd p q)))
                     (z (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P Q)))
                     (n q))))))

(defthm main-lemma
  (implies (and (natp i)
                (natp j)
                (natp p)
                (natp q)
                (< 0 p)
                (< 0 q))
           (equal (equal (nonneg-int-mod (* i p) q)
                         (nonneg-int-mod (* j p) q))
                  (equal (nonneg-int-mod (* i (nonneg-int-gcd p q)) q)
                         (nonneg-int-mod (* j (nonneg-int-gcd p q)) q))))
  :rule-classes nil
  :hints (("Goal"
           :use (main-lemma-rhs-implies-lhs
                 main-lemma-lhs-implies-rhs))))

; Proof Sketch

; Let
; g  be (nonneg-int-gcd p q)
; a  be (nonneg-int-gcd-multiplier1 p q)
; b  be (nonneg-int-gcd-multiplier2 p q)
; a1 be (fixnonneg a)
; b1 be (fixnonneg b)
; c  be (nonnegative-integer-quotient p (nonneg-int-gcd p q))

; Note 1:  g = a*p + b*q.
; Note 2:  g = (a1*p + b1*q)  (mod q)
; Note 3:  p = c * g

; Let's take the two directions.  First, let us show the lhs implies
; the rhs.

; Given

; i*p = j*p [mod q]                            {lhs}

; We simplify rhs:

; (i*g = j*g) [mod q]                          {rhs}
; =                                            {Note 2}
; (i*(a1*p + b1*q) = j*(a1*p + b1*q)) [mod q]
; =                                            {arith}
; (i*a1*p + i*b1*q) = (j*a1*p + j*b1*q) [mod q]
; =
; (i*a1*p = j*a1*p) [mod q]                    {rhs'}

; But lhs -> rhs', by * congruence and the fact that a1 is a natural.

; Now we show rhs implies lhs.

; Given

; (i*g = j*g) [mod q]                          {rhs}

; But p = c*g, where c is a natural, thus, by * congruence,

; (i*c*g = j*c*g) [mod q]
; =
; (i*p = j*p) [mod q]                          {lhs}

; Q.E.D.

(defthm nonneg-int-mod-*-*
  (implies (and (natp i)
                (natp j)
                (natp k)
                (< 0 i)
                (< 0 k))
           (equal (nonneg-int-mod (* j i) (* k i))
                  (* i (nonneg-int-mod j k)))))

(encapsulate
 nil
 (local
  (defthm identity-reduction-lemma1
    (IMPLIES
     (AND (EQUAL (NONNEG-INT-MOD (* i P) Q)
                 (NONNEG-INT-MOD (* J P) Q))
          (EQUAL (NONNEG-INT-MOD (* I x)
                                 Q)
                 (NONNEG-INT-MOD (* J x)
                                 Q))
          (EQUAL Q
                 (* x
                    a))
          (natp x)
          (< 0 x)
          (natp a)
          (NATP I)
          (NATP J)
          (NATP P)
          (< 0 P)
          (< 0 Q))
     (EQUAL
      (NONNEG-INT-MOD I
                      a)
      (NONNEG-INT-MOD J
                      a)))
    :rule-classes nil))

 (defthm identity-reduction
   (implies
    (and (natp i)
         (natp j)
         (natp p)
         (natp q)
         (< 0 p)
         (< 0 q))
    (equal
     (equal (nonneg-int-mod (* i p) q)
            (nonneg-int-mod (* j p) q))
     (equal
      (nonneg-int-mod i
                      (nonnegative-integer-quotient q (nonneg-int-gcd p q)))
      (nonneg-int-mod j
                      (nonnegative-integer-quotient q (nonneg-int-gcd p q))))))
   :rule-classes nil
   :hints
   (("Goal"
     :in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-GCD)
     :use (main-lemma
           (:instance note-3
                      (p q)
                      (q p))
           (:instance identity-reduction-lemma1
                      (x (nonneg-int-gcd p q))
                      (a (nonnegative-integer-quotient
                          q
                          (nonneg-int-gcd p q)))))))))
