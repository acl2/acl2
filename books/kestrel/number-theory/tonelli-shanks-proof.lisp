; Number Theory Library
; Tonelli-Shanks Square Root
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
; Contributing Authors:
;   Eric McCarthy (mccarthy@kestrel.edu)
;   Alessandro Coglio (coglio@kestrel.edu),
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/number-theory/tonelli-shanks" :dir :system)

(defxdoc+ tonelli-shanks-algorithm-is-correct
  :parents (tonelli-shanks-modular-sqrt-algorithm)
  :short "Proof of correctness of the Tonelli-Shanks Modular Square Root Algorithm."
  :long "<h3> Overview </h3>

         <p> Below are the key lemmas and proof of correctness of the
         Tonelli-Shanks modular square root algorithm.</p>

         <h3>Theorems </h3>
         <p>Key lemmas:</p>

         @(thm y^2=1modp)
         @(thm least-repeated-square-equiv)
         @(thm least-repeated-square-tt^2^lrs=1)
         @(thm least-repeated-square-is-least)

         <p>Theorem about loop invariants of the algorithm:</p>
         @(thm t-s-aux-loop-invariants)

         <p>Base case theorem:</p>
         @(thm t-s-aux-base-case)

         <p> Assuming some properties about the loop invariants and using the
         theorems t-s-aux-loop-invariants, t-s-aux-base-case, we can prove the
         following theorem about t-s-aux function of the Tonelli-Shanks
         algorithm. </p>

         @(thm t-s-aux-equiv)

         <p> Proof that the algorithm returns the square root of n modulo p if
         a square root exists for n modulo p: </p>

         @(thm tonelli-shanks-sqrt-aux-is-sqrt-modp)

         <p>Key lemma required to prove that the algorithm is correct: </p>

         @(thm modx^2-y^2)

         <p> Proof that the Tonelli-Shanks modular square root
         algorithm is correct: </p>

         @(thm tonelli-shanks-sqrt-aux-is-correct)")

(local
 (encapsulate
   ()
   (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))

   (defthm mod-of-expt-of-mod
     (implies (and (natp i)
                   (integerp x)
                   (posp y))
              (equal (mod (expt (mod x y) i) y)
                     (mod (expt x i) y))))

   (defthm mod-of-*-of-expt-of-mod
     (implies (and (natp i)
                   (integerp x1)
                   (integerp x2)
                   (posp y))
              (equal (mod (* x1 (expt (mod x2 y) i)) y)
                     (mod (* x1 (expt x2 i)) y))))

   (defthm natp-2^x
     (implies (natp x)
              (natp (expt 2 x)))
     )
   ))

(local
 (encapsulate
   ()

   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))

   (defthm exponents-add-for-nonneg-exponents
     (implies (and (<= 0 i)
                   (<= 0 j)
                   (integerp i)
                   (integerp j))
              (equal (* (expt r i) (expt r j))
                     (expt r (+ i j)))))

   (defthm expt-half-linear
     (implies (natp i)
              (equal (+ (expt 2 (+ -1 i))
                        (expt 2 (+ -1 i)))
                     (expt 2 i))))

   (defthm exponents-multiply
     (implies (and (integerp i)
                   (integerp j))
              (equal (expt (expt r i) j)
                     (expt r (* i j)))))

   (defthm posp!=0
     (implies (posp x)
              (not (= x 0))))
   ))


(local
 (encapsulate
   ()

   (local
    (defthm lrs-aux-lemma-1
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (< (+ i 1) m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (equal (least-repeated-square-aux (+ i 1) tt^2^i m p) 0))))

   (local
    (defthm lrs-aux-lemma-2
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (equal (least-repeated-square-aux (- m 1) tt^2^i m p) 0))
      :hints (("Goal"
               :use ((:instance least-repeated-square-aux (i m)
                                (tt^2^i (mod (* tt^2^i tt^2^i) p))
                                (m m)
                                (p p)))
               :do-not-induct t
               ))))

   (local
    (defthm lrs-aux-lemma-3
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< 2 p)
                    (< i m)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0)
                    (>= x i)
                    (<= x (- m 1)))
               (equal (least-repeated-square-aux x tt^2^i m p) 0))))

   (local
    (defthm lrs-aux-lemma-4-1
      (implies (and (integerp i)
                    (< 0 i)
                    (integerp m)
                    (<= 0 m)
                    (< i m)
                    (not (equal (mod (* tt^2^i tt^2^i) p) 1))
                    (not (equal (mod (expt (* tt^2^i tt^2^i)
                                           (expt 2 (+ -1 (- i) m)))
                                     p)
                                1))
                    (integerp tt^2^i)
                    (<= 0 tt^2^i)
                    (integerp p)
                    (<= 0 p)
                    (< 2 p)
                    (equal (least-repeated-square-aux (+ 1 i)
                                                      (mod (* tt^2^i tt^2^i) p)
                                                      m p)
                           0))
               (not (equal (mod (expt tt^2^i (expt 2 (+ (- i) m)))
                                p)
                           1)))
      :hints (("Goal"
               :use ((:instance exponents-multiply (i 2) (j (expt 2 (+ -1 (- i) m)))
                                (r tt^2^i))
                     (:instance exponents-add-for-nonneg-exponents (r 2) (i 1)
                                (j (+ -1 (- i) m))))
               ))))

   (local
    (defthm lrs-aux-lemma-4
      (implies (and (natp tt^2^i)
                    (posp i)
                    (natp m)
                    (natp p)
                    (< i m)
                    (< 2 p)
                    (equal (least-repeated-square-aux i tt^2^i m p) 0))
               (not (equal (mod (expt tt^2^i (expt 2 (- m i))) p) 1)))))

   (encapsulate
     ()

     (local (include-book "arithmetic-5/top" :dir :system))

     (defthmd least-repeated-square-aux-lemma5
       (implies (and (natp tt^2^i)
                     (posp i)
                     (natp m)
                     (natp p)
                     (< i m)
                     (< 2 p)
                     (equal (least-repeated-square-aux 1 tt^2^i m p) 0))
                (not (equal (mod (expt tt^2^i (expt 2 i)) p) 1)))
       :hints (("Goal"
                :use ((:instance lrs-aux-lemma-3 (tt^2^i tt^2^i)
                                 (i i)
                                 (m m)
                                 (p p)
                                 (x (- m i)))
                      (:instance lrs-aux-lemma-4 (tt^2^i tt^2^i)
                                 (i (- m i))
                                 (m m)
                                 (p p)))
                ))))
   ))

(local
 (encapsulate
   ()

   (local (include-book "rtl/rel11/lib/basic" :dir :system))
   (local (include-book "arithmetic/equalities" :dir :system))
   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm integerp-mod
     (implies (and (integerp m)
                   (integerp n))
              (integerp (mod m n))))

   (defthm mod-*a-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* a b) c)
                 (mod (* (mod a c) (mod b c)) c))))

   (defthm mod-*mod-a*mod-b=
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (= c 0)))
              (= (mod (* (mod a c) (mod b c)) c)
                 (mod (* a b) c)))
     :hints (("Goal"
              :use (:instance mod-*a-b= (a a) (b b) (c c))
              :in-theory nil
              )))

   (defthm mod-times-mod
     (implies (and (integerp a)
                   (integerp b)
                   (integerp c)
                   (not (zp n))
                   (= (mod a n) (mod b n)))
              (= (mod (* a c) n) (mod (* b c) n)))
     :hints (("Goal"
              :use (:instance rtl::mod-times-mod (a a) (b b) (c c) (n n))
              :in-theory nil
              )))
   ))

(local
 (encapsulate
   ()
   (local (include-book "kestrel/number-theory/divides" :dir :system))
   (local (include-book "kestrel/crypto/ecurve/primes" :dir :system))

   (defthm primep-implies
     (implies (and (rtl::primep p)
                   (< 2 p))
              (and (oddp p)
                   (integerp p)))
     :hints (("Goal"
              :in-theory (e/d (rtl::primep) (oddp))
              ))
     )
   ))

(encapsulate
  ()

  (local (include-book "projects/quadratic-reciprocity/euclid" :dir :system))
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm y^2=1modp-lemma1
     (implies (and (integerp a)
                   (integerp b)
                   (rtl::primep p)
                   (rtl::divides p (* a b))
                   (not (rtl::divides p b)))
              (rtl::divides p a))
     :hints (("Goal"
              :use (:instance rtl::euclid (p p) (a a) (b b))
              ))))

  (local
   (defthm y^2=1modp-1
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (equal (mod (* y y) p) 1))
              (or (equal (mod y p) 1)
                  (equal (mod y p) (mod -1 p))))
     :hints (("Goal"
              :cases ((rtl::divides p (- y 1))
                      (rtl::divides p (+ y 1)))
              :use ((:instance rtl::divides-mod-equal (n p) (a (* y y)) (b 1))
                    (:instance y^2=1modp-lemma1 (a (- y 1)) (b (+ y 1)))
                    (:instance rtl::divides-mod-equal (n p) (a y) (b 1))
                    (:instance rtl::divides-mod-equal (n p) (a y) (b -1)))
              :in-theory (e/d (rtl::primep) ())
              ))))

  (local
   (defthm y^2=1modp-2
     (implies (and (rtl::primep p)
                   (integerp y)
                   (< 2 p)
                   (or (equal (mod y p) 1)
                       (equal (mod y p) (mod -1 p))))
              (equal (mod (* y y) p) 1))
     :hints (("Goal"
              :cases ((equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))
              :use ((:instance primep-implies (p p))
                    (:instance mod-*a-b= (a y) (b y) (c p))
                    (:instance mod-*mod-a*mod-b= (a y) (b y) (c p)))
              :in-theory (e/d () (mod))
              ))))

  (defthm y^2=1modp
    (implies (and (rtl::primep p)
                  (integerp y)
                  (< 2 p))
             (iff (equal (mod (* y y) p) 1)
                  (or (equal (mod y p) 1)
                      (equal (mod y p) (mod -1 p)))))
    :hints (("Goal"
             :use ((:instance y^2=1modp-1)
                   (:instance y^2=1modp-2))
             )))

  (defthm modx^2-y^2
    (implies (and (natp x)
                  (natp y)
                  (rtl::primep p)
                  (< 2 p)
                  (< x p)
                  (< y p)
                  (equal (mod (* x x) p) (mod (* y y) p)))
             (or (equal x y)
                 (equal x (mod (- y) p))))
    :hints (("Goal"
             :use ((:instance rtl::divides-mod-equal (n p) (a (* x x)) (b (* y y)))
                   (:instance y^2=1modp-lemma1 (p p) (a (+ x y)) (b (- x y)))
                   (:instance rtl::divides-mod-equal (n p) (a x) (b y))
                   (:instance rtl::divides-mod-equal (n p) (a x) (b (- y))))
             :in-theory (e/d () (mod-*a-b= mod-*mod-a*mod-b=))
             )))
  )

(encapsulate
  ()

  (local (include-book "kestrel/arithmetic-light/expt" :dir :system))

  (local
   (defthmd least-repeated-square-aux-lemma1
     (implies (and (posp i)
                   (< i m)
                   (natp x)
                   (< x i)
                   (natp tt^2^i)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (not (equal (least-repeated-square-aux i tt^2^i m p) 0)))
              (< x (least-repeated-square-aux i tt^2^i m p)))
     :hints (("Goal"
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
              ))))

  (local
   (defthm least-repeated-square-aux-lemma2
     (implies
      (and (integerp i)
           (<= 0 i)
           (integerp m)
           (<= 0 m)
           (< i m)
           (not (equal (mod (* tt tt) p) 1))
           (equal (mod (expt (mod (* tt tt) p)
                             (expt 2
                                   (+ (- i)
                                      (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p))))
                       p)
                  1)
           (< (+ 1 i) m)
           (integerp tt)
           (<= 0 tt)
           (< 0 m)
           (integerp p)
           (<= 0 p)
           (< 0 i)
           (< 2 p)
           (not (equal (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p) 0)))
      (equal (mod (expt tt
                        (expt 2
                              (+ 1 (- i)
                                 (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p))))
                  p)
             1))
     :hints (("Goal"
              :use ((:instance expt-half-linear
                               (i (+ (- i) (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p) 1)))
                    (:instance least-repeated-square-aux-lemma1 (i (+ i 1)) (x i)
                               (m m) (p p) (tt^2^i (mod (* tt tt) p))))
              :in-theory (e/d () (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
              ))))

  (defthmd least-repeated-square-aux-lemma3
    (implies (and (natp tt)
                  (posp m)
                  (natp p)
                  (posp i)
                  (< 2 p)
                  (equal (least-repeated-square-aux i tt m p) lrs)
                  (not (= lrs 0)))
             (and (= (mod (expt tt (expt 2 (+ lrs (- i) 1))) p) 1)
                  (< lrs m)
                  (< i m)))
    :hints (("Goal"
             :use ((:instance least-repeated-square-aux-lemma2))
             :in-theory (e/d (acl2::expt) (y^2=1modp primep-implies mod-*a-b= mod-*mod-a*mod-b= mod-times-mod))
             )))

  (local
   (defthmd least-repeated-square-aux-lemma4
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (equal (least-repeated-square-aux 1 tt m p) lrs)
                   (not (= lrs 0)))
              (and (= (mod (expt tt (expt 2 lrs)) p) 1)
                   (< lrs m)
                   (< 0 m)))
     :hints (("Goal"
              :use (:instance least-repeated-square-aux-lemma3 (i 1) (tt tt) (m m)
                              (p p) (lrs (least-repeated-square-aux 1 tt m p)))
              :in-theory (e/d (acl2::mod-expt-fast)
                              (y^2=1modp
                               primep-implies
                               mod-*a-b=
                               mod-*mod-a*mod-b=
                               mod-times-mod))))
     ))

  (defthm least-repeated-square-equiv
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square tt m p) lrs)
                  (not (= lrs 0)))
             (= (mod (expt tt (expt 2 lrs)) p) 1))
    :hints (("Goal"
             :use ((:instance least-repeated-square-aux-lemma4 (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p))))
             :in-theory (e/d (acl2::mod-expt-fast)
                             (y^2=1modp
                              primep-implies
                              mod-*a-b=
                              mod-*mod-a*mod-b=
                              mod-times-mod))
             )))

  (defthm least-repeated-square-tt^2^lrs=1
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (natp i)
                  (< i m)
                  (< 2 p)
                  (< 0 m)
                  (= (mod (expt tt (expt 2 i)) p) 1))
             (= (mod (expt tt (expt 2 (least-repeated-square tt m p))) p) 1))
    :hints (("Goal"
             :use (
                   (:instance least-repeated-square-aux-lemma3
                              (tt tt) (m m) (p p) (lrs i) (i i))
                   (:instance least-repeated-square-aux-lemma5
                              (tt^2^i tt) (m m) (p p) (i i))
                   (:instance least-repeated-square-aux-lemma4
                              (tt tt) (m m) (p p)
                              (lrs (least-repeated-square-aux 1 tt m p)))
                   )
             :in-theory (e/d (acl2::mod-expt-fast)
                             (y^2=1modp
                              primep-implies
                              mod-*a-b=
                              mod-*mod-a*mod-b=
                              mod-times-mod))))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm least-repeated-square-aux-is-least
     (implies (and (natp tt)
                   (natp m)
                   (natp p)
                   (< 2 p)
                   (equal (least-repeated-square-aux i tt m p) d)
                   (not (= d 0))
                   (posp i)
                   (< i d))
              (not (= (mod (expt tt (expt 2 (- d i))) p) 1)))
     :hints (("Goal"
              :use ((:instance exponents-multiply
                               (i 2)
                               (j (expt 2 (+ -1 (- i) (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p))))
                               (r tt))
                    (:instance exponents-add-for-nonneg-exponents (i 1)
                               (r 2)
                               (j (expt 2 (+ -1 (- i) (least-repeated-square-aux (+ 1 i) (mod (* tt tt) p) m p)))))
                    (:instance least-repeated-square-aux-lemma3 (tt tt) (m m) (p p)
                               (i i) (lrs (least-repeated-square-aux i tt m p))))
              :in-theory (e/d (acl2::mod-expt-fast least-repeated-square-aux)
                              (y^2=1modp
                               primep-implies
                               mod-*a-b=
                               mod-*mod-a*mod-b=
                               mod-times-mod))))))

  (defthm least-repeated-square-is-least
    (implies (and (natp tt)
                  (natp m)
                  (natp p)
                  (< 2 p)
                  (equal (least-repeated-square tt m p) d)
                  (not (= d 0)))
             (not (= (mod (expt tt (expt 2 (- d 1))) p) 1)))
    :hints (("Goal"
             :use (:instance least-repeated-square-aux-is-least (i 1) (tt tt) (m m) (p p) (d (least-repeated-square-aux 1 tt m p)))))))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
   (local (include-book "kestrel/number-theory/divides" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))

   (defthm t-s-aux-euler-criterion
     (implies (and (rtl::primep p)
                   (> p 2)
                   (integerp n)
                   (< n p)
                   (> n 0))
              (equal (mod (expt n (/ (- p 1) 2)) p)
                     (if (has-square-root? n p) 1 (mod -1 p))))
     :hints (("Goal"
              :use ((:instance mod-expt-fast-instance-meaning (m n) (p p))
                    (:instance residue-meaning (p p) (m n))
                    (:instance rtl::euler-criterion (p p) (m n))
                    )
              :in-theory (enable acl2::mod-expt-fast rtl::primep)
              )))

   (local
    (defthm lemma-1
      (implies (and (integerp a)
                    (integerp b)
                    (integerp c))
               (equal (expt a (* b (expt 2 (- c 1))))
                      (expt a (/ (* b (expt 2 c)) 2))))))

   (defthm t-s-aux-z-is-non-residue
     (implies (and (rtl::primep p)
                   (< 2 p)
                   (natp z)
                   (not (has-square-root? z p))
                   (< z p))
              (equal (mod (expt (expt z (mv-nth 0 (q*2^s (+ -1 p))))
                                (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p))))))
                          p)
                     (+ -1 p)))
     :hints (("Goal"

              :use ((:instance q2s-is-correct (n (- p 1)))
                    (:instance t-s-aux-euler-criterion (n z) (p p))
                    (:instance posp-q*2^s-n-is-even (n (- p 1)))
                    (:instance q*2^s-type-1 (n (- p 1)))
                    (:instance posp!=0 (x (mv-nth 1 (q*2^s (+ -1 p)))))
                    (:instance exponents-multiply
                               (r z)
                               (i (mv-nth 0 (q*2^s (+ -1 p))))
                               (j (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p)))))))
                    )
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
              )))

   (defthm t-s-aux-n-is-residue
     (implies (and (rtl::primep p)
                   (< 2 p)
                   (natp n)
                   (has-square-root? n p)
                   (> n 0)
                   (< n p))
              (equal (mod (expt (expt n (mv-nth 0 (q*2^s (+ -1 p))))
                                (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p))))))
                          p)
                     1))
     :hints (("Goal"

              :use ((:instance q2s-is-correct (n (- p 1)))
                    (:instance posp-q*2^s-n-is-even (n (- p 1)))
                    (:instance q*2^s-type-1 (n (- p 1)))
                    (:instance posp!=0 (x (mv-nth 1 (q*2^s (+ -1 p)))))
                    (:instance exponents-multiply
                               (r z)
                               (i (mv-nth 0 (q*2^s (+ -1 p))))
                               (j (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p)))))))
                    )
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp) ())
              )))
   ))

(local
 (encapsulate
   ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
   (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

   (defthm hyps-true-t-s-aux
     (implies (and (natp n)
                   (natp p)
                   (natp z)
                   (not (has-square-root? z p))
                   (< 2 p)
                   (< z p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (< 0 n)
                   (equal (mv-nth 1 (q*2^s (- p 1))) m)
                   (equal (mv-nth 0 (q*2^s (- p 1))) q)
                   (equal (acl2::mod-expt-fast z q p) c)
                   (equal (acl2::mod-expt-fast n q p) tt)
                   (equal (acl2::mod-expt-fast n (/ (+ q 1) 2) p) r)
                   (equal (least-repeated-square tt m p) m2))
              (and (posp m)
                   (natp c)
                   (natp tt)
                   (natp r)
                   (equal (mod (* r r) p) (mod (* tt n) p))
                   (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                   (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1)))
     :hints (("Goal"
              :use ((:instance least-repeated-square-tt^2^lrs=1
                               (m m)
                               (i (- m 1))
                               (p p))
                    (:instance posp-q*2^s-n-is-even (n (- p 1)))
                    (:instance posp!=0 (x (mv-nth 1 (q*2^s (+ -1 p)))))
                    (:instance mod-of-expt-of-mod (x (expt n (mv-nth 0 (q*2^s (+ -1 p)))))
                               (y p)
                               (i (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p)))))))
                    (:instance mod-of-expt-of-mod (x (expt z (mv-nth 0 (q*2^s (+ -1 p)))))
                               (y p)
                               (i (expt 2 (+ -1 (mv-nth 1 (q*2^s (+ -1 p)))))))
                    (:instance t-s-aux-z-is-non-residue (z z) (p p))
                    (:instance t-s-aux-n-is-residue (n n) (p p))
                    (:instance q2s-is-correct (n (- p 1))))
              :in-theory (e/d (acl2::mod-expt-fast acl2::not-evenp-when-oddp)
                              (y^2=1modp mod-*a-b= mod-*mod-a*mod-b= least-repeated-square mod-times-mod))
              :do-not-induct t
              )))))

(local
 (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (local
    (encapsulate
      ()

      (local (include-book "arithmetic-5/top" :dir :system))

      (defthm lemma1
        (implies (and (posp m)
                      (posp lrs)
                      (< lrs m))
                 (>= (+ -1 m (- lrs)) 0)))

      (defthm lemma2
        (implies (and (integerp c)
                      (natp m))
                 (integerp (expt c (expt 2 m)))))

      (defthm lemma3
        (implies (and (integerp a)
                      (integerp b)
                      (equal a (+ 1 b)))
                 (equal (- a 1) b)))))

   (defthmd t-s-aux-invariant1
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp m)
                   (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp r)
                   (equal (mod (* r r) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt m p) m2)
                   (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
              (if (zp m2)
                  (equal (mod (* r r) p) (mod n p))
                (let ((b (repeated-square c (- (- m m2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (r2 (mod (* r b) p)))
                    (declare (ignore r2 tt2))
                    (equal (mod (expt c2 (expt 2 (- m2 1))) p) (mod -1 p))
                    ))))
     :hints (("Goal"
              :cases ((= (- (- m m2) 1) 0))
              :use ((:instance repeated-square-equiv (x (+ -1 m (- (least-repeated-square tt m p)))) (p p) (c c))
                    (:instance lemma1 (m m) (lrs (least-repeated-square tt m p)))
                    (:instance mod-*a-b= (a n) (b tt) (c p))
                    (:instance natp-2^x (x (+ -1 m (- (least-repeated-square tt m p)))))
                    (:instance exponents-add-for-nonneg-exponents
                               (r c)
                               (i (expt 2 (+ -1 m (- (least-repeated-square tt m p)))))
                               (j (expt 2 (+ -1 m (- (least-repeated-square tt m p))))))
                    (:instance expt-half-linear (i  (+ m (- (least-repeated-square tt m p)))))

                    (:instance mod-*mod-a*mod-b=
                               (a (expt c (expt 2 (+ -1 m (- (least-repeated-square tt m p))))))
                               (b (expt c (expt 2 (+ -1 m (- (least-repeated-square tt m p))))))
                               (c p))
                    (:instance least-repeated-square-less-than-m (m m) (tt tt) (p p)))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square)
                              (y^2=1modp
                               mod-*a-b= mod-*mod-a*mod-b=
                               least-repeated-square hyps-true-t-s-aux
                               t-s-aux-n-is-residue t-s-aux-z-is-non-residue
                               least-repeated-square-is-least
                               least-repeated-square-tt^2^lrs=1 mod-times-mod))
              :do-not-induct t
              )))))

(local
 (encapsulate
   ()

   (local
    (encapsulate
      ()
      (local (include-book "arithmetic-5/top" :dir :system))

      (defthm lemma1
        (implies (and (natp tt)
                      (posp m)
                      (natp c)
                      (rtl::primep p)
                      (< 2 p))
                 (natp (mod (* tt (expt c (expt 2 (+ -1 m (- (least-repeated-square tt m p)))))
                               (expt c (expt 2 (+ -1 m (- (least-repeated-square tt m p))))))
                            p))))

      (defthm lemma2
        (implies (and (integerp a)
                      (integerp b)
                      (< a b))
                 (<= (+ a 1) b)))

      (defthm lemma3
        (implies (and (natp tt)
                      (posp m)
                      (natp c)
                      (rtl::primep p)
                      (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                      (< 2 p))
                 (equal
                  (mod
                   (expt (mod (* tt (expt c (expt 2 (+ -1  m (- (least-repeated-square tt m p)))))
                                 (expt c (expt 2 (+ -1 m (- (least-repeated-square tt m p))))))
                              p)
                         (expt 2 (+ -1 (least-repeated-square tt m p))))
                   p)
                  1))
        :hints (("Goal"
                 :use ((:instance least-repeated-square-is-least
                                  (tt tt) (m m) (p p)
                                  (d (least-repeated-square tt m p)))
                       (:instance lemma2 (a (least-repeated-square tt m p)) (b m))
                       (:instance y^2=1modp (y (expt tt
                                                     (expt 2
                                                           (+ -1 (least-repeated-square tt m p))))))
                       (:instance mod-*mod-a*mod-b= (a -1) (b -1) (c p))
                       (:instance mod-*a-b= (c p)
                                  (a (expt c (expt 2 (+ -1 m))))
                                  (b (expt tt
                                           (expt 2
                                                 (+ -1 (least-repeated-square tt m p)))))))
                 :in-theory (e/d (acl2::mod-expt-fast repeated-square)
                                 (y^2=1modp
                                  mod-times-mod mod-*a-b=
                                  mod-*mod-a*mod-b= least-repeated-square
                                  hyps-true-t-s-aux t-s-aux-n-is-residue
                                  t-s-aux-z-is-non-residue
                                  least-repeated-square-tt^2^lrs=1)))))

      (defthm lemma4
        (implies (and (posp m)
                      (posp lrs)
                      (< lrs m))
                 (>= (+ -1 m (- lrs)) 0)))

      (defthm lemma5
        (implies (and (integerp c)
                      (natp m))
                 (integerp (expt c (expt 2 m)))))

      (defthm lemma6
        (implies (integerp x)
                 (equal (* 1/2 (expt 2 x))
                        (expt 2 (- x 1)))))

      ))

   (local
    (defthmd t-s-aux-invariant2-lemma1
      (implies (and (posp n)
                    (< 2 p)
                    (rtl::primep p)
                    (< n p)
                    (has-square-root? n p)
                    (posp m)
                    (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                    (natp c)
                    (natp tt)
                    (natp r)
                    (equal (mod (* r r) p) (mod (* tt n) p))
                    (equal (least-repeated-square tt m p) m2)
                    (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
               (if (zp m2)
                   (equal (mod (* r r) p) (mod n p))
                 (let ((b (expt c (expt 2 (- (- m m2) 1)))))
                   (let ((c2 (mod (* b b) p))
                         (tt2 (mod (* tt b b) p))
                         (r2 (mod (* r b) p)))
                     (declare (ignore r2 c2))
                     (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 m2 p)) p) 1)))))
      :hints (("Goal"
               :use (
                     (:instance least-repeated-square-tt^2^lrs=1
                                (tt (mod (* tt (expt c (expt 2 (- (- m (least-repeated-square tt m p)) 1)))
                                            (expt c (expt 2 (- (- m (least-repeated-square tt m p)) 1)))) p))
                                (m (least-repeated-square tt m p))
                                (p p)
                                (i (- (least-repeated-square tt m p) 1)))
                     (:instance mod-*a-b= (a n) (b tt) (c p))
                     (:instance least-repeated-square-less-than-m (tt tt) (m m) (p p))
                     (:instance least-repeated-square-is-least
                                (tt tt) (m m) (p p)
                                (d (least-repeated-square tt m p)))
                     (:instance lemma2 (a (least-repeated-square tt m p)) (b m))
                     (:instance y^2=1modp (y (expt tt
                                                   (expt 2
                                                         (+ -1 (least-repeated-square tt m p))))))
                     (:instance mod-*mod-a*mod-b= (a -1) (b -1) (c p))
                     (:instance mod-*a-b= (c p)
                                (a (expt c (expt 2 (+ -1 m))))
                                (b (expt tt (expt 2 (+ -1 (least-repeated-square tt m p)))))))
               :in-theory (e/d (acl2::mod-expt-fast)
                               (repeated-square
                                y^2=1modp mod-times-mod
                                mod-*a-b= mod-*mod-a*mod-b=
                                least-repeated-square hyps-true-t-s-aux
                                t-s-aux-n-is-residue t-s-aux-z-is-non-residue
                                least-repeated-square-is-least
                                least-repeated-square-tt^2^lrs=1))
               :do-not-induct t
               )
              )))

   (local
    (encapsulate
      ()

      (local (include-book "arithmetic-5/top" :dir :system))
      (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
      (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
      (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

      (defthmd t-s-aux-invariant2-lemma2
        (implies (and (posp n)
                      (< 2 p)
                      (rtl::primep p)
                      (< n p)
                      (has-square-root? n p)
                      (posp m)
                      (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                      (natp c)
                      (natp tt)
                      (natp r)
                      (equal (expt c (expt 2 (- (- m m2) 1))) b1)
                      (equal (mod (* r r) p) (mod (* tt n) p))
                      (equal (least-repeated-square tt m p) m2)
                      (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
                 (if (zp m2)
                     (equal (mod (* r r) p) (mod n p))
                   (let ((b (repeated-square c (- (- m m2) 1) p)))
                     (let ((c2 (mod (* b b) p))
                           (tt2 (mod (* tt b b) p))
                           (r2 (mod (* r b) p)))
                       (declare (ignore r2 c2))
                       (equal tt2 (mod (* tt b1 b1) p))))))
        :hints (("Goal"
                 :use ((:instance lemma5 (c c) (m (- (- m m2) 1)))
                       (:instance lemma2 (a m2) (b m))
                       (:instance least-repeated-square-less-than-m (tt tt) (m m) (p p))
                       (:instance mod-*a-b= (a n) (b tt) (c p))
                       (:instance repeated-square-equiv (x (- (- m m2) 1)) (p p) (c c))
                       (:instance mod-of-*-of-expt-of-mod (i 2) (y p)
                                  (x1 tt) (x2 (expt c (expt 2 (- (- m m2) 1))))))
                 :in-theory
                 (e/d (acl2::mod-expt-fast repeated-square)
                      (y^2=1modp
                       mod-times-mod mod-*a-b= mod-*mod-a*mod-b=
                       least-repeated-square hyps-true-t-s-aux
                       t-s-aux-n-is-residue t-s-aux-z-is-non-residue
                       least-repeated-square-is-least
                       least-repeated-square-tt^2^lrs=1))
                 :do-not-induct t
                 )))))

   (defthmd t-s-aux-invariant2
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp m)
                   (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp r)
                   (equal (mod (* r r) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt m p) m2)
                   (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
              (if (zp m2)
                  (equal (mod (* r r) p) (mod n p))
                (let ((b (repeated-square c (- (- m m2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (r2 (mod (* r b) p)))
                    (declare (ignore r2 c2))
                    (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 m2 p)) p) 1)))))
     :hints (("Goal"
              :use ((:instance t-s-aux-invariant2-lemma2 (tt tt) (m m) (p p) (n n) (c c) (r r)
                               (m2 (least-repeated-square tt m p)) (b1 (expt c (expt 2 (- (- m m2) 1)))))
                    (:instance t-s-aux-invariant2-lemma1 (tt tt) (m m) (p p) (n n) (c c) (r r)
                               (m2 (least-repeated-square tt m p)))
                    )
              :in-theory
              (e/d (acl2::mod-expt-fast repeated-square)
                   (y^2=1modp
                    mod-times-mod
                    mod-*a-b= mod-*mod-a*mod-b=
                    least-repeated-square hyps-true-t-s-aux t-s-aux-n-is-residue
                    t-s-aux-z-is-non-residue least-repeated-square-is-least
                    least-repeated-square-tt^2^lrs=1))
              :do-not-induct t
              )))

   (local
    (encapsulate
      ()
      (local (include-book "arithmetic-5/top" :dir :system))
      (local (include-book "kestrel/arithmetic-light/integerp" :dir :system))
      (local (include-book "kestrel/arithmetic-light/even-and-odd" :dir :system))
      (local (in-theory (enable acl2::integerp-of-*-of-1/2-becomes-evenp)))

      (defthmd t-s-aux-invariant3-lemma1
        (implies (and (posp n)
                      (< 2 p)
                      (rtl::primep p)
                      (< n p)
                      (has-square-root? n p)
                      (posp m)
                      (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                      (natp c)
                      (natp tt)
                      (natp r)
                      (equal (mod (* r r) p) (mod (* tt n) p))
                      (equal (least-repeated-square tt m p) m2)
                      (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
                 (if (zp m2)
                     (equal (mod (* r r) p) (mod n p))
                   (let ((b (expt c (expt 2 (- (- m m2) 1)))))
                     (let ((c2 (mod (* b b) p))
                           (tt2 (mod (* tt b b) p))
                           (r2 (mod (* r b) p)))
                       (declare (ignore c2))
                       (equal (mod (* r2 r2) p) (mod (* tt2 n) p))))))
        :hints (("Goal"
                 :use ((:instance mod-times-mod (a (expt r 2)) (b (* n tt))
                                  (c (expt c (expt 2 (+ m (- (least-repeated-square tt m p))))))
                                  (n p)))
                 :in-theory (e/d (acl2::mod-expt-fast
                                  repeated-square
                                  acl2::not-evenp-when-oddp)
                                 (y^2=1modp
                                  mod-times-mod mod-*a-b=
                                  mod-*mod-a*mod-b= least-repeated-square
                                  hyps-true-t-s-aux t-s-aux-n-is-residue
                                  t-s-aux-z-is-non-residue
                                  least-repeated-square-is-least
                                  least-repeated-square-tt^2^lrs=1))
                 :do-not-induct t
                 )))))

   (defthmd t-s-aux-invariant3
     (implies (and (posp n)
                   (< 2 p)
                   (rtl::primep p)
                   (< n p)
                   (has-square-root? n p)
                   (posp m)
                   (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                   (natp c)
                   (natp tt)
                   (natp r)
                   (equal (mod (* r r) p) (mod (* tt n) p))
                   (equal (least-repeated-square tt m p) m2)
                   (= (acl2::mod-expt-fast tt (expt 2 m2) p) 1))
              (if (zp m2)
                  (equal (mod (* r r) p) (mod n p))
                (let ((b (repeated-square c (- (- m m2) 1) p)))
                  (let ((c2 (mod (* b b) p))
                        (tt2 (mod (* tt b b) p))
                        (r2 (mod (* r b) p)))
                    (declare (ignore c2))
                    (equal (mod (* r2 r2) p) (mod (* tt2 n) p))))))
     :hints (("Goal"
              :use ((:instance t-s-aux-invariant3-lemma1)
                    (:instance mod-of-*-of-expt-of-mod (i 1) (x2 (expt c (expt 2 (- (- m m2) 1))))
                               (x1 r) (y p))
                    (:instance repeated-square-equiv (x (- (- m m2) 1)) (p p) (c c))
                    (:instance t-s-aux-invariant2-lemma2 (tt tt) (m m) (p p) (n n) (c c) (r r)
                               (m2 (least-repeated-square tt m p)) (b1 (expt c (expt 2 (- (- m m2) 1))))))
              :in-theory (e/d (acl2::mod-expt-fast repeated-square)
                              (y^2=1modp
                               mod-times-mod mod-*a-b=
                               mod-*mod-a*mod-b= least-repeated-square
                               hyps-true-t-s-aux t-s-aux-n-is-residue
                               t-s-aux-z-is-non-residue
                               least-repeated-square-is-least
                               least-repeated-square-tt^2^lrs=1))
              :do-not-induct t
              )))))

(defthm t-s-aux-loop-invariants
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp m)
                 (natp c)
                 (natp tt)
                 (natp r)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p)
                 (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                 (= (acl2::mod-expt-fast tt (expt 2 (least-repeated-square tt m p)) p) 1)
                 (equal (mod (* r r) p) (mod (* tt n) p))
                 (< 0 (least-repeated-square tt m p)))
            (let ((b (repeated-square c (- (- m (least-repeated-square tt m p)) 1) p)))
              (let ((c2 (mod (* b b) p))
                    (tt2 (mod (* tt b b) p))
                    (r2 (mod (* r b) p)))
                (and (equal (mod (* r2 r2) p) (mod (* tt2 n) p))
                     (= (acl2::mod-expt-fast tt2 (expt 2 (least-repeated-square tt2 (least-repeated-square tt m p) p)) p) 1)
                     (equal (mod (expt c2 (expt 2 (- (least-repeated-square tt m p) 1))) p) (mod -1 p))
                     ))))
  :hints (("Goal"
           :use ((:instance t-s-aux-invariant1 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt m p)))
                 (:instance t-s-aux-invariant2 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt m p)))
                 (:instance t-s-aux-invariant3 (n n) (m m) (c c) (tt tt) (r r) (p p)
                            (m2 (least-repeated-square tt m p))))
           :in-theory (e/d (acl2::mod-expt-fast)
                           (repeated-square
                            y^2=1modp mod-times-mod mod-*a-b=
                            mod-*mod-a*mod-b= least-repeated-square
                            hyps-true-t-s-aux t-s-aux-n-is-residue
                            t-s-aux-z-is-non-residue
                            least-repeated-square-is-least
                            least-repeated-square-tt^2^lrs=1))
           :do-not-induct t
           )))

(defthm t-s-aux-base-case
  (implies (and (equal (least-repeated-square tt m p) 0)
                (integerp n)
                (< 0 n)
                (rtl::primep p)
                (equal (acl2::mod-expt-fast n (+ -1/2 (* 1/2 p))
                                            p)
                       1)
                (integerp m)
                (< 0 m)
                (integerp c)
                (<= 0 c)
                (integerp tt)
                (<= 0 tt)
                (integerp r)
                (<= 0 r)
                (<= 0 p)
                (< n p)
                (< 2 p)
                (equal (mod (expt c (expt 2 (+ -1 m))) p)
                       (+ -1 p))
                (equal (acl2::mod-expt-fast tt 1 p) 1)
                (equal (mod (* r r) p)
                       (mod (* n tt) p)))
           (equal (mod (* n tt) p) n))
  :hints (("Goal"
           :in-theory (e/d () (acl2::mod-expt-fast
                               repeated-square y^2=1modp
                               mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square
                               hyps-true-t-s-aux least-repeated-square-is-least
                               least-repeated-square-tt^2^lrs=1 mod expt rtl::mod acl2::expt))
           :use (:instance t-s-aux-invariant3
                           (n n) (p p) (m m) (c c) (tt tt) (r r)
                           (m2 (least-repeated-square tt m p))))))

(defthm t-s-aux-equiv
  (implies  (and (posp n)
                 (has-square-root? n p)
                 (posp m)
                 (natp c)
                 (natp tt)
                 (natp r)
                 (natp p)
                 (< n p)
                 (rtl::primep p)
                 (< 2 p)
                 (equal (mod (expt c (expt 2 (- m 1))) p) (mod -1 p))
                 (= (acl2::mod-expt-fast tt (expt 2 (least-repeated-square tt m p)) p) 1)
                 (equal (mod (* r r) p) (mod (* tt n) p)))
            (= (mod (* (t-s-aux m c tt r p) (t-s-aux m c tt r p)) p) n))
  :hints (("Goal"
           :in-theory (e/d () (acl2::mod-expt-fast
                               binary-* acl2::binary-*
                               repeated-square y^2=1modp mod-times-mod mod-*a-b=
                               mod-*mod-a*mod-b=
                               least-repeated-square hyps-true-t-s-aux
                               least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 mod
                               expt rtl::mod acl2::expt))
           :induct (t-s-aux m c tt r p)
           )))

(defthm tonelli-shanks-sqrt-aux-is-sqrt-modp
  (implies (and (natp n)
                (natp z)
                (> p 2)
                (< n p)
                (< z p)
                (rtl::primep p)
                (not (has-square-root? z p))
                (equal (tonelli-shanks-sqrt-aux n p z) y))
           (if (has-square-root? n p)
	       (equal (mod (* y y) p) n)
	     0))
  :hints (("Goal"
           :use ((:instance hyps-true-t-s-aux
                            (n n)
                            (p p)
                            (m (mv-nth 1 (q*2^s (- p 1))))
                            (q (mv-nth 0 (q*2^s (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                            (tt (acl2::mod-expt-fast n (mv-nth 0 (q*2^s (- p 1))) p))
                            (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p))
                            (m2 (least-repeated-square (acl2::mod-expt-fast n (mv-nth 0 (q*2^s (- p 1))) p)
                                                       (mv-nth 1 (q*2^s (- p 1))) p)))
                 (:instance t-s-aux-equiv
                            (n n)
                            (p p)
                            (m (mv-nth 1 (q*2^s (- p 1))))
                            (c (acl2::mod-expt-fast z (mv-nth 0 (q*2^s (- p 1))) p))
                            (tt (acl2::mod-expt-fast n (mv-nth 0 (q*2^s (- p 1))) p))
                            (r (acl2::mod-expt-fast n (/ (+ (mv-nth 0 (q*2^s (- p 1))) 1) 2) p))
                            )
                 )
           :in-theory (e/d (acl2::mod-expt-fast tonelli-shanks-sqrt-aux)
                           (repeated-square
                            y^2=1modp mod-times-mod mod-*a-b=
                            mod-*mod-a*mod-b= least-repeated-square hyps-true-t-s-aux
                            least-repeated-square-is-least least-repeated-square-tt^2^lrs=1 ))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm tonelli-shanks-sqrt-aux-is-correct
    (implies (and (natp n)
                  (natp z)
                  (> p 2)
                  (has-square-root? n p)
                  (< n p)
                  (< z p)
                  (rtl::primep p)
                  (not (has-square-root? z p))
                  (natp y)
                  (< y p)
                  (= (mod (* y y) p) n))
             (or (= (tonelli-shanks-sqrt-aux n p z) y)
                 (= (tonelli-shanks-sqrt-aux n p z) (- p y))))
    :hints (("Goal"
             :use ((:instance tonelli-shanks-sqrt-aux-is-sqrt-modp
                              (n n) (z z) (p p)
                              (y (tonelli-shanks-sqrt-aux n p z)))
                   (:instance modx^2-y^2 (x (tonelli-shanks-sqrt-aux n p z)) (y y) (p p))
                   (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                   (:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z)
                              (y (tonelli-shanks-sqrt-aux n p z))))
             :in-theory (e/d (acl2::mod-expt-fast tonelli-shanks-sqrt tonelli-shanks-lesser-sqrt)
                             (repeated-square
                              y^2=1modp mod-times-mod mod-*a-b=
                              mod-*mod-a*mod-b= least-repeated-square hyps-true-t-s-aux
                              least-repeated-square-is-least least-repeated-square-tt^2^lrs=1
                              modx^2-y^2 natp-tonelli-shanks-sqrt-aux))))))

(encapsulate
  ()

  (local
   (encapsulate
     ()
     (local (include-book "arithmetic-5/top" :dir :system))

     (defthm lemma1
       (implies (natp x)
                (and (integerp (- x))
                     (integerp x))))

     (defthm lemma2
       (implies (natp x)
                (equal (* (- x) (- x)) (* x x))))))

  (defthm tonelli-shanks-is-sqrt-modp
    (implies (and (natp n)
                  (natp z)
                  (> p 2)
                  (< n p)
                  (< z p)
                  (rtl::primep p)
                  (not (has-square-root? z p))
                  (equal (tonelli-shanks-sqrt n p z) y))
	     (if (has-square-root? n p)
		 (equal (mod (* y y) p) n)
	       0))
    :hints (("Goal"
             :use ((:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
		   (:instance tonelli-shanks-sqrt-aux-is-sqrt-modp
			      (n n) (p p) (z z) (y (tonelli-shanks-sqrt-aux n p z)))
                   (:instance mod-*mod-a*mod-b=
                              (a (- (tonelli-shanks-sqrt-aux n p z)))
                              (b (- (tonelli-shanks-sqrt-aux n p z)))
                              (c p)))
             :in-theory (e/d (acl2::mod-expt-fast tonelli-shanks-sqrt tonelli-shanks-lesser-sqrt)
                             (tonelli-shanks-sqrt-aux repeated-square y^2=1modp
                                                      mod-times-mod mod-*a-b= mod-*mod-a*mod-b=
                                                      least-repeated-square hyps-true-t-s-aux
                                                      least-repeated-square-is-least
                                                      least-repeated-square-tt^2^lrs=1 modx^2-y^2))))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm tonelli-shanks-is-correct
    (implies (and (natp n)
                  (natp z)
                  (> p 2)
                  (has-square-root? n p)
                  (< n p)
                  (< z p)
                  (rtl::primep p)
                  (not (has-square-root? z p))
                  (natp y)
                  (< y p)
                  (= (mod (* y y) p) n))
             (or (= (tonelli-shanks-sqrt n p z) y)
                 (= (tonelli-shanks-sqrt n p z) (- p y))))
    :hints (("Goal"
             :use ((:instance tonelli-shanks-is-sqrt-modp (n n) (z z) (p p)
                              (y (tonelli-shanks-sqrt n p z)))
                   (:instance modx^2-y^2 (x (tonelli-shanks-sqrt n p z)) (y y) (p p))
                   (:instance tonelli-shanks-sqrt-aux (n 0) (p p) (z z))
                   (:instance tonelli-shanks-sqrt-aux-is-posp<p (n n) (p p) (z z)
                              (y (tonelli-shanks-sqrt-aux n p z))))
             :in-theory (e/d (acl2::mod-expt-fast tonelli-shanks-sqrt tonelli-shanks-lesser-sqrt)
                             (tonelli-shanks-sqrt-aux
                              repeated-square y^2=1modp
                              mod-times-mod mod-*a-b= mod-*mod-a*mod-b= least-repeated-square
                              hyps-true-t-s-aux least-repeated-square-is-least
                              least-repeated-square-tt^2^lrs=1 modx^2-y^2
                              tonelli-shanks-is-sqrt-modp natp-tonelli-shanks-sqrt-aux))))))
