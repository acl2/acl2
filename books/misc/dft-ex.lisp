; Copyright (C) 2014, Regents of the University of Texas
; Written by J Moore, 6/13/01
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; J Moore, 6/13/01

(include-book "dft")

(dft comm2-test-1
     (equal (* a (* b c)) (* b (* a c)))
     :rule-classes nil
     :otf-flg nil
     :proof
     ((consider (* a (* b c)))
      (= (* (* a b) c))
      (= (* (* b a) c) :disable (associativity-of-*))
      (= (* b (* a c)))))


(include-book "arithmetic/top-with-meta" :dir :system)

; Here I prove Euclid's theorem, that p|ab implies p|a or p|b, for prime p.  I
; defaxiom a few "basic" facts.  My point is to illustrate dft.

(progn
 (defstub primep (x) t)
 (defstub divides (x y) t)
 (defstub quotient (x y) t)
 (defstub my-gcd (x y) t)
 (defaxiom fact0
   (implies (and (integerp x)
                 (integerp y))
            (integerp (quotient x y))))
 (defaxiom fact1
   (implies (and (integerp x)
                 (integerp y))
            (integerp (my-gcd x y))))
 (defaxiom fact2
   (implies (and (integerp x)
                 (integerp y)
                 (divides x y))
            (equal (* x (quotient y x)) y)))
 (defaxiom fact3
   (implies (and (integerp x)
                 (integerp y)
                 (primep x)
                 (not (divides x y)))
            (equal (my-gcd x y) 1)))

 (defaxiom fact4
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z))
            (equal (my-gcd (* x y) (* x z))
                   (* x (my-gcd y z)))))
 (defaxiom fact5
   (implies (and (integerp x)
                 (integerp y))
            (divides x (* x y))))

 (dft prime-key
     (implies (and (integerp a)
                   (integerp b)
                   (integerp p)
                   (primep p)
                   (divides p (* a b)))
              (or (divides p a)
                  (divides p b)))
     :rule-classes nil
     :Proof
     ((Observe (equal (* p (quotient (* a b) p)) (* a b)))
      (Generalize (quotient (* a b) p) to i where (integerp i))
      (case (not (divides p a))
        (observe (equal 1 (my-gcd p a)))
        (consider b)
        (= (* b (my-gcd p a)))
        (= (my-gcd (* b p) (* b a)) :by fact4)
        (= (my-gcd (* p b) (* p i)))
        (= (* p (my-gcd b i)) :by fact4)
        (so-it-suffices-to-prove
         (implies (and (integerp a)
                       (integerp b)
                       (integerp p)
                       (integerp i))
                  (divides p (* p (my-gcd b i)))))
        (observe (divides p (* p (my-gcd b i))))))))

; This is a theorem similar to one I had a hard time proving during the
; K5 FDIV proof.

(dft abs-chain-proof-1
     (implies (and (rationalp x)
                   (rationalp y)
                   (rationalp c)
                   (<= c (+ x y))
                   (integerp i))
              (<= (* (expt 2 i) c)
                  (abs (+ (* (expt 2 i) x) (* (expt 2 i) y)))))
     :rule-classes nil
     :proof
     ((let e be (expt 2 i))
      (consider (* e c))
      (<= (* e (+ x y)))
      (= (+ (* e x) (* e y)))
      (<= (abs (+ (* e x) (* e y))) :enable abs)))

(dft abs-chain-proof-2
     (implies (and (rationalp x)
                   (rationalp y)
                   (rationalp c)
                   (<= c (+ x y))
                   (integerp i))
              (<= (* (expt 2 i) c)
                  (abs (+ (* (expt 2 i) x) (* (expt 2 i) y)))))
     :rule-classes nil
     :proof
     ((let e be (expt 2 i))
      (Observe (<= c (abs (+ x y))) :enable abs)
      (Consider (abs (+ (* e x) (* e y))))
      (= (abs (* e (+ x y))))
      (= (* e (abs (+ x y)))
         :proof
         ((observe (rationalp e))
          (observe (equal (abs e) e))
          (Theorem (implies (and (rationalp x)
                                 (rationalp y))
                            (equal (abs (* x y)) (* (abs x) (abs y))))
                   :enable abs)
          (Instantiate (x e) (y (+ x y)))))
      (Observe (<= (* e c)
                   (abs (+ (* e x) (* e y)))))))

(dft abs-chain-proof-3
     (implies (and (rationalp x)
                   (rationalp y)
                   (rationalp c)
                   (<= c (+ x y))
                   (integerp i))
              (<= (* (expt 2 i) c)
                  (abs (+ (* (expt 2 i) x) (* (expt 2 i) y)))))
     :rule-classes nil
     :proof
     ((let e be (expt 2 i))
      (let rhs be (abs (+ (* (expt 2 i) x) (* (expt 2 i) y))))
      (Observe (<= c (abs (+ x y))) :enable abs)
      (Consider rhs)
      (= (abs (* e (+ x y))))
      (= (* e (abs (+ x y)))
         :proof
         ((generalize (+ x y) to z where (rationalp z))
          (observe (equal (abs (* e z)) (* e (abs z))) :enable abs)))
      (observe (<= (* e c) rhs))))
