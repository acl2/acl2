(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/norm" :dir :system)
(local (include-book "nonstd/nsa/sqrt" :dir :system))


(local
 (defthm expt-sqrt-2
     (implies (and (realp x) (<= 0 x))
              (equal (expt (acl2-sqrt x) 2)
                     x))
   :hints (("Goal"
            :use ((:instance sqrt-sqrt))
            :in-theory (disable sqrt-sqrt)))))

(local
 (defthm square-positive
     (implies (realp x)
              (<= 0 (expt x 2)))
   :hints (("Goal"
            :cases ((<= 0 x))))))

(local
 (defthm norm-squared-real
     (and (realp (+ (EXPT (IMAGPART Z) 2)
                    (EXPT (REALPART Z) 2)))
          (<= 0 (+ (EXPT (IMAGPART Z) 2)
                   (EXPT (REALPART Z) 2))))
   :hints (("Goal"
            :use ((:instance square-positive
                             (x (imagpart z)))
                  (:instance square-positive
                             (x (realpart z))))
            :in-theory (disable square-positive)))))

(local
 (defthmd conj-prod-lemma
     (implies (and (realp a)
                   (realp b))
              (equal (* (complex a b)
                        (conjugate (complex a b)))
                     (+ (expt a 2)
                        (expt b 2))))
   :instructions ((:use (:instance complex-definition
                                   (x a)
                                   (y b)))
                  (:use (:instance complex-definition
                                   (x a)
                                   (y (- b))))
                  :pro (:forwardchain 1)
                  (:forwardchain 1)
                  (:dv 1)
                  (:dv 1)
                  := :nx :x := :top (:dv 1)
                  (:rewrite |(* x (+ y z))|)
                  (:dv 1)
                  (:rewrite |(* (+ x y) z)|)
                  (:dv 2)
                  :s :up :nx (:rewrite |(* (+ x y) z)|)
                  :s :up :s (:dive 2)
                  (:dive 2)
                  (:dv 2)
                  (:= (- (* #c(0 1) a b)))
                  :up (:= 0)
                  :top :s)
   ))

(local
 (defthm conj-prod
     (implies (acl2-numberp z)
              (equal (* z
                        (conjugate z))
                     (+ (expt (realpart z) 2)
                        (expt (imagpart z) 2))))
   :hints (("Goal"
            :use ((:instance conj-prod-lemma
                             (a (realpart z))
                             (b (imagpart z))))))))

(defthmd conjugate-product-normsq
    (implies (acl2-numberp z)
             (equal (* z (conjugate z))
                    (expt (norm-2c z) 2)))
  :hints (("Goal"
           :in-theory (disable conjugate)))
  )

(local
 (defthmd sum-of-inverses
     (implies (and (acl2-numberp x)
                   (acl2-numberp y)
                   (not (= x 0))
                   (not (= y 0)))
              (equal (+ (/ x) (/ y))
                     (/ (+ x y) (* x y))))))

(local
 (defthmd *-complex
     (implies (and (realp a)
                   (realp b)
                   (realp c)
                   (realp d))
              (equal (* (complex a b)
                        (complex c d))
                     (complex (- (* a c) (* b d))
                              (+ (* b c) (* a d)))))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x a)
                             (y b))
                  (:instance complex-definition
                             (x c)
                             (y d))
                  (:instance complex-definition
                             (x (- (* a c) (* b d)))
                             (y (+ (* b c) (* a d)))))))
   ))

(local
 (defthmd conjugate-of-product-lemma-1
     (implies (and (realp a)
                   (realp b)
                   (realp c)
                   (realp d))
              (equal (conjugate (* (complex a b)
                                   (complex c d)))
                     (complex (- (* a c) (* b d))
                              (- (+ (* b c) (* a d))))))
   :hints (("Goal"
            :use ((:instance *-complex))))
   ))

(local
 (defthmd conjugate-of-product-lemma-2
     (implies (and (realp a)
                   (realp b)
                   (realp c)
                   (realp d))
              (equal (* (complex a (- b))
                        (complex c (- d)))
                     (complex (- (* a c) (* b d))
                              (- (+ (* b c) (* a d))))))
   :hints (("Goal"
            :use ((:instance *-complex
                             (a a)
                             (b (- b))
                             (c c)
                             (d (- d))))
            :in-theory (disable conjugate)
            ))
   ))

(local
 (defthmd conjugate-of-product-lemma-3
     (implies (and (realp a)
                   (realp b)
                   (realp c)
                   (realp d))
              (equal (conjugate (* (complex a b)
                                   (complex c d)))
                     (* (conjugate (complex a b))
                        (conjugate (complex c d)))))
   :hints (("Goal"
            :use ((:instance conjugate-of-product-lemma-1)
                  (:instance conjugate-of-product-lemma-2))
            ))
   ))

(defthmd conjugate-of-product
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (conjugate (* x y))
                    (* (conjugate x) (conjugate y))))
  :hints (("Goal"
           :use ((:instance conjugate-of-product-lemma-3
                            (a (realpart x))
                            (b (imagpart x))
                            (c (realpart y))
                            (d (imagpart y))
                            ))
           :in-theory (disable conjugate)
           )))

(defthmd conjugate-uminus
    (equal (conjugate (- x))
           (- (conjugate x)))
  :hints (("Goal"
           :use ((:instance conjugate-of-product
                            (x -1)
                            (y x))))))

(local
 (defthmd conjugate-of-sum-lemma
     (implies (and (realp a)
                   (realp b)
                   (realp c)
                   (realp d))
              (equal (conjugate (+ (complex a b)
                                   (complex c d)))
                     (+ (conjugate (complex a b))
                        (conjugate (complex c d)))))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x a)
                             (y b))
                  (:instance complex-definition
                             (x c)
                             (y d))
                  (:instance complex-definition
                             (x (+ a c))
                             (y (+ b d)))
                  (:instance complex-definition
                             (x a)
                             (y (- b)))
                  (:instance complex-definition
                             (x c)
                             (y (- d)))
                  (:instance complex-definition
                             (x (+ a c))
                             (y (- (+ b d))))
                  )
            ))
   ))

(defthmd conjugate-of-sum
    (implies (and (acl2-numberp x)
                  (acl2-numberp y))
             (equal (conjugate (+ x y))
                    (+ (conjugate x) (conjugate y))))
  :hints (("Goal"
           :use ((:instance conjugate-of-sum-lemma
                            (a (realpart x))
                            (b (imagpart x))
                            (c (realpart y))
                            (d (imagpart y))
                            ))
           :in-theory (disable conjugate)
           )))


(defthmd uminus-complex
    (implies (and (realp x)
                  (realp y))
             (equal (- (complex x y))
                    (complex (- x) (- y))))
  :hints (("Goal"
           :use ((:instance complex-definition
                            (x x)
                            (y y))
                 (:instance complex-definition
                            (x (- x))
                            (y (- y))))
           ))
  )

(local
 (defthmd realpart-uminus-lemma
     (implies (and (realp a)
                   (realp b))
              (equal (realpart (complex (- a) (- b)))
                     (- (realpart (complex a b)))))
   ))

(local
 (defthmd imagpart-uminus-lemma
     (implies (and (realp a)
                   (realp b))
              (equal (imagpart (complex (- a) (- b)))
                     (- (imagpart (complex a b)))))
   ))

(defthmd realpart-uminus
    (equal (realpart (- x))
           (- (realpart x)))
  :hints (("Goal"
           :use ((:instance realpart-imagpart-elim)
                 (:instance realpart-imagpart-elim (x (- x)))
                 (:instance realpart-uminus-lemma
                            (a (realpart x))
                            (b (imagpart x)))
                 )
           :in-theory (e/d (uminus-complex)
                           (realpart-imagpart-elim))
           ))
  )

(defthmd imagpart-uminus
    (equal (imagpart (- x))
           (- (imagpart x)))
  :hints (("Goal"
           :use ((:instance realpart-imagpart-elim)
                 (:instance realpart-imagpart-elim (x (- x)))
                 (:instance imagpart-uminus-lemma
                            (a (realpart x))
                            (b (imagpart x)))
                 )
           :in-theory (e/d (uminus-complex)
                           (realpart-imagpart-elim))
           ))
  )

(local
 (defthmd denominator-term
     (implies (acl2-numberp z)
              (equal (* (expt (norm-2c (- 1 z)) 2)
                        (expt (norm-2c (+ 1 z)) 2))
                     (expt (norm-2c (- 1 (expt z 2))) 2)))
   :instructions ((:in-theory (disable conjugate))
                  (:use (:instance conjugate-product-normsq (z (+ 1 z))))
                  (:use (:instance conjugate-product-normsq
                                   (z (+ 1 (- z)))))
                  :pro (:forwardchain 1)
                  (:forwardchain 1)
                  (:dv 1)
                  (:dv 1)
                  := :nx := (:drop 2 3)
                  :up (:rewrite |(* y (* x z))|)
                  (:dive 2)
                  (:rewrite |(* (* x y) z)|)
                  (:dive 2)
                  :top
                  (:use (:instance conjugate-of-product (x (+ 1 (- z)))
                                   (y (+ 1 z))))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  (:dive 2 2)
                  := (:drop 2)
                  :top
                  (:claim (implies (acl2-numberp z)
                                   (equal (* (+ 1 z) (+ 1 (- z)))
                                          (+ 1 (- (expt z 2))))))
                  (:forwardchain 2)
                  (:dv 1)
                  (:= (* (* (+ 1 z) (+ 1 (- z)))
                         (conjugate (* (+ 1 (- z)) (+ 1 z)))))
                  (:dv 1)
                  := :nx (:dv 1)
                  (:rewrite |(* y x)|)
                  := (:drop 2)
                  :up
                  :up (:rewrite conjugate-product-normsq)
                  :top :s)
   ))

(local
 (defthmd numerator-term
     (implies (acl2-numberp z)
              (equal (+ (expt (norm-2c (- 1 z)) 2)
                        (expt (norm-2c (+ 1 z)) 2))
                     (* 2 (+ 1 (expt (norm-2c z) 2)))))
   :instructions ((:use (:instance conjugate-product-normsq (z (+ 1 z))))
                  (:use (:instance conjugate-product-normsq
                                   (z (+ 1 (- z)))))
                  :pro (:forwardchain 1)
                  (:forwardchain 1)
                  (:dv 1)
                  (:dv 1)
                  := (:dv 2)
                  (:rewrite conjugate-of-sum)
                  (:dv 1)
                  :x :up :up :nx := (:drop 2 3)
                  (:dv 2)
                  (:rewrite conjugate-of-sum)
                  (:dv 1)
                  :x :top :s (:dv 2)
                  (:dv 2)
                  (:dv 2)
                  (:dv 1)
                  (:= (norm-2c z))
                  :top (:dv 1)
                  (:dv 4)
                  (:dv 2)
                  (:= (conjugate z))
                  :up (:rewrite conjugate-product-normsq)
                  :up :up
                  (:= (+ (+ (complex (realpart z) (- (imagpart z)))
                            (complex (realpart (- z))
                                     (- (imagpart (- z)))))
                         (expt (norm-2c z) 2)))
                  (:dv 1)
                  (:dv 2)
                  (:dv 1)
                  (:rewrite realpart-uminus)
                  :up (:dv 2)
                  (:dv 1)
                  (:rewrite imagpart-uminus)
                  :up :s :up :up (:dv 1)
                  (:rewrite complex-definition)
                  :nx (:rewrite complex-definition)
                  :up :s (:dv 2)
                  (:= (- (* #c(0 1) (imagpart z))))
                  :up (:= 0)
                  :up (:= (expt (norm-2c z) 2))
                  :up :nx (:dv 3)
                  (:dv 2)
                  (:dv 1)
                  :up
                  (:= (conjugate (complex (realpart (- z))
                                          (imagpart (- z)))))
                  (:dv 1)
                  (:rewrite realpart-imagpart-elim)
                  :up (:rewrite conjugate-uminus)
                  :up (:rewrite |(* x (- y))|)
                  (:dv 1)
                  (:rewrite conjugate-product-normsq)
                  (:in-theory (disable expt norm-2c))
                  :top :bash)
   ))

(local
 (defthmd norm-0-for-0-only-1
     (implies (and (acl2-numberp z)
                   (not (equal z 0)))
              (not (equal (norm-2c z) 0)))
   :hints (("Goal"
            :use ((:instance norm-zero-for-zero-only (x z)))
            :in-theory (disable norm-zero-for-zero-only)))))

(local
 (defthmd not-equal-square-0
     (implies (and (acl2-numberp z)
                   (not (equal z 0)))
              (not (equal (expt z 2) 0)))
   ))

(local
 (defthm equal-square-norm-0
     (implies (and (acl2-numberp z)
                   (not (equal z 0)))
              (not (equal (expt (norm-2c z) 2) 0)))
   :hints (("Goal"
            :use ((:instance norm-0-for-0-only-1)
                  (:instance not-equal-square-0
                             (z (norm-2c 0))))))))

(defthmd sum-of-inverses-specialized
    (implies (and (acl2-numberp z)
                  (not (= (abs z) 1)))
             (equal (+ (/ (expt (norm-2c (- 1 z)) 2))
                       (/ (expt (norm-2c (+ 1 z)) 2)))
                    (/ (* 2 (+ 1 (expt (norm-2c z) 2)))
                       (expt (norm-2c (- 1 (expt z 2))) 2))))
  :instructions ((:in-theory (disable norm-2c))
                 (:use (:instance sum-of-inverses
                                  (x (expt (norm-2c (- 1 z)) 2))
                                  (y (expt (norm-2c (+ 1 z)) 2))))
                 (:use (:instance equal-square-norm-0 (z (+ 1 z))))
                 (:use (:instance equal-square-norm-0 (z (+ 1 (- z)))))
                 (:in-theory (disable equal-square-norm-0))
                 :pro (:forwardchain 1)
                 (:forwardchain 1)
                 (:forwardchain 1)
                 (:dv 1)
                 := (:drop 5)
                 :top (:dv 1)
                 (:dv 1)
                 (:rewrite numerator-term)
                 :nx (:dv 1)
                 (:rewrite denominator-term)
                 :top :s)
  )
