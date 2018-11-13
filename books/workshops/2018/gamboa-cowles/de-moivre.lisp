(in-package "ACL2")
  
; cert_param: (uses-acl2r)


(local (include-book "nonstd/nsa/exp-sum" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/complex-polar" :dir :system)
(include-book "nonstd/nsa/raise" :dir :system)

(include-book "norm2")

(in-theory (disable (radiuspart) (anglepart)))

(local
 (defthm radiuspart-0
   (equal (radiuspart 0) 0)
   :hints (("Goal"
            :use ((:instance norm2-zero-for-zero-only))
            :in-theory (enable radiuspart norm2)))
   ))

(defthm times-in-polar
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (* x y)
                  (* (radiuspart x)
                     (radiuspart y)
                     (acl2-exp (* #c(0 1) (+ (anglepart x)
                                             (anglepart y)))))))
  :hints (("Goal"
           :use ((:instance correctness-of-polar-form (x x))
                 (:instance correctness-of-polar-form (x y))
                 (:instance exp-sum
                            (x (* #c(0 1) (anglepart x)))
                            (y (* #c(0 1) (anglepart y)))))
           :in-theory (disable correctness-of-polar-form
                               exp-sum
                               radiuspart
                               anglepart))
          )
  :rule-classes nil)

(defthm equal-radiuspart-norm2
  (equal (radiuspart z)
         (norm2 z))
  :hints (("Goal"
           :in-theory (enable radiuspart norm2)))
  :rule-classes nil)

(local
 (defthm realpart-ix
   (implies (realp x)
            (equal (realpart (* #c(0 1) x)) 0))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x 0)
                             (y x))
                  )
            :in-theory (disable complex-definition))
           )
   ))

(local
 (defthm imagpart-ix
   (implies (realp x)
            (equal (imagpart (* #c(0 1) x)) x))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x 0)
                             (y x))
                  )
            :in-theory (disable complex-definition))
           )
   ))

(local
 (defthm radiuspart-of-e^ix
   (implies (realp x)
            (equal (radiuspart (acl2-exp (* #c(0 1) x))) 1))
   :hints (("Goal"
            :use ((:instance sin**2+cos**2)
                  )
            :in-theory (disable sin**2+cos**2))
           )
   ))

#|
(defun normalize-angle-0-2pi (x)
  (- x
     (* 2 (acl2-pi)
        (floor1 (/ x (* 2 (acl2-pi)))))))

(defthm cos-2npi
  (implies (integerp n)
           (equal (acl2-cosine (* 2 (acl2-pi) n)) 1))
  :hints (("Goal"
           :use ((:instance sin-2npi)
                 (:instance 

(defthm cos-normalize-angle-0-2pi
  (equal (acl2-cosine (normalize-angle-0-2pi x))
         (acl2-cosine x))
  :use ((: ... )))

|#


(local
 (defthm e^ix-not-zero
   (implies (realp x)
            (not (equal (acl2-exp (* #c(0 1) x)) 0)))
   :hints (("Goal"
            :use ((:instance radiuspart-of-e^ix)
                  (:instance norm2-zero-for-zero-only (x (acl2-exp (* #c(0 1) x))))
                  (:instance equal-radiuspart-norm2 (z (acl2-exp (* #c(0 1) x)))))
            :in-theory (disable radiuspart-of-e^ix norm2-zero-for-zero-only)
            )
           )
   ))

(local
 (defthm realpart-of-e^ix
   (implies (realp x)
            (equal (realpart (acl2-exp (complex 0 x)))
                   (acl2-cosine x)))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin)
                  (:instance complex-definition (x 0) (y x)))
            :in-theory (disable  e^ix-cos-i-sin complex-definition)))
   ))

(local
 (defthm imagpart-of-e^ix
   (implies (realp x)
            (equal (imagpart (acl2-exp (complex 0 x)))
                   (acl2-sine x)))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin)
                  (:instance complex-definition (x 0) (y x)))
            :in-theory (disable  e^ix-cos-i-sin complex-definition)))
   ))

(local
 (defthm expt-sin-2+expt-cos-2
   (equal (+ (expt (acl2-cosine x) 2)
             (expt (acl2-sine x) 2))
          1)
   :hints (("Goal"
            :use ((:instance sin**2+cos**2))
            :in-theory (disable sin**2+cos**2)))))

(local
 (defthm range-of-x-when-sin-negative
   (implies (and (realp x)
                 (<= 0 x)
                 (< x (* 2 (acl2-pi)))
                 (< (acl2-sine x) 0))
            (< (acl2-pi) x))
   :hints (("Goal"
            :use ((:instance sine-positive-in-0-pi/2)
                  (:instance sine-positive-in-pi/2-pi)
                  )
            :in-theory (disable sine-positive-in-0-pi/2
                                sine-positive-in-pi/2-pi)
            )
           )
   :rule-classes nil))

(local
 (defthm in-right-interval-when-sin-negative
   (implies (and (realp x)
                 (<= 0 x)
                 (< x (* 2 (acl2-pi)))
                 (< (acl2-sine x) 0))
            (inside-interval-p (- (* 2 (acl2-pi)) x)
                               (interval 0 (acl2-pi))))
   :hints (("Goal"
            :use ((:instance range-of-x-when-sin-negative))
            :in-theory (e/d (interval-definition-theory)
                            (SINE-<-0-=>-X->-PI))))
   :rule-classes nil))

(local
 (defthm range-of-x-when-sin-positive
   (implies (and (realp x)
                 (<= 0 x)
                 (< x (* 2 (acl2-pi)))
                 (<= 0 (acl2-sine x)))
            (<= x (acl2-pi)))
   :hints (("Goal"
            :use ((:instance sine-negative-in-pi-3pi/2)
                  (:instance sine-negative-in-3pi/2-2pi)
                  )
            :in-theory (disable sine-negative-in-pi-3pi/2
                                sine-negative-in-3pi/2-2pi
                                SINE->=-0-=>-X-<=-PI)
            )
           )
   :rule-classes nil))

(local
 (defthm in-right-interval-when-sin-positive
   (implies (and (realp x)
                 (<= 0 x)
                 (< x (* 2 (acl2-pi)))
                 (<= 0 (acl2-sine x)))
            (inside-interval-p x
                               (interval 0 (acl2-pi))))
   :hints (("Goal"
            :use ((:instance range-of-x-when-sin-positive))
            :in-theory (enable interval-definition-theory)))
   :rule-classes nil))

(local
 (defthm anglepart-of-e^ix 
   (implies (and (realp x)
                 (<= 0 x)
                 (< x (* 2 (acl2-pi))))
            (equal (anglepart (acl2-exp (* #c(0 1) x))) x))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x 0)
                             (y x))
                  (:instance e^ix-not-zero)
                  )
            :in-theory (disable complex-definition e^ix-not-zero))
           ("Subgoal 2"
            :use ((:instance in-right-interval-when-sin-negative)
                  (:instance cos-2pi-x)
                  (:instance acl2-acos-inverse-exists
                             (x (- (* 2 (acl2-pi)) x)))
                  )
            :in-theory (disable cos-2pi-x cos-2pi+x cosine-of-sums
                                acl2-acos-inverse-exists
                                )
            )
           ("Subgoal 1"
            :use ((:instance in-right-interval-when-sin-positive)
                  (:instance acl2-acos-inverse-exists)
                  )
            :in-theory (disable acl2-acos-inverse-exists
                                )
            )
           )
   ))


(local
 (defthm iff-radiuspart-0
   (iff (equal (radiuspart z) 0)
        (equal (fix z) 0))
   :hints (("Goal"
            :use ((:instance equal-radiuspart-norm2)
                  (:instance norm2-zero-for-zero-only (x z)))
            :in-theory (disable radiuspart norm2-zero-for-zero-only)))
   :rule-classes nil
   ))

(local
 (defthm equal-radiuspart-0
   (equal (equal (radiuspart z) 0)
          (equal (fix z) 0))
   :hints (("Goal"
            :use ((:instance iff-radiuspart-0))
            :in-theory (disable radiuspart
                                radiuspart-is-zero-only-for-zero)))
   ))

(local
 (defthm de-moivre-1-lemma-1
   (implies (acl2-numberp y)
            (equal (+ (* #c(0 1) y)
                      (* #c(0 -1) y))
                   0))
   :hints (("Goal"
            :use ((:instance
                   (:theorem
                    (equal (* #c(0 -1) y)
                           (- (* #c(0 1) y)))))
                  )
           )
   )))

(local
 (defthm de-moivre-1-lemma-2
   (implies (acl2-numberp y)
            (equal (* (acl2-exp (* #c(0 1) y))
                      (acl2-exp (* #c(0 -1) y)))
                   1))
   :hints (("Goal"
            :use ((:instance exp-sum
                             (x (* #c(0 1) y))
                             (y (* #c(0 -1) y)))
                  )
            :in-theory (disable exp-sum e^ix-cos-i-sin))
           )
   ))
   

(local
 (defthm de-moivre-1-lemma-3
   (implies (and (acl2-numberp z)
                 (equal z 0)
                 (natp n))
            (equal (expt z n)
                   (* (expt (radiuspart z) n)
                      (acl2-exp (* #c(0 1) n (anglepart z))))))
   ))

(local
 (defthm de-moivre-1-lemma-4
   (implies (and (acl2-numberp z)
                 ;(not (equal z 0))
                 (integerp n)
                 (< 0 n))
            (equal (* (radiuspart z)
                      (acl2-exp (* #c(0 1) (anglepart z)))
                      (expt (radiuspart z) (1- n))
                      (acl2-exp (* #c(0 1) (1- n) (anglepart z))))
                   (* (expt (radiuspart z) n)
                      (acl2-exp (* #c(0 1) n (anglepart z))))))
   :hints (("Goal"
            :expand (expt (radiuspart z) n)
            :use ((:instance de-moivre-1-lemma-2
                             (y (anglepart z)))
                  (:instance
                   (:theorem (implies (equal y 1)
                                      (equal (* a y b) (* a b))))
                   (y (* (ACL2-EXP (* #C(0 1) (ANGLEPART Z)))
                         (ACL2-EXP (* #C(0 -1) (ANGLEPART Z)))))
                   (a (RADIUSPART Z))
                   (b (* (EXPT (RADIUSPART Z) (+ -1 N))
                         (ACL2-EXP (* #C(0 1) N (ANGLEPART Z))))))
                  )
            :in-theory (disable radiuspart anglepart e^ix-cos-i-sin
                                de-moivre-1-lemma-2
                                SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL
                                NORMALIZE-FACTORS-GATHER-EXPONENTS)))
   :rule-classes nil))

(local
 (defthm de-moivre-1-lemma-5
   (implies (and (acl2-numberp z)
                 (integerp n)
                 (< 0 n))
            (equal (* z
                      (expt (radiuspart z) (1- n))
                      (acl2-exp (* #c(0 1) (1- n) (anglepart z))))
                   (* (expt (radiuspart z) n)
                      (acl2-exp (* #c(0 1) n (anglepart z))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance de-moivre-1-lemma-4)
                  (:instance correctness-of-polar-form (x z))
                  )
            :in-theory (disable radiuspart anglepart correctness-of-polar-form
                                SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL
                                NORMALIZE-FACTORS-GATHER-EXPONENTS)))
   :rule-classes nil))


(defthm de-moivre-1
  (implies (and (acl2-numberp z)
                (natp n))
           (equal (expt z n)
                  (* (expt (radiuspart z) n)
                     (acl2-exp (* #c(0 1) n (anglepart z))))))
  :hints (("Goal"
           :induct (expt z n)
           :do-not-induct t
           :in-theory (e/d (expt) (radiuspart anglepart e^ix-cos-i-sin)))
          ("Subgoal *1/3"
           :do-not-induct t
           :expand (expt z n)
           :use ((:instance de-moivre-1-lemma-5))
           :in-theory (disable correctness-of-polar-form radiuspart anglepart
                               e^ix-cos-i-sin exp-sum))
          ("Subgoal *1/2"
           :do-not-induct t
           :cases ((equal z 0))
           :in-theory (disable de-moivre-1-lemma-3))
          )
  :rule-classes nil)

(local (in-theory (disable de-moivre-1-lemma-3)))

(defun nth-root (z n)
  (* (raise (radiuspart z) (/ n))
     (acl2-exp (* #c(0 1) (/ (anglepart z) n)))))

(defthm radiuspart-nth-root
  (implies (posp n)
           (equal (radiuspart (nth-root z n))
                  (raise (radiuspart z) (/ n))))
  :hints (("Goal"
           :use ((:instance norm2-product
                            (a (raise (radiuspart z) (/ n)))
                            (b (acl2-exp (* #c(0 1) (/ (anglepart z) n)))))
                 (:instance radiuspart-of-e^ix
                            (x (/ (anglepart z) n)))
                 (:instance equal-radiuspart-norm2
                            (z (raise (radiuspart z) (/ n))))
                 (:instance equal-radiuspart-norm2
                            (z (acl2-exp (* #c(0 1) (/ (anglepart z) n)))))
                 )
           :in-theory (disable norm2-product radiuspart-of-e^ix
                               radiuspart e^ix-cos-i-sin)
           )
          )
  )

(local
 (defthm realp-raise
   (implies (and (realp a)
                 (<= 0 a)
                 (realp x))
            (realp (raise a x)))
   :hints (("Goal"
            :use ((:instance realp-exp
                             (x (* x (acl2-ln a))))
                  (:instance realp-ln
                             (y a))
                  )
            :in-theory (disable realp-exp realp-ln)
            )
           )
   ))


(local
 (defthm raise-non-negative
   (implies (and (realp a)
                 (<= 0 a)
                 (realp x))
            (<= 0 (raise a x)))
   :hints (("Goal"
            :cases ((equal a 0)))
           ("Subgoal 1"
            :expand (raise a x))
           )
   ))

(local
 (defthm raise-positive-for-non-zero-a
   (implies (and (realp a)
                 (< 0 a)
                 (realp x))
            (< 0 (raise a x)))
   :hints (("Goal"
            :cases ((equal a 0)))
           ("Subgoal 1"
            :expand (raise a x))
           )
   ))
   

(local
 (defthm lemma-1
   (implies (and (realp x)
                 (<= 0 x)
                 (realp z)
                 (< 0 z)
                 (<= z 1)
                 )
            (<= (* x z) x))
   :rule-classes nil))

(defthm anglepart-nth-root-lemma-1
  (implies (and (posp n)
                (acl2-numberp z)
                (not (equal z 0)))
           (equal (anglepart (nth-root z n))
                  (/ (anglepart z) n)))
  :hints (("Goal"
           :use ((:instance anglepart-*-real
                            (x (raise (radiuspart z) (/ n)))
                            (y (acl2-exp (* #c(0 1) (/ (anglepart z) n)))))
                 (:instance anglepart-between-0-and-2pi (x z))
                 (:instance anglepart-of-e^ix
                            (x (/ (anglepart z) n)))
                 (:instance lemma-1
                            (x (anglepart z))
                            (z (/ n)))
                 )
           :in-theory (disable anglepart-*-real
                               anglepart-of-e^ix
                               anglepart-between-0-and-2pi
                               radiuspart anglepart
                               e^ix-cos-i-sin
                               raise)
           )
          )
  :rule-classes nil)
                 
(defthm anglepart-nth-root-lemma-2
  (implies (and (posp n)
                (acl2-numberp z)
                (equal z 0))
           (equal (anglepart (nth-root z n))
                  (/ (anglepart z) n)))
  :rule-classes nil)

(defthm anglepart-nth-root-lemma
  (implies (and (posp n)
                (acl2-numberp z))
           (equal (anglepart (nth-root z n))
                  (/ (anglepart z) n)))
  :hints (("Goal"
           :use ((:instance anglepart-nth-root-lemma-1)
                 (:instance anglepart-nth-root-lemma-2))))
  )

(in-theory (disable anglepart-nth-root-lemma))

(defthm expt-raise-lemma
  (implies (and (acl2-numberp a)
                (posp n)
                (acl2-numberp x))
           (equal (expt (raise a x) n)
                  (raise a (* x n))))
  :hints (("Goal"
           :do-not-induct t
           :induct (expt a n)
           :in-theory (enable expt)))
  :rule-classes nil)

(defthm expt-raise-for-de-moivre
  (implies (and (acl2-numberp z)
                (posp n))
           (equal (expt (raise z (/ n)) n)
                  z))
  :hints (("Goal"
           :use ((:instance expt-raise-lemma
                            (a z)
                            (x (/ n))))))
  :rule-classes nil)


(defthm de-moivre-2
  (implies (and (acl2-numberp z)
                (posp n))
           (equal (expt (nth-root z n) n) z))
  :hints (("Goal"
           :use ((:instance de-moivre-1
                            (z (nth-root z n)))
                 (:instance expt-raise-for-de-moivre
                            (z (radiuspart z)))
                 (:instance anglepart-nth-root-lemma)
                 )
           :in-theory (disable radiuspart anglepart
                               e^ix-cos-i-sin
                               nth-root
                               raise
                               )
           )
          )
  )
