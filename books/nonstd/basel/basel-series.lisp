(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/norm" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/nsa/complex-polar" :dir :system)
(include-book "nonstd/nsa/raise" :dir :system)
(include-book "nonstd/nsa/standard-close-utils" :dir :system)

(include-book "basel-bound")
(local (include-book "complex-helper"))

(local (in-theory (disable (i-large-integer)
                           binomial-theorem)))

(local
 (defun zeta (n)
   (acl2-exp (* 2 (acl2-pi) #c(0 1) (/ n)))))

(local (in-theory (disable (zeta))))

(local
 (defun omega-term (k n)
   (/ (expt (norm-2c (- 1 (expt (zeta (expt 2 (1+ n)))
                                (- (* 2 k) 1))))
            2))))


(local
 (defun omega-term-dual (k n)
   (/ (expt (norm-2c (+ 1 (expt (zeta (expt 2 (1+ n)))
                                (- (* 2 k) 1))))
            2))))

(local (in-theory (disable (omega-term)
                           (omega-term-dual))))

(local
 (defthm exp-1/2-pi-i
     (equal (ACL2-EXP (* #C(0 1/2) (ACL2-PI)))
            #c(0 1))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin
                             (x (* 1/2 (acl2-pi)))))
            :in-theory (disable e^ix-cos-i-sin)))))

(local
 (defthm expt-sqrt--2
     (implies (and (realp x)
                   (<= 0 x))
              (equal (expt (acl2-sqrt x) -2)
                     (/ x)))
   :hints (("Goal"
            :use ((:instance sqrt-sqrt))
            :in-theory (disable sqrt-sqrt)))
   ))

(local
 (defthm omega-term-1-1
     (equal (omega-term 1 1) 1/2)))

(local
 (defun omega-series (k m n)
   (declare (xargs :measure (nfix (- m k))))
   (if (zp (- m k))
       (if (= m k)
           (omega-term k n)
           0)
       (+ (omega-term k n)
          (omega-series (1+ k) m n)))))

(local
 (defun omega-series-dual (k m n)
   (declare (xargs :measure (nfix (- m k))))
   (if (zp (- m k))
       (if (= m k)
           (omega-term-dual k n)
           0)
       (+ (omega-term-dual k n)
          (omega-series-dual (1+ k) m n)))))


(local (in-theory (disable (omega-series)
                           (omega-series-dual))))

(local
 (defun omega-series-down (k m n)
   (declare (xargs :measure (nfix (- m k))))
   (if (zp (- m k))
       (if (= m k)
           (omega-term k n)
           0)
       (+ (omega-term m n)
          (omega-series-down k (1- m) n)))))

(local (in-theory (disable (omega-series-down))))

(local
 (defthm omega-series-down-bridge-lemma
     (implies (and (natp k)
                   (natp m)
                   (natp n)
                   (< k m))
              (equal (omega-series-down (1+ k) m n)
                     (- (omega-series-down k m n) (omega-term k n))))
   :hints (("Goal" :induct (omega-series-down k m n)
                   :in-theory (disable omega-term))
           )
   ))

(local
 (defthm omega-series-down-is-omega-series
     (implies (and (natp k)
                   (natp m))
              (equal (omega-series-down k m n)
                     (omega-series k m n)))
   :hints (("Goal"
            :induct (omega-series k m n)
            :in-theory (disable omega-term)))
   ))

(local
 (defthm omega-series-1-1-1
     (equal (omega-series 1 1 1) 1/2)))

(local
 (defthmd omega-series-sum-base
     (implies (= n 1)
              (equal (omega-series 1 n n)
                     (expt 2 (- (* 2 n) 3))))
   :hints (("Goal"
            :use ((:instance omega-series-1-1-1))
            :in-theory (disable omega-series
                                omega-series-1-1-1)))))


(local
 (defthm e^i-pi
     (equal (acl2-exp (* #c(0 1) (acl2-pi))) -1)))

(local
 (defthm zeta-2n-to-n
     (implies (posp n)
              (equal (expt (zeta (* 2 n)) n)
                     -1))
   :hints (("Goal"
            :use ((:instance power-of-powers
                             (a (acl2-exp 1))
                             (x (* #C(0 1) (ACL2-PI) (/ N)))
                             (y n))
                  )
            :in-theory (disable e^ix-cos-i-sin
                                power-of-powers)))
   ))

(local
 (defthmd zeta-2n-to-n+j
     (implies (and (posp n)
                   (natp j))
              (equal (expt (zeta (* 2 n)) (+ n j))
                     (- (expt (zeta (* 2 n)) j))))
   :hints (("Goal"
            :in-theory (e/d (|arith (expt x (+ m n))|)
                            (zeta
                             e^ix-cos-i-sin
                             |(* (expt x m) (expt x n))|))))
   ))

(local
 (defthmd exp-i-theta-inverse-1
     (implies (realp theta)
              (equal (acl2-exp (* #c(0 1) (- theta)))
                     (/ (acl2-exp (* #c(0 1) theta)))))
   :hints (("Goal"
            :use ((:instance /-complex
                             (r (acl2-cosine (- theta)))
                             (s (acl2-sine (- theta))))
                  (:instance e^ix-cos-i-sin
                             (x (- theta)))
                  (:instance e^ix-cos-i-sin
                             (x theta))
                  (:instance complex-definition
                             (x (acl2-cosine (- theta)))
                             (y (acl2-sine (- theta))))
                  (:instance complex-definition
                             (x (acl2-cosine theta))
                             (y (acl2-sine theta)))
                  (:instance sin**2+cos**2
                             (x theta))
                  )
            :in-theory (e/d ()
                            (e^ix-cos-i-sin
                             complex-definition
                             sin**2+cos**2
                             /-complex-2
                             /-complex))))
   ))

(local
 (defthmd exp-i-theta-inverse-2
     (implies (realp theta)
              (equal (acl2-exp (* #c(0 1) (- theta)))
                     (conjugate (acl2-exp (* #c(0 1) theta)))))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin
                             (x (- theta)))
                  (:instance e^ix-cos-i-sin
                             (x theta))
                  (:instance complex-definition
                             (x (realpart (ACL2-EXP (* #C(0 1) THETA))))
                             (y (- (imagpart (ACL2-EXP (* #C(0 1) THETA))))))
                  )
            :in-theory (disable e^ix-cos-i-sin
                                complex-definition
                                ))
           )
   ))

(local
 (encapsulate nil

     (local
      (defthmd lemma-1
          (implies (realp x)
                   (equal (imagpart (* #c(0 1) x)) x))))

   (local
    (defthm lemma-2
        (implies (realp x)
                 (equal (imagpart (* #c(0 2) x)) (* 2 x)))
      :hints (("Goal"
               :use ((:instance lemma-1
                                (x (* 2 x))))))))


   (local
    (defthm e^i-2pi
        (equal (acl2-exp (* #c(0 2) (acl2-pi))) 1)
      :hints (("Goal"
               :use ((:instance e^ix-cos-i-sin
                                (x (* 2 (acl2-pi))))
                     )
               :in-theory (disable e^ix-cos-i-sin)))
      ))

   (defthm zeta-n-to-n
       (implies (posp n)
                (equal (expt (zeta n) n)
                       1))
     :otf-flg t
     :hints (("Goal"
              :use ((:instance power-of-powers
                               (a (acl2-exp 1))
                               (x (* #C(0 2) (ACL2-PI) (/ N)))
                               (y n))
                    )
              :in-theory (disable e^ix-cos-i-sin
                                  power-of-powers)))
     )
   ))


(local
 (defthm complex-uminus-2
     (implies (acl2-numberp x)
              (equal (complex (- (realpart x)) (- (imagpart x)))
                     (- x)))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x (- (realpart x)))
                             (y (- (imagpart x))))
                  (:instance complex-definition
                             (x (realpart x))
                             (y (imagpart x)))
                  )
            ))
   ))

(local
 (defthm expt-acl2-exp
     (implies (and (integerp n)
                   (<= 0 (imagpart x))
                   (< (imagpart x) (* 2 (acl2-pi)))
                   (acl2-numberp x)
                   )
              (equal (expt (acl2-exp x) n)
                     (acl2-exp (* x n))))
   :hints (("Goal"
            :use ((:instance power-of-powers
                             (a (acl2-exp 1))
                             (x x)
                             (y n))
                  (:instance raise-acl2-exp
                             (x x))
                  (:instance raise-expt
                             (a (acl2-exp x))
                             (i n)))
            :in-theory (disable raise-expt
                                raise-acl2-exp
                                power-of-powers)))))

(local
 (defthm conjugate-e^-ix
     (implies (realp x)
              (equal (conjugate (acl2-exp (* #c(0 -1) x)))
                     (acl2-exp (* #c(0 1) x))))
  :instructions (:pro (:dv 1)
                      (:dv 1)
                      (:dv 1)
                      (:= (* #c(0 1) (- x)))
                      :up (:rewrite e^ix-cos-i-sin)
                      :s
                      (:= (+ (acl2-cosine x)
                             (* #c(0 1) (- (acl2-sine x)))))
                      :up :x (:dv 1)
                      (:dv 2)
                      (:dv 1)
                      (:= (* #c(0 1) (- (acl2-sine x))))
                      :top
                      (:use (:instance complex-definition (x 0)
                                       (y (- (acl2-sine x)))))
                      :pro (:forwardchain 1)
                      (:dv 1)
                      (:dv 1)
                      (:dv 2)
                      (:dv 1)
                      (:= (complex 0 (- (acl2-sine x))))
                      :up (:rewrite realpart-complex)
                      :up :s :nx (:dv 1)
                      (:dv 1)
                      (:= (* #c(0 1) (- (acl2-sine x))))
                      (:= (complex 0 (- (acl2-sine x))))
                      :up (:rewrite imagpart-complex)
                      :up :s
                      :up (:rewrite complex-definition)
                      :nx (:rewrite e^ix-cos-i-sin)
                      :top :s)))

(local
 (defthm conjugate-e^+ix
     (implies (realp x)
              (equal (conjugate (acl2-exp (* #c(0 1) x)))
                     (acl2-exp (* #c(0 1) (- x)))))
   :hints (("Goal"
            :use ((:instance conjugate-e^-ix
                             (x (- x))))))))

(local
 (defthm complexx-uminus-uminus
     (implies (and (realp x)
                   (realp y))
              (equal (complex (- x) (- y))
                     (- (complex x y))))
   :hints (("Goal"
            :use ((:instance complex-definition
                             (x (- x))
                             (y (- y)))
                  (:instance complex-definition))))
   ))

(local
 (defthm complex-uminus-realpart
     (equal (complex (- (realpart z))
                     (imagpart z))
            (- (conjugate z)))
   :instructions ((:dv 1)
                 (:dv 2)
                 (:= (- (- (imagpart z))))
                 :up (:rewrite complexx-uminus-uminus)
                 :top :s)))

(local (in-theory (enable imagpart-uminus realpart-uminus)))

(local
 (defthmd exp-i-theta-inverse
     (implies (and (posp n)
                   (natp j)
                   (< j n))
              (equal (expt (zeta (* 2 n)) (+ n j))
                     (conjugate (expt (zeta (* 2 n)) (- n j)))))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin
                             (x (- (* (acl2-pi) j (/ n)))))
                  (:instance e^ix-cos-i-sin
                             (x (* (acl2-pi) j (/ n)))))
            :in-theory (e/d ()
                            (e^ix-cos-i-sin))))
   ))

(local
 (defthm norm-1-to-conjugate
     (implies (acl2-numberp x)
              (equal (norm-2c (- 1 (conjugate x)))
                     (norm-2c (- 1 x))))
   ))

(local
 (defthmd paired-omega-terms
     (implies (and (posp n)
                   (posp j)
                   (<= j (expt 2 (1- n))))
              (equal (omega-term (+ (expt 2 (1- n)) j) n)
                     (omega-term (- (expt 2 (1- n)) (- j 1)) n)))
   ;; :hints (("Goal"
   ;;          :use ((:instance norm-1-to-conjugate
   ;;                           (x (EXPT (ZETA (* 2 (EXPT 2 N)))
   ;;                                    (+ (EXPT 2 N) (- (+ -1 (* 2 J)))))))
   ;;                (:instance exp-i-theta-inverse (n (expt 2 n))
   ;;                           (j (- (* 2 j) 1)))
   ;;                (:instance (:theorem (implies (and (posp j)
   ;;                                                   (posp n)
   ;;                                                   (<= J (EXPT 2 (+ -1 N))))
   ;;                                              (<= (* 2 J) (EXPT 2 N))))))
   ;;          :in-theory  (disable exp-i-theta-inverse
   ;;                               norm-2c conjugate zeta
   ;;                               norm-1-to-conjugate)))
   :instructions ((:in-theory (disable exp-i-theta-inverse
                                      norm-2c conjugate zeta))
                 (:use (:instance exp-i-theta-inverse (n (expt 2 n))
                                  (j (- (* 2 j) 1))))
                 :pro (:claim (<= (* 2 j) (expt 2 n)))
                 (:forwardchain 1)
                 (:dv 1)
                 :x :nx :x :top (:dv 1)
                 (:dv 1)
                 (:dv 1)
                 (:dv 2)
                 (:dv 1)
                 (:= (conjugate (expt (zeta (* 2 (expt 2 n)))
                                      (+ (expt 2 n) (- (+ -1 (* 2 j)))))))
                 :top (:drop 5)
                 (:dv 1)
                 (:dv 1)
                 (:rewrite norm-1-to-conjugate)
                  :top :s)
      ))

(local
 (defthmd paired-omega-series-half-lemma-1
     (implies (and (posp n)
                   (posp i)
                   (posp j)
                   (<= i j)
                   (<= j (expt 2 (1- n))))
              (equal (omega-series (+ (expt 2 (1- n)) i)
                                   (+ (expt 2 (1- n)) j)
                                   n)
                     (omega-series-down (- (expt 2 (1- n)) (- j 1))
                                        (- (expt 2 (1- n)) (- i 1))
                                        n)))
   :instructions ((:in-theory (e/d (basel-series) (omega-term)))
                  (:induct (basel-series i j))
                  :pro (:change-goal nil t)
                  :pro (:claim (= i j))
                  :s
                  (:use (:instance paired-omega-terms (j i)))
                  :bash (:forwardchain 2)
                  (:claim (< i j))
                  (:dv 1)
                  :x (:dv 2)
                  (:= (omega-series-down (+ (expt 2 (+ -1 n)) (- (+ -1 j)))
                                         (+ (expt 2 (+ -1 n)) (- (+ -1 1 i)))
                                         n))
                  :top (:dv 2)
                  :x :top
                  (:use (:instance paired-omega-terms (j i)))
                  :bash)))

(local
 (defthm paired-omega-series-half-lemma-2
     (implies (and (posp n)
                   (posp i)
                   (posp j)
                   (<= i j)
                   (<= j (expt 2 (1- n))))
              (equal (omega-series (+ (expt 2 (1- n)) i)
                                   (+ (expt 2 (1- n)) j)
                                   n)
                     (omega-series (- (expt 2 (1- n)) (- j 1))
                                   (- (expt 2 (1- n)) (- i 1))
                                   n)))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half-lemma-1)
                  (:instance omega-series-down-is-omega-series
                             (k (- (expt 2 (1- n)) (- j 1)))
                             (m (- (expt 2 (1- n)) (- i 1)))))
            :in-theory (disable omega-series
                                omega-series-down)
            )
           )))

(local
 (defthmd paired-omega-series-half-lemma
     (implies (posp n)
              (equal (omega-series (+ (expt 2 (1- n)) 1)
                                   (expt 2 n)
                                   n)
                     (omega-series 1
                                   (expt 2 (1- n))
                                   n)))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half-lemma-2
                             (i 1)
                             (j (expt 2 (1- n)))))
            :in-theory (disable omega-series)
            )
           )))

(local
 (defthmd omega-series-split
     (implies (and (posp n)
                   (posp i)
                   (posp j)
                   (posp k)
                   (<= i j)
                   (<= j k))
              (equal (omega-series i k n)
                     (+ (omega-series i j n)
                        (omega-series (1+ j) k n))))
   :hints (("Goal"
            :in-theory (disable omega-term)
            )
           )))


(local
 (defthmd paired-omega-series-half-2
     (implies (posp n)
              (equal (omega-series 1 (expt 2 (1- n)) n)
                     (* 1/2 (omega-series 1 (expt 2 n) n))))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half-lemma)
                  (:instance omega-series-split
                             (i 1)
                             (j (expt 2 (1- n)))
                             (k (expt 2 n))))
            :in-theory (disable omega-series)
            )
           )))

(local
 (defthmd paired-omega-series-half-3
     (implies (posp n)
              (equal (omega-series 1 (expt 2 (1- n)) n)
                     (* 1/2 (+ (omega-series 1 (expt 2 (1- n)) n)
                               (omega-series (+ 1 (expt 2 (1- n))) (expt 2 n) n)))))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half-2)
                  (:instance omega-series-split
                             (i 1)
                             (j (expt 2 (1- n)))
                             (k (expt 2 n))))
            :in-theory (disable omega-series)
            )
           )))

(local
 (defthmd omega-term-to-dual
     (implies (and (posp n)
                   (posp j))
              (equal (omega-term (+ (expt 2 (1- n)) j) n)
                     (omega-term-dual j n)))
   :hints (("Goal"
            :use ((:instance zeta-2n-to-n+j
                             (n (expt 2 n))
                             (j (+ (* 2 j) -1))))
            :in-theory (disable zeta
                                norm-2c
                                )))))

(local
 (defthmd omega-series-to-dual-lemma
     (implies (and (posp n)
                   (posp i)
                   (posp j)
                   (<= i j)
                   ;; (<= j (xexpt 2 (1- n)))
                   )
              (equal (omega-series (+ i (expt 2 (1- n))) (+ j (expt 2 (1- n))) n)
                     (omega-series-dual i j n)))
   :hints (("Goal"
            :induct (omega-series i j n)
            :in-theory (disable omega-term
                                omega-term-dual)
            )
           ("Subgoal *1/3"
            :use ((:instance omega-term-to-dual
                             (j i))))
           ("Subgoal *1/1"
            :use ((:instance omega-term-to-dual
                             (j i)))))))

(local
 (defthmd paired-omega-series-half
     (implies (posp n)
              (equal (omega-series 1 (expt 2 (1- n)) n)
                     (* 1/2 (+ (omega-series 1 (expt 2 (1- n)) n)
                               (omega-series-dual 1 (expt 2 (1- n)) n)))))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half-3)
                  (:instance omega-series-to-dual-lemma
                             (i 1)
                             (j (expt 2 (1- n)))))
            :in-theory (disable omega-series
                                omega-series-dual)
            )
           )))

;;; I-AM-HERE

(local
 (defthm sine-0-only-for-pi
     (implies (and (realp x)
                   (< 0 x)
                   (< x (* 2 (acl2-pi)))
                   (equal (acl2-sine x) 0)
                   )
              (equal x (acl2-pi)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance sine-positive-in-0-pi/2)
                  (:instance SINE-PI/2)
                  (:instance sine-positive-in-pi/2-pi)
                  (:instance sine-negative-in-pi-3pi/2)
                  (:instance SINE-3PI/2)
                  (:instance sine-negative-in-3pi/2-2pi))
            :in-theory (disable sine-positive-in-0-pi/2
                                SINE-PI/2
                                sine-positive-in-pi/2-pi
                                sine-negative-in-pi-3pi/2
                                SINE-3PI/2
                                sine-negative-in-3pi/2-2pi
                                SINE->=-0-=>-X-<=-PI)))))


(local
 (defthmd expt-zeta-not-real-for-odd-exponents
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 n)))
              (not (equal (imagpart (expt (zeta (expt 2 (1+ n))) (1- (* 2 k))))
                          0)))
   :instructions
   (:pro (:dv 1)
         (:dv 1)
         (:dv 1)
         (:dv 1)
         :x-dumb
         (:= (acl2-exp (* 2 (acl2-pi)
                          #c(0 1) (/ (expt 2 (+ 1 n))))))
         :up (:rewrite expt-acl2-exp)
         (:dv 1)
         (:= (* 2 (acl2-pi)
                #c(0 1) (/ (expt 2 (+ 1 n)))
                (+ -1 (* 2 k))))
         (:= (* #c(0 1) 2 (acl2-pi)
                (/ (expt 2 (+ 1 n)))
                (+ -1 (* 2 k))))
         (:= (* #c(0 1) (* 2 (acl2-pi))
                (/ (expt 2 (+ 1 n)))
                (+ -1 (* 2 k))))
         (:= (* #c(0 1) (* 2 (acl2-pi))
                (+ -1 (* 2 k))
                (/ (expt 2 (+ 1 n)))))
         (:= (* #c(0 1) (* 2 (acl2-pi))
                (/ (+ -1 (* 2 k)) (expt 2 (+ 1 n)))))
         :up (:rewrite e^ix-cos-i-sin)
         :top
         (:use (:instance complex-definition
                          (x (acl2-cosine (* (* 2 (acl2-pi))
                                             (+ -1 (* 2 k))
                                             (/ (expt 2 (+ 1 n))))))
                          (y (acl2-sine (* (* 2 (acl2-pi))
                                           (+ -1 (* 2 k))
                                           (/ (expt 2 (+ 1 n))))))))
         :pro (:forwardchain 1)
         (:dv 1)
         (:dv 1)
         (:dv 1)
         := (:drop 4)
         :up (:rewrite imagpart-complex)
         (:claim (< 0
                    (* (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))))
         (:change-goal nil t)
         :bash (:change-goal nil t)
         (:change-goal nil t)
         (:change-goal nil t)
         (:dv 2)
         (:dv 1)
         (:= (* #c(0 1) 2 (acl2-pi)
                (expt 2 (+ -1 (- n)))))
         :top
         (:use (:instance complex-definition (x 0)
                          (y (* 2 (acl2-pi) (expt 2 (+ -1 (- n)))))))
         :pro (:forwardchain 1)
         (:dv 2)
         (:dv 1)
         (:= (complex 0
                      (* 2 (acl2-pi) (expt 2 (+ -1 (- n))))))
         :up (:rewrite imagpart-complex)
         :up :top :bash
         (:use (:instance complex-definition (x 0)
                          (y (* 2 (acl2-pi) (/ (expt 2 (+ 1 n)))))))
         :pro (:forwardchain 1)
         (:dv 1)
         (:dv 1)
         (:= (complex 0 (* 2 (acl2-pi) (/ (expt 2 (+ 1 n))))))
         :up (:rewrite imagpart-complex)
         :up :bash
         (:claim (<= (* 2 k) (expt 2 (+ 1 n))))
         (:claim (< (+ -1 (* 2 k)) (expt 2 (+ 1 n))))
         (:drop 5)
         :top
         (:use (:instance (:theorem (implies (and (posp x) (posp y) (< x y))
                                             (< (/ x y) 1)))
                          (x (+ -1 (* 2 k)))
                          (y (expt 2 (+ 1 n)))))
         :pro (:forwardchain 1)
         (:claim (< (* (* 2 (acl2-pi))
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    (* 2 (acl2-pi))))
         (:claim (< 0
                    (* (* 2 (acl2-pi))
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))))
         (:drop 4 5)
         (:use (:instance sine-0-only-for-pi
                          (x (* (* 2 (acl2-pi))
                                (+ -1 (* 2 k))
                                (/ (expt 2 (+ 1 n)))))))
         :pro (:contrapose 1)
         (:dv 1)
         (:dv 1)
         :s :up
         (:= (equal (* (* 2 (acl2-pi))
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    (acl2-pi)))
         (:= (equal (* 2 (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    1))
         (:dv 1)
         (:dv 3)
         (:dv 1)
         (:= (* 2 (expt 2 n)))
         :up :up :up
         (:= (* (+ -1 (* 2 k)) (/ (expt 2 n))))
         :up
         (:rewrite |(not (equal (* x (/ y)) 1))|)
         (:dv 1)
         (:claim (not (evenp (+ -1 (* 2 k)))))
         (:claim (evenp (expt 2 n)))
         :top
         :bash :bash)))

(local
 (defthmd expt-zeta-not-one-for-odd-exponents
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 n)))
              (not (equal (abs (expt (zeta (expt 2 (1+ n))) (1- (* 2 k))))
                          1)))
   :hints (("Goal"
            :use ((:instance expt-zeta-not-real-for-odd-exponents))))))

(local
 (defthmd omega-term+dual-lemma-1
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 n)))
              (equal (+ (omega-term k n)
                        (omega-term-dual k n))
                     (/ (* 2 (+ 1 (expt (norm-2c (expt (zeta (expt 2 (1+ n)))
                                                       (- (* 2 k) 1)))
                                        2)))
                        (expt (norm-2c (- 1 (expt (expt (zeta (expt 2 (1+ n)))
                                                        (- (* 2 k) 1))
                                                  2)))
                              2))))
   :hints (("Goal"
            :use ((:instance sum-of-inverses-specialized
                             (z (expt (zeta (expt 2 (1+ n)))
                                      (- (* 2 k) 1))))
                  (:instance expt-zeta-not-one-for-odd-exponents))
            :in-theory (disable zeta)
            ))))

(local
 (defthm norm-2c-expt
     (implies (natp n)
              (equal (norm-2c (expt x n))
                     (expt (norm-2c x) n)))
   :hints (("Goal"
            :induct (expt x n)
            :in-theory (e/d (expt)
                            (norm-2c)))
           ("Subgoal *1/3"
            :use ((:instance norm-2c-product
                             (a x)
                             (b (expt x (1- n)))))
            :in-theory (disable norm-2c-product))
           )
   ))

(local
 (defthm e^2ix-cos-i-sin
     (equal (acl2-exp (* #c(0 2) x))
            (+ (acl2-cosine (* 2 x))
               (* #c(0 1) (acl2-sine (* 2 x)))))
   :hints (("Goal"
            :use ((:instance e^ix-cos-i-sin
                             (x (* 2 x))))))))

(local
 (defthm norm-2c-zeta
     (implies (natp n)
              (equal (norm-2c (zeta n)) 1))
   :hints (("Goal"
            :use ((:instance sin**2+cos**2
                             (x (* 2 (ACL2-PI) (/ N)))))
            :in-theory (disable cosine-2x sine-2x sin**2+cos**2)))
))

(local
 (defthmd omega-term+dual-lemma-2
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 n)))
              (equal (+ (omega-term k n)
                        (omega-term-dual k n))
                     (/ 4
                        (expt (norm-2c (- 1 (expt (expt (zeta (expt 2 (1+ n)))
                                                        (- (* 2 k) 1))
                                                  2)))
                              2))))
   :hints (("Goal"
            :use ((:instance omega-term+dual-lemma-1))
            :in-theory (disable zeta)
            ))))

(local
 (defthm imagpart-2ix
     (implies (realp x)
              (equal (imagpart (* #c(0 2) x)) (* 2 x)))
   :hints (("Goal"
            :use ((:instance imagpart-of-imaginary
                             (x (* 2 x))))))
   ))





(local
 (encapsulate
     ()

     (local
      (defun induction-hint (n)
        (if (and (integerp n)
	         (< 0 n))
	    (1+ (induction-hint (+ n -1)))
            1)))

   (local
    (defthm cos-2npi-n>=0
        (implies (and (integerp n)
		      (<= 0 n))
	         (equal (acl2-cosine (* 2 (acl2-pi) n))
		        1))
      :instructions ((:induct (induction-hint n))
                     :bash :pro (:casesplit (equal n 0))
                     :bash (:forwardchain 2)
                     (:dv 1)
                     (:dv 1)
                     (:dv 3)
                     (:= (+ (+ n -1) 1))
                     :up :up
                     (:= (* (* 2 (acl2-pi)) (+ (+ n -1) 1)))
                     (:rewrite |(* x (+ y z))|)
                     :up (:rewrite cosine-of-sums)
                     (:dv 2)
                     (:= 0)
                     :up (:= 1))))

   (defthm cos-2npi
       (implies (integerp n)
	        (equal (acl2-cosine (* 2 (acl2-pi) n))
		       1))
     :hints (("Goal"
	      :cases ((< n 0)
		      (= n 0)
		      (> n 0)))
	     ("Subgoal 3"
	      :use ((:instance cos-uminus
			       (x (* 2 (acl2-pi) n)))
		    (:instance cos-2npi-n>=0 (n (- n))))
	      :in-theory (disable cos-uminus cos-2npi-n>=0))))

   ))



(local
 (defthm e^2i-pi-n
     (implies (natp n)
              (equal (acl2-exp (* #c(0 2) (acl2-pi) n))
                     1))
   :hints (("Goal"
            :in-theory (disable sine-2x cosine-2x)))
))

(local
 (defthmd flip-zeta-exponents-by-2
     (implies (and (natp m)
                   (natp n))
              (equal (expt (zeta (* 2 n)) (* 2 m))
                     (expt (zeta n) m)))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance EXPT-ACL2-EXP
                             (x (* #c(0 2) (acl2-pi) (/ n)))
                             (n m))
                  (:instance EXPT-ACL2-EXP
                             (x (* #c(0 1) (acl2-pi) (/ n)))
                             (n (* 2 m))))
            :in-theory (disable sine-2x
                                cosine-2x
                                E^IX-COS-I-SIN
                                E^2IX-COS-I-SIN)))
   ))

(local
 (defthmd omega-term+dual
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 n)))
              (equal (+ (omega-term k n)
                        (omega-term-dual k n))
                     (* 4 (omega-term k (1- n)))))
   :hints (("Goal"
            :use ((:instance omega-term+dual-lemma-2)
                  (:instance flip-zeta-exponents-by-2
                             (n (expt 2 n))
                             (m (+ -1 (* 2 k))))
                  )
            :in-theory (disable zeta norm-2c)
            ))))

(local
 (defthmd omega-series+dual
     (implies (and (posp n)
                   (posp i)
                   (posp k)
                   (<= k (expt 2 n)))
              (equal (+ (omega-series i k n)
                        (omega-series-dual i k n))
                     (* 4 (omega-series i k (1- n)))))
   :hints (("Goal"
            :induct (omega-series i k n)
            :in-theory (disable omega-term omega-term-dual)
            )
           ("Subgoal *1/3"
            :use ((:instance omega-term+dual (k i))))
           ("Subgoal *1/1"
            :use ((:instance omega-term+dual (k i))))
           )))

(local
 (defthmd omega-series-recurrence
     (implies (and (posp n)
                   (< 1 n))
              (equal (omega-series 1 (expt 2 (1- n)) n)
                     (* 4 (omega-series 1 (expt 2 (- n 2)) (1- n)))))
   :hints (("Goal"
            :use ((:instance paired-omega-series-half)
                  (:instance omega-series+dual
                             (i 1)
                             (k (expt 2 (- n 1)))
                             (n n))
                  (:instance paired-omega-series-half-2
                             (n (1- n)))
                  )
            :in-theory (disable omega-series
                                omega-series-dual)))))

(local
 (defthmd omega-series-sum-base
     (implies (= n 1)
              (equal (omega-series 1 n n)
                     (expt 2 (- (* 2 n) 3))))
   :hints (("Goal"
            :use ((:instance omega-series-1-1-1))
            :in-theory (disable omega-series
                                omega-series-1-1-1)))))

(local
 (encapsulate nil

     (local
      (defun induction-hint (n)
        (if (and (integerp n)
	         (< 0 n))
	    (1+ (induction-hint (+ n -1)))
            1)))

   (defthmd omega-series-closed-form
       (implies (posp n)
                (equal (omega-series 1 (expt 2 (1- n)) n)
                       (expt 2 (- (* 2 n) 3))))
     :hints (("Goal"
              :induct (induction-hint n)
              :in-theory (disable omega-series))
             ("Subgoal *1/1"
              :use ((:instance omega-series-recurrence)))
             )))
 )

;;; The above is the main theorem in page 2. Now we do the corollary on that
;;; page.

(local
 (encapsulate nil

     (local
      (defthmd lemma-1
          (implies (and (posp n)
                        (posp k))
                   (equal (expt (norm-2c (- 1 (expt (zeta n) k))) 2)
                          (- 2 (+ (expt (zeta n) k)
                                  (conjugate (expt (zeta n) k))))))
        :hints (("Goal"
                 :use ((:instance conjugate-product-normsq (z (- 1 (expt (zeta n) k))))
                       (:instance conjugate-product-normsq (z (expt (zeta n) k))))
                 :in-theory (e/d (conjugate-of-sum
                                  conjugate-uminus)
                                 (norm-2c conjugate zeta))
                 ))))

   (local
    (defthmd lemma-2
        (equal (+ z (conjugate z))
               (* 2 (realpart z)))
      :instructions ((:use (:instance realpart-imagpart-elim (x z)))
                     (:use (:instance complex-definition (x (realpart z))
                                      (y (imagpart z))))
                     (:use (:instance complex-definition (x (realpart z))
                                      (y (- (imagpart z)))))
                     :pro (:forwardchain 1)
                     (:forwardchain 1)
                     (:casesplit (acl2-numberp z) th)
                     (:casesplit (acl2-numberp z))
                     (:forwardchain 1)
                     (:dv 1)
                     (:dv 1)
                     := (:drop 5)
                     := (:drop 2)
                     :nx :x := (:drop 1)
                     :top :s (:dv 1)
                     (:dv 2)
                     (:= (- (* #c(0 1) (imagpart z))))
                     :up :top (:dv 1)
                     (:rewrite inverse-of-+)
                     :bash :bash)
      ))

   (local
    (defthmd lemma-3
        (implies (and (posp n)
                      (posp k))
                 (equal (expt (norm-2c (- 1 (expt (zeta n) k))) 2)
                        (- 2 (+ (* 2 (realpart (expt (zeta n) k)))))))
      :hints (("Goal"
               :use ((:instance lemma-1)
                     (:instance lemma-2 (z (expt (zeta n) k))))
               :in-theory (disable zeta  norm-2c)
               ))))

   (local
    (defthmd lemma-4
        (implies (and (posp n)
                      (posp k))
                 (equal (realpart (expt (zeta n) k))
                        (acl2-cosine (* 2 (acl2-pi) (/ n) k))))
      :hints (("Goal"
               :use ((:instance EXPT-ACL2-EXP
                                (x (* #C(0 2) (ACL2-PI) (/ N)))
                                (n k))
                     (:instance E^2IX-COS-I-SIN
                                (x (* (ACL2-PI) K (/ N))))
                     )
               :in-theory (disable sine-2x cosine-2x
                                   E^IX-COS-I-SIN
                                   E^2IX-COS-I-SIN
                                   expt-acl2-exp)))
      ))

   (local
    (defthmd lemma-5
        (implies (and (posp n)
                      (posp k))
                 (equal (expt (norm-2c (- 1 (expt (zeta n) k))) 2)
                        (- 2 (+ (* 2 (acl2-cosine (* 2 (acl2-pi) (/ n) k)))))))
      :hints (("Goal"
               :use ((:instance lemma-3)
                     (:instance lemma-4))
               :in-theory (disable zeta  norm-2c)
               ))))

   (local
    (defthmd lemma-6
        (equal (acl2-cosine (* 2 x))
               (- 1 (* 2 (expt (acl2-sine x) 2))))
      :hints (("Goal"
               :use ((:instance cosine-2x)
                     (:instance cos**2->1-sin**2))
               :in-theory (disable cosine-2x
                                   cos**2->1-sin**2)))))

   (local
    (defthmd lemma-7
        (implies (and (posp n)
                      (posp k))
                 (equal (expt (norm-2c (- 1 (expt (zeta n) k))) 2)
                        (- 2 (+ (* 2 (- 1 (* 2 (expt (acl2-sine (* (acl2-pi) (/ n) k)) 2))))))))
      :hints (("Goal"
               :use ((:instance lemma-5)
                     (:instance lemma-6 (x (* (acl2-pi) (/ n) k))))
               :in-theory (disable zeta  norm-2c)
               ))))

   (local
    (defthmd lemma-8
        (implies (and (posp n)
                      (posp k))
                 (equal (expt (norm-2c (- 1 (expt (zeta n) k))) 2)
                        (* 4 (expt (acl2-sine (* (acl2-pi) (/ n) k)) 2))))
      :hints (("Goal"
               :use ((:instance lemma-7))
               :in-theory (disable zeta  norm-2c)
               ))))


   (defthmd omega-term->sin
       (implies (and (posp n)
                     (posp k))
                (equal (omega-term k n)
                       (/ (* 4 (expt (acl2-sine (* (acl2-pi)
                                                   (- (* 2 k) 1)
                                                   (/ (expt 2 (1+ n)))))
                                     2)))))
     :hints (("Goal"
              :use ((:instance lemma-8
                               (n (expt 2 (1+  n)))
                               (k (- (* 2 k) 1))))
              :in-theory (disable zeta
                                  )
              )))
   ))

(local
 (defun sine-series (k m n)
   (declare (xargs :measure (nfix (- m k))))
   (if (zp (- m k))
       (if (= m k)
           (/ (expt (acl2-sine (* (acl2-pi)
                                  (- (* 2 k) 1)
                                  (/ (expt 2 (1+ n)))))
                    2))
           0)
       (+ (/ (expt (acl2-sine (* (acl2-pi)
                                 (- (* 2 k) 1)
                                 (/ (expt 2 (1+ n)))))
                   2))
          (sine-series (1+ k) m n)))))

(local
 (defthmd sine-series-closed-form-lemma
     (implies (and (posp i)
                   (posp k)
                   (posp n))
              (equal (sine-series i k n)
                     (* 4 (omega-series i k n))))
   :instructions ((:in-theory (disable omega-term))
                  (:induct (omega-series i k n))
                  (:change-goal nil t)
                  :bash :pro (:dv 1)
                  (:= (/ (expt (acl2-sine (* (acl2-pi)
                                             (+ -1 (* 2 i))
                                             (/ (expt 2 (+ 1 n)))))
                               2)))
                  :nx (:dv 2)
                  :x (:rewrite omega-term->sin)
                  :top :bash :pro (:forwardchain 2)
                  (:dv 1)
                  :x-dumb
                  (:= (+ (/ (expt (acl2-sine (* (acl2-pi)
                                                (+ -1 (* 2 i))
                                                (/ (expt 2 (+ 1 n)))))
                                  2))
                         (sine-series (+ 1 i) k n)))
                  (:dv 2)
                  := (:drop 5)
                  :top (:dv 2)
                  (:dv 2)
                  :x
                  (:= (+ (omega-term i n)
                         (omega-series (+ 1 i) k n)))
                  (:dv 1)
                  (:rewrite omega-term->sin)
                  :top :bash)))

(local
 (defthmd sine-series-closed-form
     (implies (posp n)
              (equal (sine-series 1 (expt 2 (1- n)) n)
                     (expt 2 (- (* 2 n) 1))))
   :hints (("Goal"
            :use ((:instance omega-series-closed-form)
                  (:instance sine-series-closed-form-lemma
                             (i 1)
                             (k (expt 2 (1- n)))))
            :in-theory (disable sine-series omega-series)))))


(local
 (defthm sign-sumlist-alternating-sequence
     (implies (and (alternating-sequence-p x)
		   (real-listp x)
		   (not (null x)))
              (cond ((< 0 (car x))
                     (< 0 (sumlist x)))
                    ((equal 0 (car x))
                     (equal (sumlist x) 0))
                    ((< (car x) 0)
                     (< (sumlist x) 0))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance sumlist-alternating-sequence-lemma)
                  (:instance sumlist-alternating-sequence))
            :in-theory (disable sumlist-alternating-sequence)))))

(encapsulate nil

    (local
     (defthm lemma-1
         (implies (and (realp x)
                       (realp y)
                       (realp z)
                       (< 0 z))
                  (equal (< (* z x) (* z y))
                         (< x y)))))

  (local
   (defthmd lemma-2
       (implies (and (posp counter)
                     (realp x)
                     (< 0 x)
                     (<= x 2)
                     )
                (< (* (expt x 2)
                      (/ (factorial (+ 2 counter))))
                   (/ (factorial counter))))
     :instructions (:pro (:dv 1)
                         (:dv 1)
                         (:= (* x x))
                         :nx (:dv 1)
                         :x-dumb
                         (:= (* (+ 2 counter)
                                (factorial (+ 1 counter))))
                         (:dv 2)
                         :x-dumb
                         (:= (* (+ 1 counter) (factorial counter)))
                         :top (:claim (<= 1 (factorial counter)))
                         (:= (< (* (factorial counter)
                                   (* x x)
                                   (/ (* (+ 2 counter)
                                         (+ 1 counter)
                                         (factorial counter))))
                                (* (factorial counter)
                                   (/ (factorial counter)))))
                         (:dv 1)
                         (:= (* (* x x)
                                (/ (* (+ 2 counter) (+ 1 counter)))))
                         :nx (:= 1)
                         :top
                         (:claim (<= 1 (* (+ 2 counter) (+ 1 counter))))
                         (:dv 1)
                         (:dv 2)
                         (:rewrite |arith (/ (* x y))|)
                         :top (:claim (posp (+ 2 counter)))
                         (:claim (posp (+ 1 counter)))
                         (:claim (<= x (+ 1 counter)))
                         (:claim (< x (+ 2 counter)))
                         (:generalize ((+ 2 counter) counter+2)
                                      ((+ 1 counter) counter+1))
                         (:dv 1)
                         (:= (* (/ x counter+1) (/ x counter+2)))
                         (:claim (realp (* x (/ counter+1))))
                         (:claim (realp (* x (/ counter+2))))
                         (:claim (< 0 (* x (/ counter+1))))
                         (:claim (< 0 (* x (/ counter+2))))
                         (:claim (<= (* x (/ counter+1)) 1))
                         (:claim (< (* x (/ counter+2)) 1))
                         :top
                         (:use (:instance lemma-1 (x (* x (/ counter+2)))
                                          (y 1)
                                          (z (* x (/ counter+1)))))
                         :pro (:demote 1)
                         (:dv 1)
                         (:dv 1)
                         :s :up
                         (:= (< (* (* x (/ counter+1)) x (/ counter+2))
                                (* x (/ counter+1))))
                         :top
                         :pro :bash)))


  (defthm alternating-sequence-2-p-taylor-sincos
      (implies (and (realp sign)
		    (not (equal sign 0))
		    (posp counter)
		    (natp nterms)
		    (realp x)
		    (< 0 x)
		    (<= x 2))
	       (alternating-sequence-2-p
	        (taylor-sincos-list nterms
				    counter
				    sign
				    x)))
    :hints (("Goal"
	     :induct (taylor-sincos-list nterms counter sign x))
            ("Subgoal *1/2"
             :use ((:instance lemma-2)))
            ))
  )

(local
 (defthm alternating-sequence-p-taylor-sincos
     (implies (and (realp sign)
		   (not (equal sign 0))
		   (posp counter)
		   (natp nterms)
		   (realp x)
		   (< 0 x)
		   (<= x 2))
	      (alternating-sequence-p
	       (taylor-sincos-list nterms
				   counter
				   sign
				   x)))
   ))

(local (in-theory (disable alternating-sequence-p)))

(local
 (defthm open-taylor-sincos-list-zp-nterms
     (implies (zp nterms)
              (equal (taylor-sincos-list nterms counter sign x)
                     nil))))

(local
 (defthmd sin-x-<=-x-lemma
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   (posp nterms)
                   (realp sign)
                   )
              (<= (sumlist (taylor-sincos-list nterms 1 1 x)) x))
   :hints (("Goal"
            :do-not-induct t
            :expand (taylor-sincos-list nterms 1 1 x)
            :use ((:instance sign-sumlist-alternating-sequence
                             (x (taylor-sincos-list (- nterms 2) 3 -1 x)))
                  (:instance alternating-sequence-p-taylor-sincos
                             (nterms (+ -2 nterms))
                             (counter 3)
                             (sign -1)
                             (x x))
                  (:instance car-taylor-sincos-list
                             (nterms (+ -2 nterms))
                             (counter 3)
                             (sign -1)
                             (x x))
                  )
            :in-theory (disable car-taylor-sincos-list)
            )
           )))

(local
 (defthmd x-x^3/6-<=-sin-x-lemma
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   (posp nterms)
                   (<= 4 nterms)
                   (realp sign)
                   )
              (<= (- x (* 1/6 (expt x 3)))
                  (sumlist (taylor-sincos-list nterms 1 1 x))))
   :hints (("Goal"
            :do-not-induct t
            :expand ((taylor-sincos-list nterms 1 1 x)
                     (taylor-sincos-list (+ -2 nterms) 3 -1 x))
            :use ((:instance sign-sumlist-alternating-sequence
                             (x (taylor-sincos-list (- nterms 4) 5 1 x)))
                  (:instance alternating-sequence-p-taylor-sincos
                             (nterms (+ -4 nterms))
                             (counter 5)
                             (sign 1)
                             (x x))
                  (:instance car-taylor-sincos-list
                             (nterms (+ -4 nterms))
                             (counter 5)
                             (sign 1)
                             (x x))
                  )
            :in-theory (disable car-taylor-sincos-list)
            )
           )))

(local
 (defthm posp-1-i-large-integer
     (POSP (+ -1 (I-LARGE-INTEGER)))))

(local
 (defthmd sin-x-<=-x-standard
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   (standardp x)
                   )
              (<= (acl2-sine x) x))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance taylorish-sin-valid
                             (x x))
                  (:instance sin-x-<=-x-lemma
                             (nterms (- (i-large-integer) 1))
                             (sign 1)
                             (x x))
                  (:instance STANDARD-PART-<=
                             (x (sumlist (taylor-sincos-list (+ -1 (i-large-integer))
                                                             1 1 x)))
                             (y x))
                  )
            :in-theory (disable car-taylor-sincos-list)
            )
           )))

(local
 (defthm-std sin-x-<=-x
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   )
              (<= (acl2-sine x) x))
   :hints (("Goal'" :by sin-x-<=-x-standard))))


(local
 (defthm 5-<-large-integer
     (not (< (i-large-integer) 5))
   :hints (("Goal"
            :use ((:instance large->-non-large
                             (x (i-large-integer))
                             (y 5)))))))

(local
 (defthmd x-x^3/6-<=-sin-x-standard
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   (standardp x)
                   )
              (<= (- x (* 1/6 (expt x 3)))
                  (acl2-sine x)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance taylorish-sin-valid
                             (x x))
                  (:instance x-x^3/6-<=-sin-x-lemma
                             (nterms (- (i-large-integer) 1))
                             (sign 1)
                             (x x))
                  (:instance STANDARD-PART-<=
                             (x (- x (* 1/6 (expt x 3))))
                             (y (sumlist (taylor-sincos-list (+ -1 (i-large-integer))
                                                             1 1 x))))
                  )
            :in-theory (disable car-taylor-sincos-list
                                standard-part-<=)
            )
           )))

(local
 (defthm-std x-x^3/6-<=-sin-x
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   )
              (<= (- x (* 1/6 (expt x 3)))
                  (acl2-sine x)))
   :hints (("Goal'"
            :by x-x^3/6-<=-sin-x-standard))))

(local
 (defthmd sin-x-/-x-<=-1
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   )
              (<= (/ (acl2-sine x) x) 1))
   :hints (("Goal"
            :use ((:instance sin-x-<=-x))))))

(local
 (defthmd 1-x^2/6-<=-sin-x-/-x
     (implies (and (realp x)
                   (< 0 x)
                   (<= x 2)
                   )
              (<= (- 1 (* 1/6 (expt x 2)))
                  (/ (acl2-sine x) x)))
   :hints (("Goal"
            :use ((:instance x-x^3/6-<=-sin-x)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (< 0 x))
                                      (equal (<= (* x y) (* x z))
                                             (<= y z))))
                   (x (/ x))
                   (y (- x (* 1/6 (expt x 3))))
                   (z (acl2-sine x))))
            ))))

(local
 (defthmd 1-<=-x-/-sin-x
     (implies (and (realp x)
                   (< 0 x)
                   (<= x (* 1/2 (acl2-pi)))
                   )
              (<= 1 (/ x (acl2-sine x))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance sin-x-/-x-<=-1)
                  (:instance acl2-pi-gross-upper-bound)
                  (:instance sine-positive-in-0-2)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (< 0 x))
                                      (equal (<= (* x y) (* x z))
                                             (<= y z))))
                   (x (* X (/ (ACL2-SINE X))))
                   (y (* (/ X) (ACL2-SINE X)))
                   (z 1)))
            :in-theory (disable acl2-pi-gross-upper-bound
                                pi-between-2-4
                                sine-positive-in-0-2)))))

(local
 (defthmd x-/-sin-x-<=-1/1-x^2/6
     (implies (and (realp x)
                   (< 0 x)
                   (<= x (* 1/2 (acl2-pi)))
                   )
              (<= (/ x (acl2-sine x))
                  (/ (- 1 (* 1/6 (expt x 2))))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance 1-x^2/6-<=-sin-x-/-x)
                  (:instance acl2-pi-gross-upper-bound)
                  (:instance sine-positive-in-0-2)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (< 0 x)
                                           (< 0 y))
                                      (equal (<= (/ x) (/ y))
                                             (<= y x))))
                   (x (/ (acl2-sine x) x))
                   (y (- 1 (* 1/6 (expt x 2)))))
                  (:instance
                   (:theorem (implies (and (realp x) (<= 0 x) (<= x 2))
                                      (<= (expt x 2) 4))))
                  )
            :in-theory (disable acl2-pi-gross-upper-bound
                                pi-between-2-4
                                sine-positive-in-0-2))
           ("Subgoal 1"
            :use ((:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (< 0 x))
                                      (equal (<= (* x y) (* x z))
                                             (<= y z))))
                   (x x)
                   (y x)
                   (z 2))))
           )))


(local
 (defthmd <-squares
     (implies (and (realp x)
                   (realp y)
                   (< 0 x)
                   (< 0 y))
              (equal (< (expt x 2) (expt y 2))
                     (< x y)))
   :hints (("Goal"
            :cases ((< x y)))
           ("Subgoal 1"
            :use ((:instance
                   (:theorem (implies (and (realp x) (realp y)
                                           (< 0 x) (< 0 y) (< x y))
                                      (and (< (* x x) (* x y))
                                           (< (* x y) (* y y))))))
                  (:instance
                   (:theorem (implies (and (realp x) (realp y) (realp z)
                                           (< x y) (< y z))
                                      (< x z)))
                             (x (* x x))
                             (y (* x y))
                             (z (* y y))))))))

(local
 (defthmd <=-squares
     (implies (and (realp x)
                   (realp y)
                   (< 0 x)
                   (< 0 y))
              (equal (<= (expt x 2) (expt y 2))
                     (<= x y)))
   :hints (("Goal"
            :cases ((= x y) (< x y) (< y x)))
           ("Subgoal 1"
            :use ((:instance <-squares (x y) (y x)))))))

(local
 (defthmd 1-<=-x-/-sin-x-squares
     (implies (and (realp x)
                   (< 0 x)
                   (<= x (* 1/2 (acl2-pi)))
                   )
              (<= 1 (expt (/ x (acl2-sine x)) 2)))
   :hints (("Goal"
            :use ((:instance <=-squares
                             (x 1)
                             (y (/ x (acl2-sine x))))
                  (:instance 1-<=-x-/-sin-x))))))

(local
 (defthmd x-/-sin-x-<=-1/1-x^2/6-squares
     (implies (and (realp x)
                   (< 0 x)
                   (< x (* 1/2 (acl2-pi)))
                   )
              (<= (expt (/ x (acl2-sine x)) 2)
                  (expt (/ (- 1 (* 1/6 (expt x 2)))) 2)))
  :instructions ((:use (:instance <=-squares (x (/ x (acl2-sine x)))
                                  (y (/ (- 1 (* 1/6 (expt x 2)))))))
                 (:use (:instance x-/-sin-x-<=-1/1-x^2/6))
                 :pro (:forwardchain 1)
                 (:demote 1)
                 (:dv 1)
                 (:dv 1)
                 :s
                 (:claim (< 0 (* x (/ (acl2-sine x)))))
                 :s :top (:use acl2-pi-gross-upper-bound)
                 :pro (:claim (< (* 1/2 (acl2-pi)) 2))
                 (:claim (< x 2))
                 (:use (:instance <-squares (x x) (y 2)))
                 :pro (:forwardchain 1)
                 (:claim (< (expt x 2) 4))
                 (:demote 7)
                 (:dv 1)
                 (:dv 1)
                 (:= t)
                 :up (:= (equal (<= (expt (* x (/ (acl2-sine x))) 2)
                                    (expt (/ (+ 1 (- (* 1/6 (expt x 2)))))
                                          2))
                                (<= (* x (/ (acl2-sine x)))
                                    (/ (+ 1 (- (* 1/6 (expt x 2))))))))
                 :up :pro
                 := :s)))

(encapsulate nil

    (local
     (defthmd lemma-1
         (implies (and (realp x)
                       (< 0 x)
                       (< (expt x 2) 3))
                  (< 0 (* (- (expt x 2) 3) (- (expt x 2) 8))))
       :instructions (:pro (:claim (< (expt x 2) 8))
                           (:claim (< (+ -3 (expt x 2)) 0))
                           (:claim (< (+ -8 (expt x 2)) 0))
                           :bash)))

  (local
   (defthmd lemma-2
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< 0 (+ (expt x 4) (* -11 (expt x 2))
                        24)))
     :hints (("Goal"
              :use lemma-1))))

  (local
   (defthmd lemma-3
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< 0 (+ (expt x 6) (* -11 (expt x 4)) (* 24 (expt x 2)))))
     :hints (("Goal"
              :use ((:instance lemma-2)
                    (:instance (:theorem
                                (implies (and (realp x) (realp y)
                                              (< 0 x) (< 0 y))
                                         (< 0 (* x y))))
                               (x (+ (expt x 4) (* -11 (expt x 2)) 24))
                               (y (expt x 2))))))))

  (local
   (defthmd lemma-4
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< 0 (+ (expt x 6) (* -11 (expt x 4)) (* 24 (expt x 2)))))
     :hints (("Goal"
              :use ((:instance lemma-3)
                    (:instance (:theorem
                                (implies (and (realp x) (realp y)
                                              (< 0 x) (< 0 y))
                                         (< 0 (* x y))))
                               (x (+ (expt x 4) (* -11 (expt x 2)) 24))
                               (y (expt x 2))))))))

  (local
   (defthmd lemma-5
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< 36 (* (+ 36 (* -12 (expt x 2)) (expt x 4))
                         (+ 1 (expt x 2)))))
     :hints (("Goal"
              :use ((:instance lemma-4))))))

  (local
   (defthmd lemma-6
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< 36 (* (expt (- 6 (expt x 2)) 2)
                         (+ 1 (expt x 2)))))
     :hints (("Goal"
              :use ((:instance lemma-5))))))

  (local
   (defthmd lemma-7
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< (/ 36 (expt (- 6 (expt x 2)) 2))
                   (+ 1 (expt x 2))))
     :instructions
     ((:use (:instance lemma-6))
      (:use (:instance (:theorem (implies (and (realp x)
                                               (realp y)
                                               (realp z)
                                               (< 0 x))
                                          (equal (< (* x y) (* x z)) (< y z))))
                       (x (expt (- 6 (expt x 2)) 2))
                       (y (/ 36 (expt (- 6 (expt x 2)) 2)))
                       (z (+ 1 (expt x 2)))))
      :pro (:forwardchain 2)
      (:forwardchain 1)
      := (:dv 1)
      (:claim (realp (expt (+ 6 (- (expt x 2))) 2)))
      (:claim (< 0 (expt (+ 6 (- (expt x 2))) 2)))
      (:= (* 36 (expt (+ 6 (- (expt x 2))) 2)
             (/ (expt (+ 6 (- (expt x 2))) 2))))
      (:dive 2)
      (:rewrite |(* a (/ a))|)
      (:= 1)
      :top
      :s :bash)))

  (local
   (defthmd lemma-8
       (implies (realp x)
                (equal (/ 36 (expt (- 6 (expt x 2)) 2))
                       (/ 1 (expt (- 1 (* 1/6 (expt x 2))) 2))))
     :instructions (:pro (:dv 2)
                         (:dv 2)
                         (:dv 1)
                         (:dv 1)
                         (:= (* 1/6 (- 6 (expt x 2))))
                         :up (:rewrite |(expt (* x y) n)|)
                         (:dv 1)
                         :s :up
                         :top :bash)))

  (local
   (defthmd lemma-9
       (implies (and (realp x)
                     (< 0 x)
                     (< (expt x 2) 3))
                (< (/ 1 (expt (- 1 (* 1/6 (expt x 2))) 2))
                   (+ 1 (expt x 2))))
     :hints (("Goal"
              :use ((:instance lemma-7)
                    (:instance lemma-8))))))

  (local
   (defthmd lemma-10
       (< (expt (* 1/2 (m-pi+eps)) 2) 3)))


  (local
   (defthmd lemma-11
       (implies (and (realp x)
                     (< 0 x)
                     (< x (* 1/2 (acl2-pi))))
                (< (expt x 2) 3))
     :hints (("Goal"
              :use ((:instance lemma-10)
                    (:instance <-squares
                               (x x)
                               (y (* 1/2 (m-pi+eps))))
                    (:instance pi-tight-bound))))
     ))

  (local
   (defthmd lemma-13
       (implies (and (realp x)
                     (< 0 x)
                     (< x (* 1/2 (acl2-pi))))
                (< (/ (expt (- 1 (* 1/6 (expt x 2))) 2))
                   (+ 1 (expt x 2))))
     :hints (("Goal"
              :use ((:instance lemma-9)
                    (:instance lemma-11))))))

  (defthmd x-/-sin-x-<=-1+x^2
      (implies (and (realp x)
                    (< 0 x)
                    (< x (* 1/2 (acl2-pi)))
                    )
               (<= (expt (/ x (acl2-sine x)) 2)
                   (+ 1 (expt x 2))))
    :hints (("Goal"
             :use ((:instance x-/-sin-x-<=-1/1-x^2/6-squares)
                   (:instance lemma-13)))))
  )

(local
 (defthmd term-in-sum-<-pi/2
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (< (* (acl2-pi)
                    (- (* 2 k) 1)
                    (/ (expt 2 (1+ n))))
                 (* 1/2 (acl2-pi))))
   :instructions (:pro (:casesplit (< (* (+ -1 (* 2 k)) (/ (expt 2 (+ 1 n))))
                                      1/2))
                       :bash (:contrapose 4)
                       (:drop 4)
                       (:claim (<= (* 2 k) (expt 2 n)))
                       (:claim (< (+ -1 (* 2 k)) (expt 2 n)))
                       (:claim (= (* (expt 2 n) (/ (expt 2 (+ 1 n))))
                                  1/2))
                       (:dv 2)
                       (:= (* (expt 2 n) (/ (expt 2 (+ 1 n)))))
                       :up
                       (:claim (and (realp (+ -1 (* 2 k)))
                                    (< 0 (+ -1 (* 2 k)))))
                       (:claim (and (realp (/ (expt 2 (+ 1 n))))
                                    (< 0 (/ (expt 2 (+ 1 n))))))
                       (:claim (and (realp (expt 2 n))
                                    (< 0 (expt 2 n))))
                       (:generalize ((+ -1 (* 2 k)) a)
                                    ((/ (expt 2 (+ 1 n))) b)
                                    ((expt 2 n) c))
                       (:drop 6)
                       :bash)
   ))


(local
 (defthmd big-lower-bound-lemma-1
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= 1 (expt (/ (* (acl2-pi)
                                (- (* 2 k) 1)
                                (/ (expt 2 (1+ n))))
                             (acl2-sine (* (acl2-pi)
                                           (- (* 2 k) 1)
                                           (/ (expt 2 (1+ n))))))
                          2)))
   :hints (("Goal"
            :use ((:instance 1-<=-x-/-sin-x-squares
                             (x (* (acl2-pi)
                                   (- (* 2 k) 1)
                                   (/ (expt 2 (1+ n))))))
                  (:instance term-in-sum-<-pi/2)
                  )
            ))))

(local
 (defthmd big-lower-bound-lemma-2
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= 1 (/ (expt (* (acl2-pi)
                                (- (* 2 k) 1)
                                (/ (expt 2 (1+ n))))
                             2)
                       (expt (acl2-sine (* (acl2-pi)
                                           (- (* 2 k) 1)
                                           (/ (expt 2 (1+ n)))))
                             2))))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma-1)
                  )
            ))))

(local
 (defthmd big-lower-bound-lemma-3
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (expt (* (acl2-pi)
                              (- (* 2 k) 1)
                              (/ (expt 2 (1+ n))))
                           2))
                  (/ (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))))
   :instructions ((:use (:instance big-lower-bound-lemma-2))
                  (:use (:instance (:theorem (implies (and (realp x)
                                                           (realp y)
                                                           (< 0 x)
                                                           (< 0 y)
                                                           (<= 1 (/ x y)))
                                                      (<= (/ x) (/ y))))
                                   (x (expt (* (acl2-pi)
                                               (- (* 2 k) 1)
                                               (/ (expt 2 (1+ n))))
                                            2))
                                   (y (expt (acl2-sine (* (acl2-pi)
                                                          (- (* 2 k) 1)
                                                          (/ (expt 2 (1+ n)))))
                                            2))))
                  :pro (:forwardchain 2)
                  (:use term-in-sum-<-pi/2)
                  :pro (:forwardchain 1)
                  (:claim (< 0
                             (* (acl2-pi)
                                (+ -1 (* 2 k))
                                (/ (expt 2 (+ 1 n))))))
                  (:change-goal nil t)
                  :bash
                  (:claim (< 0
                             (acl2-sine (* (acl2-pi)
                                           (+ -1 (* 2 k))
                                           (/ (expt 2 (+ 1 n)))))))
                  (:forwardchain 1)
                  :s)))

(local
 (defthmd big-lower-bound-lemma-4
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (equal (/ (expt (* (acl2-pi)
                                 (- (* 2 k) 1)
                                 (/ (expt 2 (1+ n))))
                              2))
                     (/ (* 4 (expt (expt 2 n) 2))
                        (* (expt (acl2-pi) 2)
                           (expt (- (* 2 k) 1) 2)))))
   ))

(local
 (defthmd big-lower-bound-lemma-5
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (* 4 (expt (expt 2 n) 2))
                     (* (expt (acl2-pi) 2)
                        (expt (- (* 2 k) 1) 2)))
                  (/ (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma-3)
                  (:instance big-lower-bound-lemma-4))))))

(local
 (defthmd big-lower-bound-lemma-6
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ 4
                     (* (expt (acl2-pi) 2)
                        (expt (- (* 2 k) 1) 2)))
                  (* (/ (expt (expt 2 n) 2))
                     (/ (expt (acl2-sine (* (acl2-pi)
                                            (- (* 2 k) 1)
                                            (/ (expt 2 (1+ n)))))
                              2)))))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma-5)
                  (:instance (:theorem
                              (implies (and (realp x) (realp y) (realp z)
                                            (< 0 x) (<= y z))
                                       (<= (* x y) (* x z))))
                             (x (/ (expt (expt 2 n) 2)))
                             (y (/ (* 4 (expt (expt 2 n) 2))
                                   (* (expt (acl2-pi) 2)
                                      (expt (- (* 2 k) 1) 2))))
                             (z (/ (expt (acl2-sine (* (acl2-pi)
                                                       (- (* 2 k) 1)
                                                       (/ (expt 2 (1+ n)))))
                                         2)))))
                  ))))

(local
 (defun basel-odds (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt (- (* 2 i) 1) -2)
         (basel-odds (1+ i) n)))))

(local
 (defun basel-evens (i n)
  (declare (xargs :measure (nfix (- n i))))
  (if (zp (- n i))
      0
      (+ (expt (* 2 i) -2)
         (basel-evens (1+ i) n)))))


(local
 (defthmd big-lower-bound-lemma
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (* (/ 4 (expt (acl2-pi) 2))
                     (basel-odds k (1+ (expt 2 (1- n)))))
                  (* (/ (expt (expt 2 n) 2))
                     (sine-series k (expt 2 (1- n)) n))))
   :instructions ((:induct (sine-series k (expt 2 (1- n)) n))
                  (:change-goal nil t)
                  :bash
                  (:use (:instance big-lower-bound-lemma-6))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  (:dv 2)
                  :x :top (:dv 2)
                  (:dv 2)
                  :x-dumb
                  (:= (/ (expt (acl2-sine (* (acl2-pi)
                                             (+ -1 (* 2 k))
                                             (/ (expt 2 (+ 1 n)))))
                               2)))
                  :top :bash :pro (:forwardchain 2)
                  (:dv 1)
                  (:dv 2)
                  :x
                  (:= (+ (expt (+ -1 (* 2 k)) -2)
                         (basel-odds (+ 1 k)
                                     (+ 1 (expt 2 (+ -1 n))))))
                  :top (:dv 2)
                  (:dv 2)
                  :x-dumb
                  (:= (+ (/ (expt (acl2-sine (* (acl2-pi)
                                                (+ -1 (* 2 k))
                                                (/ (expt 2 (+ 1 n)))))
                                  2))
                         (sine-series (+ 1 k)
                                      (expt 2 (+ -1 n))
                                      n)))
                  :top
                  (:use (:instance big-lower-bound-lemma-6))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  (:rewrite |(* x (+ y z))|)
                  :top (:dv 2)
                  (:rewrite |(* x (+ y z))|)
                  :top (:demote 6)
                  (:dv 1)
                  (:dv 1)
                  (:= (* (* 4 (/ (expt (acl2-pi) 2)))
                         (expt (+ -1 (* 2 k)) -2)))
                  :top :pro
                  (:in-theory (disable sine-series basel-odds))
                  :bash)))

(local
 (defthmd big-lower-bound-lemma-specialized-1
     (implies (posp n)
              (<= (* (/ 4 (expt (acl2-pi) 2))
                     (basel-odds 1 (1+ (expt 2 (1- n)))))
                  (* (/ (expt (expt 2 n) 2))
                     (expt 2 (- (* 2 n) 1)))))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma (k 1))
                  (:instance sine-series-closed-form))
            :in-theory (disable sine-series
                                basel-odds)
            ))))

(local
 (defthmd big-lower-bound-lemma-specialized-2
     (implies (posp n)
              (<= (* (/ 4 (expt (acl2-pi) 2))
                     (basel-odds 1 (1+ (expt 2 (1- n)))))
                  1/2))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma-specialized-1))
            :in-theory (disable sine-series
                                basel-odds)
            ))))

(local
 (defthm realp-basel-odds
     (implies (realp i)
              (realp (basel-odds i n)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthmd big-lower-bound-lemma-specialized-3
     (implies (posp n)
              (<= (basel-odds 1 (1+ (expt 2 (1- n))))
                  (/ (expt (acl2-pi) 2) 8)))
   :instructions
   ((:use (:instance big-lower-bound-lemma-specialized-2))
    (:in-theory (disable basel-odds))
    :pro (:forwardchain 1)
    (:contrapose 2)
    (:= (< 1/8
           (* (/ (expt (acl2-pi) 2))
              (basel-odds 1 (+ 1 (expt 2 (+ -1 n)))))))
    (:use (:instance (:theorem (implies (and (realp x)
                                             (realp y)
                                             (realp z)
                                             (< 0 z))
                                        (equal (< (* z x) (* z y)) (< x y))))
                     (x 1/8)
                     (y (* (/ (expt (acl2-pi) 2))
                           (basel-odds 1 (+ 1 (expt 2 (+ -1 n))))))
                     (z (expt (acl2-pi) 2))))
    :pro (:forwardchain 1)
    (:change-goal nil t)
    :bash := (:dv 2)
    :s
    :top :bash)))

(local
 (defthm-std standard-pi^2/8
     (standardp (* 1/8 (expt (acl2-pi) 2)))))

(local
 (defthmd big-lower-bound
     (implies (posp n)
              (<= (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))
                  (/ (expt (acl2-pi) 2) 8)))
   :hints (("Goal"
            :use ((:instance big-lower-bound-lemma-specialized-3)
                  (:instance standard-part-<=
                             (x (basel-odds 1 (1+ (expt 2 (1- n)))))
                             (y (/ (expt (acl2-pi) 2) 8))))
            :in-theory (disable basel-odds
                                standard-part-<=)
            ))))

(local
 (defthmd big-upper-bound-lemma-1
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (expt (/ (* (acl2-pi)
                              (- (* 2 k) 1)
                              (/ (expt 2 (1+ n))))
                           (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n))))))
                        2)
                  (+ 1 (expt (* (acl2-pi)
                                (- (* 2 k) 1)
                                (/ (expt 2 (1+ n))))
                             2))))
   :hints (("Goal"
            :use ((:instance x-/-sin-x-<=-1+x^2
                             (x (* (acl2-pi)
                                   (- (* 2 k) 1)
                                   (/ (expt 2 (1+ n))))))
                  (:instance term-in-sum-<-pi/2)
                  )
            ))))

(local
 (defthmd big-upper-bound-lemma-2
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (expt (* (acl2-pi)
                              (- (* 2 k) 1)
                              (/ (expt 2 (1+ n))))
                           2)
                     (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))
                  (+ 1 (expt (* (acl2-pi)
                                (- (* 2 k) 1)
                                (/ (expt 2 (1+ n))))
                             2))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-1))
            ))))

(local
 (defthmd big-upper-bound-lemma-3
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))
                  (+ (/ (expt (* (acl2-pi)
                                 (- (* 2 k) 1)
                                 (/ (expt 2 (1+ n))))
                              2))
                     1)))
   :instructions
   ((:use (:instance big-upper-bound-lemma-2))
    (:use (:instance (:theorem (implies (and (realp x)
                                             (realp y)
                                             (realp z)
                                             (< 0 x))
                                        (equal (<= (* x y) (* x z)) (<= y z))))
                     (x (/ (expt (* (acl2-pi)
                                    (+ -1 (* 2 k))
                                    (/ (expt 2 (+ 1 n))))
                                 2)))
                     (y (/ (expt (* (acl2-pi)
                                    (+ -1 (* 2 k))
                                    (/ (expt 2 (+ 1 n))))
                                 2)
                           (expt (acl2-sine (* (acl2-pi)
                                               (+ -1 (* 2 k))
                                               (/ (expt 2 (+ 1 n)))))
                                 2)))
                     (z (+ 1
                           (expt (* (acl2-pi)
                                    (+ -1 (* 2 k))
                                    (/ (expt 2 (+ 1 n))))
                                 2)))))
    (:change-goal nil t)
    :bash :pro (:forwardchain 1)
    (:forwardchain 1)
    (:demote 4)
    (:dv 1)
    (:dv 1)
    (:dv 1)
    (:= (* (/ (expt (* (acl2-pi)
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    2)
              (expt (* (acl2-pi)
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    2))
           (/ (expt (acl2-sine (* (acl2-pi)
                                  (+ -1 (* 2 k))
                                  (/ (expt 2 (+ 1 n)))))
                    2))))
    (:dv 1)
    (:rewrite |(* a (/ a))|)
    (:dv 1)
    (:= nil)
    :up
    (:= (/ (expt (acl2-sine (* (acl2-pi)
                               (+ -1 (* 2 k))
                               (/ (expt 2 (+ 1 n)))))
                 2)))
    :up (:dive 1)
    (:rewrite |(* x (+ y z))|)
    (:dv 2)
    (:rewrite |(* y x)|)
    (:rewrite |(* a (/ a))|)
    (:dv 1)
    (:= nil)
    :up
    (:= (+ 1
           (/ (expt (* (acl2-pi)
                       (+ -1 (* 2 k))
                       (/ (expt 2 (+ 1 n))))
                    2))))
    :top :pro (:dv 2)
    (:rewrite |(+ y x)|)
    :top
    := :bash)))

(local
 (defthmd big-upper-bound-lemma-5
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))
                  (+ (/ (* 4 (expt (expt 2 n) 2))
                        (* (expt (acl2-pi) 2)
                           (expt (- (* 2 k) 1) 2)))
                     1)))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-3)
                  (:instance big-lower-bound-lemma-4))))))

(local
 (defthmd big-upper-bound-lemma-6
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (/ (expt (acl2-sine (* (acl2-pi)
                                         (- (* 2 k) 1)
                                         (/ (expt 2 (1+ n)))))
                           2))
                  (* (expt (expt 2 n) 2)
                     (+ (/ 4
                           (* (expt (acl2-pi) 2)
                              (expt (- (* 2 k) 1) 2)))
                        (/ (expt (expt 2 n) 2))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-5))))))

(local
 (defthmd big-upper-bound-lemma-7
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (* (/ (expt (expt 2 n) 2))
                     (/ (expt (acl2-sine (* (acl2-pi)
                                            (- (* 2 k) 1)
                                            (/ (expt 2 (1+ n)))))
                              2)))
                  (+ (/ 4
                        (* (expt (acl2-pi) 2)
                           (expt (- (* 2 k) 1) 2)))
                     (/ (expt (expt 2 n) 2)))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-6)
                  (:instance (:theorem
                              (implies (and (realp x) (realp y) (realp z)
                                            (< 0 x) (<= y z))
                                       (<= (* x y) (* x z))))
                             (x (/ (expt (expt 2 n) 2)))
                             (y (/ (expt (acl2-sine (* (acl2-pi)
                                                       (- (* 2 k) 1)
                                                       (/ (expt 2 (1+ n)))))
                                         2)))
                             (z (* (EXPT (EXPT 2 N) 2) (+ (/ 4
                                                             (* (expt (acl2-pi) 2)
                                                                (expt (- (* 2 k) 1) 2)))
                                                          (/ (expt (expt 2 n)
                                                                   2)))))))))))

(local
 (defun sum-terms (i n x)
   (declare (xargs :measure (nfix (- n i))))
   (if (zp (- n i))
       (if (= n i)
           x
           0)
       (+ x (sum-terms (1+ i) n x)))))

(local
 (defthmd sum-terms-closed-form
     (implies (and (natp i)
                   (natp n)
                   (<= i n)
                   (acl2-numberp x))
              (equal (sum-terms i n x)
                     (* x (1+ (- n i)))))))

(local
 (defthmd big-upper-bound-lemma
     (implies (and (posp n)
                   (posp k)
                   (<= k (expt 2 (1- n)))
                   )
              (<= (* (/ (expt (expt 2 n) 2))
                     (sine-series k (expt 2 (1- n)) n))
                  (+ (* (/ 4 (expt (acl2-pi) 2))
                        (basel-odds k (1+ (expt 2 (1- n)))))
                     (sum-terms k (expt 2 (1- n)) (/ (expt (expt 2 n) 2))))))
   :instructions ((:induct (sine-series k (expt 2 (1- n)) n))
                  (:change-goal nil t)
                  :bash
                  (:use (:instance big-upper-bound-lemma-7))
                  :pro (:forwardchain 1)
                  (:dv 2)
                  (:dv 1)
                  (:dv 2)
                  :x :up :nx (:= (/ (expt (expt 2 n) 2)))
                  :up :up (:dv 2)
                  (:dv 2)
                  (:= (/ (expt (acl2-sine (* (acl2-pi)
                                             (+ -1 (* 2 k))
                                             (/ (expt 2 (+ 1 n)))))
                               2)))
                  :top :bash :pro (:forwardchain 2)
                  (:dv 1)
                  (:dv 2)
                  :x-dumb
                  (:= (+ (/ (expt (acl2-sine (* (acl2-pi)
                                                (+ -1 (* 2 k))
                                                (/ (expt 2 (+ 1 n)))))
                                  2))
                         (sine-series (+ 1 k)
                                      (expt 2 (+ -1 n))
                                      n)))
                  :up (:rewrite |(* x (+ y z))|)
                  :top (:dv 2)
                  (:dv 1)
                  (:dv 2)
                  :x
                  (:= (+ (expt (+ -1 (* 2 k)) -2)
                         (basel-odds (+ 1 k)
                                     (+ 1 (expt 2 (+ -1 n))))))
                  :up (:rewrite |(* x (+ y z))|)
                  :nx :x
                  (:= (+ (expt 4 (- n))
                         (sum-terms (+ 1 k)
                                    (expt 2 (+ -1 n))
                                    (expt 4 (- n)))))
                  :up (:in-theory (disable basel-odds))
                  (:in-theory (disable sum-terms))
                  :s :top (:dv 2)
                  (:= (+ (+ (expt 4 (- n))
                            (* 4 (expt (acl2-pi) -2)
                               (expt (+ -1 (* 2 k)) -2)))
                         (+ (* 4 (expt (acl2-pi) -2)
                               (basel-odds (+ 1 k)
                                           (+ 1 (expt 2 (+ -1 n)))))
                            (sum-terms (+ 1 k)
                                       (expt 2 (+ -1 n))
                                       (expt 4 (- n))))))
                  :top (:contrapose 5)
                  (:dv 1)
                  (:dv 1)
                  (:= (* 4 (expt (acl2-pi) -2)
                         (basel-odds (+ 1 k)
                                     (+ 1 (expt 2 (+ -1 n))))))
                  :nx (:dv 3)
                  :s :top (:contrapose 5)
                  (:use big-upper-bound-lemma-7)
                  :pro (:forwardchain 1)
                  (:contrapose 6)
                  (:dv 1)
                  (:= (+ (expt 4 (- n))
                         (* 4 (expt (acl2-pi) -2)
                            (expt (+ -1 (* 2 k)) -2))))
                  :top (:contrapose 6)
                  :bash)))

(local
 (defthmd big-upper-bound-lemma-specialized-1
     (implies (posp n)
              (<= (* (/ (expt (expt 2 n) 2))
                     (expt 2 (- (* 2 n) 1)))
                  (+ (* (/ 4 (expt (acl2-pi) 2))
                        (basel-odds 1 (1+ (expt 2 (1- n)))))
                     (sum-terms 1 (expt 2 (1- n)) (/ (expt (expt 2 n) 2))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma (k 1))
                  (:instance sine-series-closed-form))
            :in-theory (disable sine-series
                                basel-odds)
            ))))

(local
 (defthmd big-upper-bound-lemma-specialized-2
     (implies (posp n)
              (<= (* (/ (expt (expt 2 n) 2))
                     (expt 2 (- (* 2 n) 1)))
                  (+ (* (/ 4 (expt (acl2-pi) 2))
                        (basel-odds 1 (1+ (expt 2 (1- n)))))
                     (/ (expt 2 (1+ n))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-1)
                  (:instance sum-terms-closed-form
                             (i 1)
                             (n (expt 2 (1- n)))
                             (x (/ (expt (expt 2 n) 2)))))
            :in-theory (disable basel-odds)
            ))))

(local
 (defthmd big-upper-bound-lemma-specialized-3
     (implies (posp n)
              (<= 1/2
                  (+ (* (/ 4 (expt (acl2-pi) 2))
                        (basel-odds 1 (1+ (expt 2 (1- n)))))
                     (/ (expt 2 (1+ n))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-2))
            :in-theory (disable basel-odds)
            ))))

(local
 (defthmd big-upper-bound-lemma-specialized-4
     (implies (posp n)
              (<= (- 1/2 (/ (expt 2 (1+ n))))
                  (* (/ 4 (expt (acl2-pi) 2))
                     (basel-odds 1 (1+ (expt 2 (1- n)))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-3))
            :in-theory (disable basel-odds)
            ))))

(local
 (defthmd big-upper-bound-lemma-specialized-5
     (implies (posp n)
              (<= (* (/ (expt (acl2-pi) 2) 4)
                     (- 1/2 (/ (expt 2 (1+ n)))))
                  (basel-odds 1 (1+ (expt 2 (1- n))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-4)
                  (:instance
                   (:theorem (implies (and (realp x)
                                           (realp y)
                                           (realp z)
                                           (< 0 x))
                                      (equal (<= (* x y) (* x z))
                                             (<= y z))))
                   (x (/ (expt (acl2-pi) 2) 4))
                   (y (- 1/2 (/ (expt 2 (1+ n)))))
                   (z (* (/ 4 (expt (acl2-pi) 2))
                         (basel-odds 1 (1+ (expt 2 (1- n))))))))
            :in-theory (disable basel-odds)
            ))))

(local
 (defthmd big-upper-bound-lemma-specialized-6
     (implies (posp n)
              (<= (- (* 1/2 (/ (expt (acl2-pi) 2) 4))
                     (* (/ (expt (acl2-pi) 2) 4)
                        (/ (expt 2 (1+ n)))))
                  (basel-odds 1 (1+ (expt 2 (1- n))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-5))
            :in-theory (disable basel-odds)
            ))))

(local
 (defthmd big-upper-bound
     (implies (posp n)
              (<= (- (/ (expt (acl2-pi) 2) 8)
                     (standard-part (* (/ (expt (acl2-pi) 2) 4)
                                       (/ (expt 2 (1+ n))))))
                  (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound-lemma-specialized-6)
                  (:instance standard-part-<=
                             (x (- (* 1/2 (/ (expt (acl2-pi) 2) 4))
                                   (* (/ (expt (acl2-pi) 2) 4)
                                      (/ (expt 2 (1+ n))))))
                             (y (basel-odds 1 (1+ (expt 2 (1- n)))))))))))

(local
 (defthmd n-<-expt-2-n
     (implies (natp n)
              (<= n (expt 2 n)))
   :instructions ((:in-theory (enable expt))
                  (:induct (expt 2 n))
                  :bash
                  :pro (:casesplit (not (natp (+ n -1))))
                  (:claim (= n 0))
                  :s (:forwardchain 4)
                  (:dv 2)
                  :x (:= (* 2 (expt 2 (+ n -1))))
                  (:claim (<= n (+ 1 (expt 2 (+ n -1)))))
                  (:claim (<= 1 (expt 2 (+ n -1))))
                  (:= (+ (expt 2 (+ n -1)) (expt 2 (+ n -1))))
                  (:claim (natp (expt 2 (+ n -1))))
                  :top
                  (:generalize ((expt 2 (+ n -1)) |2^n-1|))
                  :bash
                  :bash :bash)
   ))

(local
 (defthmd large-expt-2-n
     (implies (and (natp n)
                   (i-large n))
              (i-large (expt 2 n)))
   :hints (("Goal"
            :use ((:instance n-<-expt-2-n)
                  (:instance large-if->-large
                             (x n)
                             (y (expt 2 x))))))))
(local
 (defthmd large-+-1
     (implies (and (acl2-numberp x)
                   (i-large x))
              (i-large (+ x 1)))
   :hints (("Goal"
            :use ((:instance i-limited-plus
                             (x (+ x 1))
                             (y -1)))))))

(local
 (defthmd large---1
     (implies (and (acl2-numberp x)
                   (i-large x))
              (i-large (- x 1)))
   :hints (("Goal"
            :use ((:instance i-limited-plus
                             (x x)
                             (y -1)))))))

(local
 (defthmd large-1+expt-2-n
     (implies (and (natp n)
                   (i-large n))
              (i-large (1+ (expt 2 n))))
   :hints (("Goal"
            :use ((:instance large-+-1
                             (x (expt 2 n)))
                  (:instance large-expt-2-n))))))

(local
 (defthmd large-expt-2-n+1
     (implies (and (natp n)
                   (i-large n))
              (i-large (expt 2 (1+ n))))
   :hints (("Goal"
            :use ((:instance n-<-expt-2-n (n (1+ n)))
                  (:instance large-+-1 (x n)))))))

(local
 (defthmd large-1+expt-2-n-1
     (implies (and (natp n)
                   (i-large n))
              (i-large (1+ (expt 2 (+ -1 n)))))
   :hints (("Goal"
            :use ((:instance large-+-1
                             (x (expt 2 (+ -1 n))))
                  (:instance large-expt-2-n
                             (n (+ -1 n)))
                  (:instance large---1
                             (x n)))
            ))))

(local
 (defthmd small-/-expt-2-n+1
     (implies (and (natp n)
                   (i-large n))
              (i-small (/ (expt 2 (1+ n)))))
   :hints (("Goal"
            :use ((:instance large-expt-2-n+1))
            :in-theory (enable i-large)))))

(local
 (defthm-std standard-pi^2/4
     (standardp (* 1/4 (expt (acl2-pi) 2)))))

(local
 (defthmd small-x-/-expt-2-n+1
     (implies (and (natp n)
                   (i-large n))
              (i-small (* (/ (expt (acl2-pi) 2) 4)
                          (/ (expt 2 (1+ n))))))
   :hints (("Goal"
            :use ((:instance limited*small->small
                             (x (/ (expt (acl2-pi) 2) 4))
                             (y (/ (expt 2 (1+ n)))))
                  (:instance STANDARDS-ARE-LIMITED
                             (x (* 1/4 (expt (acl2-pi) 2))))
                  (:instance small-/-expt-2-n+1)
                  )))))

(local
 (defthmd standard-part-x-/-expt-2-n+1
     (implies (and (natp n)
                   (i-large n))
              (equal (standard-part (* (/ (expt (acl2-pi) 2) 4)
                                       (/ (expt 2 (1+ n)))))
                     0))
   :hints (("Goal"
            :use ((:instance small-x-/-expt-2-n+1))
            :in-theory (enable i-small)
            ))))

(local
 (defthmd big-upper-bound-large-n
     (implies (and (posp n)
                   (i-large n))
              (<= (/ (expt (acl2-pi) 2) 8)
                  (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))))
   :hints (("Goal"
            :use ((:instance big-upper-bound)
                  (:instance standard-part-x-/-expt-2-n+1))
            :in-theory (disable basel-odds)))))

(local
 (defthmd basel-odds-closed-form
     (implies (and (posp n)
                   (i-large n))
              (equal (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))
                     (/ (expt (acl2-pi) 2) 8)))
   :hints (("Goal"
            :use ((:instance big-lower-bound)
                  (:instance big-upper-bound-large-n))))))

(local
 (defthmd basel-series-split-evens-odds
     (implies (and (natp i)
                   (natp n))
              (equal (+ (basel-odds i n)
                        (basel-evens i n))
                     (basel-series (1- (* 2 i)) (1- (* 2 n)))))
   :hints (("Goal"
            :induct (basel-odds i n)
            :in-theory (enable basel-series)
            ))))

(local
 (defthmd reduce-basel-evens
     (implies (and (natp i)
                   (natp n))
              (equal (basel-evens i n)
                     (* 1/4 (basel-series i n))))
   :hints (("Goal"
            :induct (basel-evens i n)
            :in-theory (enable basel-series)
            ))))


(local
 (defthmd basel-series-split-just-odds
     (implies (and (natp i)
                   (natp n))
              (equal (+ (basel-odds i n)
                        (* 1/4 (basel-series i n)))
                     (basel-series (1- (* 2 i)) (1- (* 2 n)))))
   :hints (("Goal"
            :use ((:instance basel-series-split-evens-odds)
                  (:instance reduce-basel-evens))
            ))))

(local
 (defthmd basel-series-split-just-odds-complete
     (implies (natp n)
              (equal (+ (basel-odds 1 n)
                        (* 1/4 (basel-series 1 n)))
                     (basel-series 1 (1- (* 2 n)))))
   :hints (("Goal"
            :use ((:instance basel-series-split-just-odds (i 1)))
            ))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete
     (implies (natp n)
              (equal (+ (standard-part (basel-odds 1 n))
                        (standard-part (* 1/4 (basel-series 1 n))))
                     (standard-part (basel-series 1 (1- (* 2 n))))))
   :hints (("Goal"
            :use ((:instance basel-series-split-just-odds (i 1)))
            ))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete-1
     (implies (posp n)
              (equal (+ (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))
                        (standard-part (* 1/4 (basel-series 1 (1+ (expt 2 (1- n)))))))
                     (standard-part (basel-series 1 (1- (* 2 (1+ (expt 2 (1- n)))))))))
   :hints (("Goal"
            :use ((:instance
                   standard-part-basel-series-split-just-odds-complete
                   (n (1+ (expt 2 (1- n))))))
            ))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete-2
     (implies (posp n)
              (equal (+ (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))
                        (* 1/4 (standard-part (basel-series 1 (1+ (expt 2 (1- n)))))))
                     (standard-part (basel-series 1 (1- (* 2 (1+ (expt 2 (1- n)))))))))
   :hints (("Goal"
            :use ((:instance standard-part-basel-series-split-just-odds-complete-1)
                  (:instance standard-part-of-times
                             (x 1/4)
                             (y (basel-series 1 (1+ (expt 2 (1- n))))))
                  (:instance limited-basel-series
                             (i 1)
                             (n (1+ (expt 2 (1- n))))))
            :in-theory (disable standard-part-of-times
                                standard-part-of-plus
                                basel-odds
                                basel-series)
            ))))

(local
 (defthmd basel-series-terms-close-for-large-m-n-specialized
     (implies (and (posp n)
                   (i-large n)
                   (posp m)
                   (i-large m))
              (i-close (basel-series 1 m)
                       (basel-series 1 n)))
   :hints (("Goal"
            :use ((:instance basel-series-close-for-large-values
                             (i 1)))))))

(local
 (defthmd basel-series-terms-same-standard-part-for-large-m-n
     (implies (and (posp n)
                   (i-large n)
                   (posp m)
                   (i-large m))
              (equal (standard-part (basel-series 1 m))
                     (standard-part (basel-series 1 n))))
   :hints (("Goal"
            :use ((:instance basel-series-terms-close-for-large-m-n-specialized)
                  (:instance limited-basel-series
                             (i 1)
                             (n m))
                  (:instance close-x-y->same-standard-part
                             (x (basel-series 1 m))
                             (y (basel-series 1 n))))))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete-3
     (implies (and (posp n)
                   (i-large n))
              (equal (+ (standard-part (basel-odds 1 (1+ (expt 2 (1- n)))))
                        (* 1/4 (standard-part (basel-series 1 (1+ (expt 2 (1- n)))))))
                     (standard-part (basel-series 1 (1+ (expt 2 (1- n)))))))
   :otf-flg t
   :hints (("Goal"
            :use ((:instance standard-part-basel-series-split-just-odds-complete-2)
                  (:instance basel-series-terms-same-standard-part-for-large-m-n
                             (m (1+ (expt 2 (1- n))))
                             (n (1- (* 2 (1+ (expt 2 (1- n)))))))
                  (:instance large-1+expt-2-n)
                  (:instance large-1+expt-2-n-1)
                  )
            :in-theory (disable standard-part-of-times
                                standard-part-of-plus
                                basel-odds
                                basel-series)
            ))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete-4
     (implies (and (posp n)
                   (i-large n))
              (equal (standard-part (basel-series 1 (1+ (expt 2 (1- n)))))
                     (* 4/3 (standard-part (basel-odds 1 (1+ (expt 2 (1- n))))))))
   :hints (("Goal"
            :use ((:instance
                   standard-part-basel-series-split-just-odds-complete-3))))))

(local
 (defthmd standard-part-basel-series-split-just-odds-complete-5
     (implies (and (posp n)
                   (i-large n))
              (equal (standard-part (basel-series 1 (1+ (expt 2 (1- n)))))
                     (/ (expt (acl2-pi) 2) 6)))
   :hints (("Goal"
            :use ((:instance basel-odds-closed-form)
                  (:instance standard-part-basel-series-split-just-odds-complete-4))))))

(defthmd basel-series-closed-form
    (implies (and (posp n)
                  (i-large n))
             (equal (standard-part (basel-series 1 n))
                    (/ (expt (acl2-pi) 2) 6)))
  :hints (("Goal"
           :use ((:instance standard-part-basel-series-split-just-odds-complete-5)
                 (:instance basel-series-terms-same-standard-part-for-large-m-n
                            (m (1+ (expt 2 (1- n))))
                            (n n))
                 (:instance large-1+expt-2-n-1)
                 ))))

(local
 (defthm-std standard-pi^2/6
     (standardp (* 1/6 (expt (acl2-pi) 2)))))

(defthmd basel-series-closed-form-close
    (implies (and (posp n)
                  (i-large n))
             (i-close (basel-series 1 n)
                      (/ (expt (acl2-pi) 2) 6)))
  :hints (("Goal"
           :use ((:instance basel-series-closed-form)
                 (:instance
                  standard-part-is-standard-implies-close-to-standard-part
                  (x (basel-series 1 n))
                  (stdx (/ (expt (acl2-pi) 2) 6))
                  )
                 ))))
