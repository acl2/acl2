(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "nonstd/nsa/nsa" :dir :system))
(local (include-book "nonstd/nsa/exp-sum" :dir :system))
(local (include-book "nonstd/nsa/ln-product" :dir :system))
(local (include-book "nonstd/nsa/raise" :dir :system))

(include-book "ln-trapezoidal")
(local (include-book "standard-close-utils"))
(local (include-book "basel-bound"))
(local (include-book "wallis-product"))

(local
 (defun wallis-product-numerator (n)
   (if (zp n)
       1
       (* (expt (* 2 n) 2)
          (wallis-product-numerator (1- n))))))

(local
 (defun wallis-product-denominator-aux (N)
   (if (zp n)
       1
       (* (expt (1- (* 2 n)) 2)
          (wallis-product-denominator-aux (1- n))))))

(local
 (defun wallis-product-denominator (n)
   (* (wallis-product-denominator-aux n)
      (1+ (* 2 n)))))

(local
 (defthmd wallis-product-as-fraction
     (implies (natp n)
              (equal (wallis-product n)
                     (/ (wallis-product-numerator n)
                        (wallis-product-denominator n))))))

(local
 (defthmd wallis-numerator-as-factorial
     (implies (natp n)
              (equal (wallis-product-numerator n)
                     (* (expt 4 n)
                        (expt (factorial n) 2))))
   :instructions (:induct (:change-goal nil t)
                         :bash :pro (:forwardchain 2)
                         (:dv 1)
                         :x (:dv 3)
                         := :top (:drop 3)
                         (:dv 2)
                         (:dv 1)
                         (:= (* 4 (expt 4 (1- n))))
                         :nx (:dv 1)
                         :x
                         :up (:rewrite |(expt (* x y) n)|)
                         :top :s)))

(local
 (defun !! (n)
   (if (zp n)
       1
       (if (= n 1)
           1
           (* n (!! (- n 2)))))))

(local
 (defthmd !!-as-factorial-odd-case
     (implies (natp n)
              (equal (!! (1+ (* 2 n)))
                     (/ (factorial (1+ (* 2 n)))
                        (* (expt 2 n)
                           (factorial n)))))
  :instructions ((:induct (wallis-product-numerator n))
                 (:change-goal nil t)
                 :bash :pro (:forwardchain 2)
                 (:dv 1)
                 :x-dumb
                 (:= (* (+ 1 (* 2 n))
                        (!! (+ 1 (* 2 (+ -1 n))))))
                 (:dv 2)
                 := :top (:dv 2)
                 (:dv 1)
                 :x-dumb
                 (:= (* (+ 1 (* 2 n)) (factorial (* 2 n))))
                 :nx (:dv 1)
                 (:dv 1)
                 (:= (* 2 (expt 2 (1- n))))
                 :nx
                 :x-dumb (:= (* n (factorial (1- n))))
                 :top (:dv 2)
                 (:dv 1)
                 (:dv 2)
                 :x-dumb (:= (* (* 2 n) (factorial (1- (* 2 n)))))
                 :top :bash)
  ))

(local
 (defthmd wallis-denominator-aux-as-!!
     (implies (natp n)
              (equal (wallis-product-denominator-aux n)
                     (* (!! (1- (* 2 n)))
                        (!! (1- (* 2 n))))))
   ))

(local
 (defthmd wallis-denominator-as-!!
     (implies (natp n)
              (equal (wallis-product-denominator n)
                     (* (!! (1- (* 2 n)))
                        (!! (1+ (* 2 n))))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance wallis-product-denominator)
                  (:instance wallis-denominator-aux-as-!!)
                  (:instance !! (n (1+ (* 2 n))))))))
 )

(local
 (defun scaled-wallis-numerator (n)
   (/ (* (expt 4 n) (expt (factorial n) 2))
      (expt (* (expt n n)
               (/ (acl2-exp n))
               (acl2-sqrt n))
            4))))

(local
 (defthmd scaled-wallis-numerator-as-stirling-constant
     (implies (and (natp n)
                   (< 1 n))
              (equal (scaled-wallis-numerator n)
                     (* (expt 4 n)
                        (expt (stirling-constant-n n) 4)
                        (/ (expt (factorial n) 2)))))
   :instructions ((:use (:instance factorial-as-stirling-term))
                  :pro (:forwardchain 1)
                  (:dv 2)
                  (:dv 2)
                  (:dv 1)
                  := (:drop 3)
                  :top (:dv 1)
                  :x
                  :top :bash)))

(local
 (defun scaled-wallis-denominator (n)
   (/ (* (!! (1- (* 2 n)))
         (!! (1+ (* 2 n))))
      (expt (* (expt n n)
               (/ (acl2-exp n))
               (acl2-sqrt n))
            4))))

(local
 (defthm scaled-wallis-simplify
     (implies (posp n)
              (equal (/ (scaled-wallis-numerator n)
                        (scaled-wallis-denominator n))
                     (wallis-product n)))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance wallis-product-as-fraction)
                  (:instance wallis-numerator-as-factorial)
                  (:instance wallis-denominator-as-!!)
                  (:instance
                   (:theorem
                    (implies (and (acl2-numberp x)
                                  (acl2-numberp y)
                                  (acl2-numberp z)
                                  (not (= z 0)))
                             (equal (/ (/ x z)
                                       (/ y z))
                                    (/ x y))))
                   (x (* (expt 4 n) (expt (factorial n) 2)))
                   (y (* (!! (1- (* 2 n)))
                         (!! (1+ (* 2 n)))))
                   (z (expt (* (expt n n)
                               (/ (acl2-exp n))
                               (acl2-sqrt n))
                            4))))
            ))))

(local
 (encapsulate nil

     (local
      (defthmd lemma-1
          (implies (posp n)
                   (equal (!! (1- (* 2 n)))
                          (/ (factorial (1- (* 2 n)))
                             (* (expt 2 (1- n))
                                (factorial (1- n))))))
        :hints (("Goal"
                 :use ((:instance !!-as-factorial-odd-case
                                  (n (1- n))))))))

   (local
    (defthmd lemma-2
        (implies (posp n)
                 (equal (* (!! (1- (* 2 n)))
                           (!! (1+ (* 2 n))))
                        (* (/ (factorial (1- (* 2 n)))
                              (* (expt 2 (1- n))
                                 (factorial (1- n))))
                           (/ (factorial (1+ (* 2 n)))
                              (* (expt 2 n)
                                 (factorial n))))))
      :hints (("Goal"
               :use ((:instance lemma-1)
                     (:instance !!-as-factorial-odd-case))))))

   (defthmd scaled-wallis-denominator-simplify-1
       (implies (posp n)
                (equal (scaled-wallis-denominator n)
                       (/ (* (/ (factorial (1- (* 2 n)))
                                (* (expt 2 (1- n))
                                   (factorial (1- n))))
                             (/ (factorial (1+ (* 2 n)))
                                (* (expt 2 n)
                                   (factorial n))))
                          (expt (* (expt n n)
                                   (/ (acl2-exp n))
                                   (acl2-sqrt n))
                                4))))
     :hints (("Goal"
              :use ((:instance lemma-2)))))
   ))

 (local
  (encapsulate nil

      (local
       (defthmd lemma-1
           (implies (posp n)
                    (equal (* (/ (factorial (1- (* 2 n)))
                                 (* (expt 2 (1- n))
                                    (factorial (1- n))))
                              (/ (factorial (1+ (* 2 n)))
                                 (* (expt 2 n)
                                    (factorial n))))
                           (/ (* (factorial (1- (* 2 n))) (factorial (1+ (* 2 n))))
                              (* (expt 2 (1- n))
                                 (expt 2 n)
                                 (factorial (1- n))
                                 (factorial n)))))))

    (local
     (defthmd lemma-2
         (implies (posp n)
                  (equal (factorial (1- (* 2 n)))
                         (* (factorial (* 2 n))
                            (/ (* 2 n)))))
       :hints (("Goal"
                :expand ((factorial (* 2 n)))))))

    (local
     (defthmd lemma-3
         (implies (posp n)
                  (equal (factorial (1+ (* 2 n)))
                         (* (factorial (* 2 n))
                            (1+ (* 2 n)))))
       :hints (("Goal"
                :expand ((factorial (1+ (* 2 n))))))))

    (defthmd scaled-wallis-denominator-simplify-2
        (implies (posp n)
                 (equal (scaled-wallis-denominator n)
                        (/ (/ (* (expt (factorial (* 2 n)) 2)
                                 (1+ (* 2 n))
                                 (/ (* 2 n)))
                              (* (expt 2 (1- n))
                                 (expt 2 n)
                                 (factorial (1- n))
                                 (factorial n)))
                           (expt (* (expt n n)
                                    (/ (acl2-exp n))
                                    (acl2-sqrt n))
                                 4))))
      :hints (("Goal"
               :use ((:instance scaled-wallis-denominator-simplify-1)
                     (:instance lemma-1)
                     (:instance lemma-2)
                     (:instance lemma-3)
                     ))))

    ))

 (local
  (defthmd scaled-wallis-denominator-simplify-3
      (implies (posp n)
               (equal (scaled-wallis-denominator n)
                      (/ (* (expt (factorial (* 2 n)) 2)
                            (1+ (* 2 n))
                            (/ (* 2 n)))
                         (* (expt 2 (1- (* 2 n)))
                            (factorial (1- n))
                            (factorial n)
                            (expt (* (expt n n)
                                     (/ (acl2-exp n))
                                     (acl2-sqrt n))
                                  4)))))
    :hints (("Goal"
             :use ((:instance scaled-wallis-denominator-simplify-2)
                   )))))

 (local
  (defthmd scaled-wallis-denominator-simplify-4
      (implies (posp n)
               (equal (scaled-wallis-denominator n)
                      (/ (* (expt (factorial (* 2 n)) 2)
                            2
                            (1+ (* 2 n))
                            (/ (* 2 n)))
                         (* (expt 2 (* 2 n))
                            (factorial (1- n))
                            (factorial n)
                            (expt (* (expt n n)
                                     (/ (acl2-exp n))
                                     (acl2-sqrt n))
                                  4)))))
    :hints (("Goal"
             :use ((:instance scaled-wallis-denominator-simplify-3)
                   )))))

 (local
  (encapsulate nil

      (local
       (defthmd lemma-1
           (implies (posp n)
                    (equal (expt (* (expt n n)
                                    (/ (acl2-exp n))
                                    (acl2-sqrt n))
                                 4)
                           (expt (expt (* (expt n n)
                                          (/ (acl2-exp n))
                                          (acl2-sqrt n))
                                       2)
                                 2)))
         ))

    (local
     (defthmd lemma-2
         (implies (posp n)
                  (equal (expt (* (expt n n)
                                  (/ (acl2-exp n))
                                  (acl2-sqrt n))
                               2)
                         (* (expt n (* 2 n))
                            (/ (acl2-exp (* 2 n)))
                            (acl2-sqrt n)
                            (acl2-sqrt n))))
       :instructions (:pro (:dv 1)
                           :s (:dv 1)
                           (:in-theory (disable sqrt-sqrt))
                           (:= (* (acl2-sqrt n) (acl2-sqrt n)))
                           :nx :x :x :x-dumb
                           (:= (* (/ (acl2-exp n))
                                  (expt (acl2-exp n) -1)))
                           (:dv 2)
                           (:= (/ (acl2-exp n)))
                           :up
                           (:= (/ (* (acl2-exp n) (acl2-exp n))))
                           (:dv 1)
                           :top
                           (:use (:instance exp-sum (x n) (y n)))
                           :pro (:forwardchain 1)
                           (:dv 1)
                           (:dv 2)
                           (:dv 1)
                           := (:drop 2)
                           (:= (acl2-exp (* 2 n)))
                           :top :s)
       ))

    (local
     (defthmd lemma-3
         (implies (posp n)
                  (equal (expt (* (expt n n)
                                  (/ (acl2-exp n))
                                  (acl2-sqrt n))
                               2)
                         (* (expt n (* 2 n))
                            (/ (acl2-exp (* 2 n)))
                            (acl2-sqrt (* 2 n))
                            (acl2-sqrt (/ n 2)))))
       :hints (("Goal"
                :use ((:instance lemma-2))))))

    (local
     (defthmd lemma-4
         (implies (posp n)
                  (equal (expt (* (expt n n)
                                  (/ (acl2-exp n))
                                  (acl2-sqrt n))
                               2)
                         (* (expt 2 (- (* 2 n)))
                            (expt (* 2 n) (* 2 n))
                            (/ (acl2-exp (* 2 n)))
                            (acl2-sqrt (* 2 n))
                            (acl2-sqrt (/ n 2)))))
       :hints (("Goal"
                :use ((:instance lemma-3))))))

    (local
     (defthmd lemma-5
         (implies (posp n)
                  (equal (expt (* (expt n n)
                                  (/ (acl2-exp n))
                                  (acl2-sqrt n))
                               4)
                         (* (expt 2 (- (* 4 n)))
                            (/ n 2)
                            (expt (* (expt (* 2 n) (* 2 n))
                                     (/ (acl2-exp (* 2 n)))
                                     (acl2-sqrt (* 2 n)))
                                  2))))
       :instructions ((:use (:instance lemma-1))
                      (:use (:instance lemma-4))
                      :pro (:forwardchain 1)
                      (:forwardchain 1)
                      (:dv 1)
                      := (:drop 3)
                      (:dv 1)
                      := (:drop 2)
                      :up (:rewrite |(expt (* x y) n)|)
                      (:dv 1)
                      (:rewrite |(expt (expt x m) n)|)
                      (:dv 2)
                      (:= (- (* 4 n)))
                      :up :nx (:dv 1)
                      (:casesplit (implies (and (integerp n) (< 0 n))
                                           (equal (expt (acl2-sqrt n) 2) n)))
                      (:forwardchain 2)
                      (:= (* (acl2-sqrt (* n 1/2))
                             (expt (* 2 n) (* 2 n))
                             (/ (acl2-exp (* 2 n)))
                             (acl2-sqrt (* 2 n))))
                      (:change-goal nil t)
                      :top (:contrapose 2)
                      :pro (:dv 1)
                      :x :top
                      :s :up (:rewrite |(expt (* x y) n)|)
                      :up (:dv 2)
                      (:= (* (acl2-sqrt (* n 1/2))
                             (acl2-sqrt (* n 1/2))))
                      (:rewrite sqrt-sqrt)
                      :top :s)))

    (defthmd scaled-wallis-denominator-simplify-5
        (implies (posp n)
                 (equal (scaled-wallis-denominator n)
                        (/ (* (expt (factorial (* 2 n)) 2)
                              2
                              (1+ (* 2 n))
                              (/ (* 2 n)))
                           (* (expt 2 (* 2 n))
                              (factorial (1- n))
                              (factorial n)
                              (expt 2 (- (* 4 n)))
                              (/ n 2)
                              (expt (* (expt (* 2 n) (* 2 n))
                                       (/ (acl2-exp (* 2 n)))
                                       (acl2-sqrt (* 2 n)))
                                    2)))))
      :instructions ((:use (:instance scaled-wallis-denominator-simplify-4))
                     (:use (:instance lemma-5))
                     :pro (:forwardchain 1)
                     (:forwardchain 1)
                     (:dv 1)
                     := (:drop 3)
                     (:dv 2)
                     (:dv 1)
                     (:dv 4)
                     := (:drop 2)
                     :top :s))
    ))

(local
 (defthmd scaled-wallis-denominator-simplify-6
      (implies (posp n)
               (equal (scaled-wallis-denominator n)
                      (/ (* (expt 4  n)
                            (expt (factorial (* 2 n)) 2)
                            2
                            (1+ (* 2 n))
                            (/ (* 2 n)))
                         (* (factorial (1- n))
                            (factorial n)
                            (/ n 2)
                            (expt (* (expt (* 2 n) (* 2 n))
                                     (/ (acl2-exp (* 2 n)))
                                     (acl2-sqrt (* 2 n)))
                                  2)))))
    :hints (("Goal"
             :use ((:instance scaled-wallis-denominator-simplify-5))))))

(local
 (defthmd scaled-wallis-denominator-simplify-7
     (implies (posp n)
              (equal (scaled-wallis-denominator n)
                     (/ (* (expt 4  n)
                           (expt (factorial (* 2 n)) 2)
                           4
                           (1+ (* 2 n))
                           (/ (* 2 n)))
                        (* (expt (factorial n) 2)
                           (expt (* (expt (* 2 n) (* 2 n))
                                    (/ (acl2-exp (* 2 n)))
                                    (acl2-sqrt (* 2 n)))
                                 2)))))
   :instructions ((:use (:instance scaled-wallis-denominator-simplify-6))
                  :pro (:forwardchain 1)
                  (:dv 1)
                  := (:drop 2)
                  (:dv 2)
                  (:dv 1)
                  (:dv 3)
                  (:= (* 1/2 n))
                  :up :up :up
                  (:= (* n (factorial (+ -1 n))
                         (factorial n)
                         1/2
                         (expt (* (expt (* 2 n) (* 2 n))
                                  (/ (acl2-exp (* 2 n)))
                                  (acl2-sqrt (* 2 n)))
                               2)))
                  (:casesplit (implies (natp n)
                                       (= (* n (factorial (1- n)))
                                          (factorial n))))
                  (:forwardchain 2)
                  (:= (* (factorial n)
                         (factorial n)
                         1/2
                         (expt (* (expt (* 2 n) (* 2 n))
                                  (/ (acl2-exp (* 2 n)))
                                  (acl2-sqrt (* 2 n)))
                               2)))
                  (:= (* 1/2 (expt (factorial n) 2)
                         (expt (* (expt (* 2 n) (* 2 n))
                                  (/ (acl2-exp (* 2 n)))
                                  (acl2-sqrt (* 2 n)))
                               2)))
                  :top :bash :top (:contrapose 2)
                  :pro (:dv 2)
                  :x
                  :top :s)))

(local
 (defthmd scaled-wallis-denominator-simplify-8
     (implies (posp n)
              (equal (scaled-wallis-denominator n)
                     (* (expt 4  n)
                        (expt (/ (factorial (* 2 n))
                                 (* (expt (* 2 n) (* 2 n))
                                    (/ (acl2-exp (* 2 n)))
                                    (acl2-sqrt (* 2 n))))
                              2)
                        4
                        (1+ (* 2 n))
                        (/ (* 2 n))
                        (/ (expt (factorial n) 2)))))
   :hints (("Goal"
            :use ((:instance scaled-wallis-denominator-simplify-7))))))


(local
 (defthmd scaled-wallis-denominator-as-stirling-constant
     (implies (and (integerp n)
                   (< 1 n))
              (equal (scaled-wallis-denominator n)
                     (* (expt 4  n)
                        (expt (stirling-constant-n (* 2 n)) 2)
                        4
                        (1+ (* 2 n))
                        (/ (* 2 n))
                        (/ (expt (factorial n) 2)))))
   :instructions ((:use (:instance scaled-wallis-denominator-simplify-8))
                  (:use (:instance factorial-as-stirling-term (n (* 2 n))))
                  :pro (:forwardchain 1)
                  (:forwardchain 1)
                  (:dv 1)
                  := :nx (:dv 2)
                  (:dv 1)
                  := (:drop 3)
                  :top :bash)))

(local
 (defthmd wallis-quotient-as-stirling-constant
     (implies (and (integerp n)
                   (< 1 n))
              (equal (/ (scaled-wallis-numerator n)
                        (scaled-wallis-denominator n))
                     (/ (expt (stirling-constant-n n) 4)
                        (* (expt (stirling-constant-n (* 2 n)) 2)
                           4
                           (1+ (* 2 n))
                           (/ (* 2 n))))))
   :instructions
  ((:use (:instance scaled-wallis-numerator-as-stirling-constant))
   (:use (:instance scaled-wallis-denominator-as-stirling-constant))
   :pro (:forwardchain 1)
   (:forwardchain 1)
   (:dv 1)
   (:dv 1)
   := (:drop 4)
   :nx (:dv 1)
   := (:drop 3)
   (:claim (and (realp (expt 4 n))
                (< 0 (expt 4 n))))
   :top (:generalize ((expt 4 n) expt-4-n))
   (:claim (and (realp (stirling-constant-n n))
                (< 0 (stirling-constant-n n))))
   (:generalize ((stirling-constant-n n) stir_n))
   (:claim (and (realp (expt stir_n 4))
                (< 0 (expt stir_n 4))))
   (:generalize ((expt stir_n 4) expt-stir-4))
   (:claim (and (realp (stirling-constant-n (* 2 n)))
                (< 0 (stirling-constant-n (* 2 n)))))
   (:generalize ((stirling-constant-n (* 2 n)) stir_2n))
   (:claim (and (realp (expt (factorial n) 2))
                (< 0 (expt (factorial n) 2))))
   (:generalize ((expt (factorial n) 2) expt-fac))
   (:claim (and (realp (expt stir_2n 2))
                (< 0 (expt stir_2n 2))))
   (:generalize ((expt stir_2n 2) expt_stir_2n))
   (:claim (and (realp (+ 1 (* 2 n)))
                (< 0 (+ 1 (* 2 n)))))
   (:generalize ((+ 1 (* 2 n)) |2n+1|))
   (:claim (and (realp (* 2 n)) (< 0 (* 2 n))))
   (:generalize ((* 2 n) |2n|))
   :s)))

(encapsulate nil

    (local
     (defthmd lemma-1
         (implies (posp n)
                  (equal (/ (expt (stirling-constant-n n) 4)
                            (* (expt (stirling-constant-n (* 2 n)) 2)
                               4
                               (1+ (* 2 n))
                               (/ (* 2 n))))
                         (* (expt (stirling-constant-n n) 4)
                            (expt (stirling-constant-n (* 2 n)) -2)
                            1/4
                            (/ (* 2 n)
                               (1+ (* 2 n))))))))

  (local
   (defthmd lemma-2
       (implies (and (integerp n)
                     (< 1 n))
                (equal (/ (scaled-wallis-numerator n)
                          (scaled-wallis-denominator n))
                       (* (expt (stirling-constant-n n) 4)
                          (expt (stirling-constant-n (* 2 n)) -2)
                          1/4
                          (/ (* 2 n)
                             (1+ (* 2 n))))))
     :hints (("Goal"
              :use ((:instance lemma-1)
                    (:instance wallis-quotient-as-stirling-constant))))
     ))


  (local
   (defthmd lemma-3
       (implies (and (posp n)
                     (i-large n))
                (equal (standard-part (* (expt (stirling-constant-n n) 4)
                                         (expt (stirling-constant-n (* 2 n)) -2)
                                         1/4
                                         (/ (* 2 n)
                                            (1+ (* 2 n)))))
                       (/ (acl2-pi) 2)))
     :hints (("Goal"
              :use ((:instance wallis-product-convergence)
                    (:instance scaled-wallis-simplify)
                    (:instance lemma-2))))))

  (local
   (defthm-std lemma-4
       (standardp (/ (acl2-pi) 2))))

  (local
   (defthm lemma-5
       (i-limited (stirling-constant-n n))
     :hints (("Goal"
              :in-theory (enable limited-stirling-constant-n)))))

  (local
   (defthm lemma-6
       (i-limited (stirling-constant-n (* 2 n)))
     :hints (("Goal"
              :in-theory (enable limited-stirling-constant-n)))))

  (local
   (defthm lemma-7
       (i-limited (expt (stirling-constant-n n) 4)))
   )

  (local
   (defthm lemma-8
       (i-limited (expt (stirling-constant-n (* 2 n)) 2))
     ))

  (local
   (defthm lemma-9
       (implies (posp n)
                (and (< (* (* 2 n)
                           (/ (1+ (* 2 n))))
                        2)
                     (< (* (/ (* 2 n))
                           (1+ (* 2 n)))
                        2)))))

  (local
   (defthm lemma-10
       (implies (posp n)
                (and (i-limited (* (* 2 n)
                                   (/ (1+ (* 2 n)))))
                     (i-limited (* (/ (* 2 n))
                                   (1+ (* 2 n))))))
     :hints (("Goal"
              :use ((:instance large-if->-large
                               (x (* (* 2 n)
                                     (/ (1+ (* 2 n)))))
                               (y 2))
                    (:instance large-if->-large
                               (x (* (/ (* 2 n))
                                     (1+ (* 2 n))))
                               (y 2)))))))

  #|
  (local
  (defthm lemma-1199999
  (implies (posp n)
  (equal (/ (expt (stirling-constant-n n) 4)
  (* (expt (stirling-constant-n (* 2 n)) 2)
  4
  (1+ (* 2 n))
  (/ (* 2 n))))
  (* (expt (stirling-constant-n n) 4)
  (expt (stirling-constant-n (* 2 n)) -2)
  1/4
  (/ (* (1+ (* 2 n))
  (/ (* 2 n)))))))))
  |#

  (local
   (defthm lemma-11
       (implies (posp n)
                (i-limited (expt (stirling-constant-n (* 2 n)) -2)))
     :instructions
     ((:use (:instance not-small-stirling-constant-n
                       (n (* 2 n))))
      :pro :s (:dv 1)
      (:dv 1)
      :x-dumb
      (:= (* (/ (stirling-constant-n (* 2 n)))
             (expt (stirling-constant-n (* 2 n))
                   -1)))
      (:dv 2)
      :x
      (:= (/ (stirling-constant-n (* 2 n))))
      :top
      (:claim (i-limited (/ (stirling-constant-n (* 2 n)))))
      (:dv 1)
      :top (:use (:instance i-limited-times
                            (x (/ (stirling-constant-n (* 2 n))))
                            (y (/ (stirling-constant-n (* 2 n)))))))))


  (local
   (defthm lemma-12
       (implies (i-large n)
                (i-close (/ (* 2 n)
                            (1+ (* 2 n)))
                         1))
     :instructions
     (:pro
      :x (:dv 1)
      (:casesplit (acl2-numberp n))
      (:claim (not (= n 0)))
      :s (:dv 2)
      (:= (+ (* 2 n (/ (+ 1 (* 2 n))))
             (/ (+ 1 (* 2 n)))
             (- (/ (+ 1 (* 2 n))))))
      (:rewrite |(+ c (+ d x))|)
      (:dv 1)
      :top
      (:use (:instance (:theorem (implies (and (acl2-numberp x) (acl2-numberp y))
                                          (= (+ (* x y) y) (* (1+ x) y))))
                       (x (* 2 n))
                       (y (/ (+ 1 (* 2 n))))))
      (:change-goal nil t)
      :bash (:in-theory (enable i-large))
      :top :bash :pro (:forwardchain 1)
      (:dv 1)
      (:dv 2)
      (:= (* (+ 1 (* 2 n)) (/ (+ 1 (* 2 n)))))
      (:= 1)
      :up
      :up :s
      :top :bash)))

  (local
   (defthm lemma-13
       (implies (i-large n)
                (equal (standard-part  (/ (* 2 n)
                                          (1+ (* 2 n))))
                       1))
     :hints (("Goal"
              :use ((:instance lemma-12)
                    (:instance
                     close-to-standard-implies-standard-part-is-that-standard
                     (x (/ (* 2 n) (1+ (* 2 n))))
                     (stdx 1)))
              :in-theory (enable i-large)
              ))))

  (local
   (defthmd lemma-14
       (implies (i-limited x)
                (equal (standard-part (expt x 4))
                       (expt (standard-part x) 4)))
     :instructions (:pro (:dv 1)
                         (:dv 1)
                         (:= (* x x x x))
                         :up :nx
                         (:= (* (standard-part x)
                                (standard-part x)
                                (standard-part x)
                                (standard-part x)))
                         :top (:claim (not (i-large (* x x))))
                         (:claim (not (i-large (* x x x))))
                         (:dv 1)
                         (:rewrite standard-part-of-times)
                         (:dv 2)
                         (:rewrite standard-part-of-times)
                         (:dv 2)
                         (:rewrite standard-part-of-times)
                         :top :s)))

  (local
   (defthmd lemma-15
       (implies (and (i-limited x)
                     (not (i-small x)))
                (equal (standard-part (expt x -2))
                       (expt (standard-part x) -2)))
     :instructions (:pro (:dv 1)
                         (:dv 1)
                         (:= (* (/ x) (/ x)))
                         :up (:rewrite standard-part-of-times)
                         (:dv 1)
                         (:rewrite standard-part-of-udivide)
                         :nx (:rewrite standard-part-of-udivide)
                         :up (:= (expt (standard-part x) -2))
                         :top :s
                         :bash :bash)))

  (local
   (defthm lemma-16
       (implies (and (posp n)
                     (i-large n))
                (equal (standard-part (* (expt (stirling-constant-n n) 4)
                                         (expt (stirling-constant-n (* 2 n)) -2)
                                         1/4
                                         (/ (* 2 n)
                                            (1+ (* 2 n)))))
                       (* (standard-part (expt (stirling-constant-n n) 4))
                          (standard-part (expt (stirling-constant-n (* 2 n)) -2))
                          1/4)))
     :instructions (:pro (:dv 1)
                         (:rewrite standard-part-of-times)
                         (:dv 2)
                         (:rewrite standard-part-of-times)
                         (:dv 2)
                         (:rewrite standard-part-of-times)
                         (:dv 2)
                         (:rewrite lemma-13)
                         :top
                         :s :bash (:use (:instance lemma-10))
                         (:use (:instance lemma-11))
                         (:use (:instance i-limited-times (x 1/4)
                                          (y (* (* 2 n) (/ (+ 1 (* 2 n)))))))
                         (:use (:instance lemma-10))
                         :bash (:use (:instance lemma-7))
                         (:use (:instance lemma-11))
                         :pro (:forwardchain 1)
                         (:use (:instance lemma-10))
                         :pro (:forwardchain 1)
                         (:dv 1)
                         (:rewrite i-limited-times)
                         (:dv 1)
                         (:rewrite i-limited-times)
                         :bash)
     ))

  (local
   (defthm lemma-17
       (implies (and (posp n)
                     (i-large n))
                (equal (* (standard-part (expt (stirling-constant-n n) 4))
                          (standard-part (expt (stirling-constant-n (* 2 n)) -2))
                          1/4)
                       (/ (acl2-pi) 2)))
     :hints (("Goal"
              :use ((:instance lemma-3)
                    (:instance lemma-16))))
     ))

  (local
   (defthm lemma-18
       (implies (and (natp n)
                     (i-large n))
                (i-close (stirling-constant-n n)
                         (stirling-constant)))
     :hints (("Goal"
              :by (:instance close-stirling-constant)))))

  (local
   (defthm lemma-19
       (implies (and (natp n)
                     (i-large n))
                (equal (standard-part (stirling-constant-n n))
                       (stirling-constant)))
     :hints (("Goal"
              :use ((:instance lemma-18)
                    (:instance close-to-standard-implies-standard-part-is-that-standard
                               (x (stirling-constant-n n))
                               (stdx (stirling-constant))))))))

  (local
   (defthm lemma-20
       (implies (and (posp n)
                     (i-large n))
                (equal (* (expt (stirling-constant) 4)
                          (expt (stirling-constant) -2)
                          1/4)
                       (/ (acl2-pi) 2)))
     :hints (("Goal"
              :use ((:instance lemma-17)
                    (:instance lemma-14 (x (stirling-constant-n n)))
                    (:instance lemma-15 (x (stirling-constant-n (* 2 n))))
                    (:instance lemma-19)
                    (:instance lemma-19 (n (* 2 n)))
                    (:instance not-small-stirling-constant-n (n (* 2 n))))
              :in-theory (disable stirling-constant)))
     ))

  (local
   (defthm lemma-21
       (implies (and (posp n)
                     (i-large n))
                (equal (* (expt (stirling-constant) 2)
                          1/4)
                       (/ (acl2-pi) 2)))
     :hints (("Goal"
              :USE ((:INSTANCE LEMMA-20))
              :in-theory (disable stirling-constant)))))

  (local
   (defthm lemma-22
       (implies (and (posp n)
                     (i-large n))
                (equal (expt (stirling-constant) 2)
                       (* 2 (acl2-pi))))
     :hints (("Goal"
              :USE ((:INSTANCE LEMMA-21))
              :in-theory (disable stirling-constant
                                  LEMMA-21)))))

  (defthmd stirling-constant-value
      (implies (and (posp n)
                    (i-large n))
               (equal (stirling-constant)
                      (acl2-sqrt (* 2 (acl2-pi)))))
    :hints (("Goal"
             :USE ((:INSTANCE LEMMA-22)
                   (:instance SQRT-*-X-X
                              (x (stirling-constant))))
             :in-theory (disable stirling-constant
                                 (stirling-constant)
                                 LEMMA-22))))
  )

(local
 (defthm factorial-as-stirling-constant-n
     (implies (and (integerp n)
                   (< 1 n))
              (equal (/ (factorial n)
                       (* (expt n n)
                          (/ (acl2-exp n))
                          (acl2-sqrt n)))
                     (stirling-constant-n n)))
   :hints (("Goal"
            :use ((:instance factorial-as-stirling-term)
                  ;;(:instance ln-stirling-constant-n)
                  ;;(:instance stirling-constant-n)
                  )
            :in-theory (enable stirling-constant-n
                               ln-stirling-constant-n)))))

(local
 (defthm factorial-as-stirling-constant
     (implies (and (natp n)
                   (i-large n))
              (i-close (/ (factorial n)
                          (* (expt n n)
                             (/ (acl2-exp n))
                             (acl2-sqrt n)))
                     (stirling-constant)))
   :hints (("Goal"
            :use ((:instance factorial-as-stirling-constant-n)
                  (:instance close-stirling-constant)
                  (:instance limited-stirling-constant-n)
                  (:instance large->-non-large
                             (x n)
                             (y 1))
                  )
            :in-theory (e/d (stirling-constant-n
                             ln-stirling-constant-n)
                            (large->-non-large))
            ))))

(local
 (defthm factorial-as-stirling-constant-corollary
     (implies (and (natp n)
                   (i-large n))
              (i-close (/ (factorial n)
                          (* (expt n n)
                             (/ (acl2-exp n))
                             (acl2-sqrt n)))
                       (acl2-sqrt (* 2 (acl2-pi)))))
   :hints (("Goal"
            :use ((:instance factorial-as-stirling-constant)
                  (:instance stirling-constant-value))))))

(local
 (defthm-std sqrt-2-pi-is-standard
     (standardp (acl2-sqrt (* 2 (acl2-pi))))))

(local
 (defthm-std /-sqrt-2-pi-is-standard
     (standardp (/ (acl2-sqrt (* 2 (acl2-pi)))))))

(defthm stirling-approximation-to-factorial
    (implies (and (natp n)
                  (i-large n))
             (i-close (/ (factorial n)
                         (* (acl2-sqrt (* 2 (acl2-pi)))
                            (expt n n)
                            (/ (acl2-exp n))
                            (acl2-sqrt n)))
                      1))
  :hints (("Goal"
           :use ((:instance factorial-as-stirling-constant-corollary)
                 (:instance close-times
                            (x1 (/ (factorial n)
                                   (* (expt n n)
                                      (/ (acl2-exp n))
                                      (acl2-sqrt n))))
                            (x2 (acl2-sqrt (* 2 (acl2-pi))))
                            (y (/ (acl2-sqrt (* 2 (acl2-pi))))))
                 (:instance standards-are-limited
                            (x (acl2-sqrt (* 2 (acl2-pi)))))
                 (:instance standards-are-limited
                            (x (/ (acl2-sqrt (* 2 (acl2-pi)))))))
           :in-theory (disable close-times
                               close-times-2
                               standards-are-limited))))

(encapsulate nil

    (local
     (defthmd lemma-1
         (implies (and (realp x)
                       (< 0 x))
                  (equal (acl2-ln (acl2-sqrt x))
                         (* 1/2 (acl2-ln x))))
       :INSTRUCTIONS (:PRO (:DV 1)
                           (:DV 1)
                           (:= (RAISE X 1/2))
                           :UP (:REWRITE LN-OF-POWERS-POSITIVE)
                           :TOP :S)))

  (local
   (defthmd lemma-2
       (implies (and (i-close x1 x2)
		     (i-close y1 y2))
	        (i-close (+ x1 y1) (+ x2 y2)))
     :hints (("Goal"
	      :use ((:instance i-small-plus
			       (x (+ x1 (- x2)))
			       (y (+ y1 (- y2)))))
              :in-theory (enable i-close))
	     )))

  (local
   (defthmd lemma-3
       (implies (i-large n)
                (not (equal n 1)))
     :hints (("Goal"
              :use ((:instance large-if->-large
                               (x n)
                               (y 1)))))))


  (local
   (defthm lemma-4
       (implies (and (posp n)
                     (i-large n))
                (i-close (acl2-ln (factorial n))
                         (+ (acl2-ln (expt n n))
                            (- n)
                            (acl2-ln (acl2-sqrt n))
                            (ln-stirling-constant))))
     :hints (("Goal"
              :use ((:instance lemma-2
                               (x1 (+ (acl2-ln (expt n n))
                                      (- n)
                                      (acl2-ln (acl2-sqrt n))))
                               (y1 (ln-stirling-constant-n n))
                               (x2 (+ (acl2-ln (expt n n))
                                      (- n)
                                      (acl2-ln (acl2-sqrt n))))
                               (y2 (ln-stirling-constant)))
                    (:instance lemma-3)
                    (:instance ln-factorial-as-stirling-term)
                    (:instance close-ln-stirling-constant))
              :in-theory (disable ln-stirling-constant-n
                                  ln-stirling-constant)
              ))))

  (local
   (defthm lemma-5
       (implies (and (posp n)
                     (i-large n))
                (i-close (acl2-ln (factorial n))
                         (+ (acl2-ln (expt n n))
                            (- n)
                            (acl2-ln (acl2-sqrt n))
                            (acl2-ln (stirling-constant)))))
     :hints (("Goal"
              :use ((:instance lemma-4)
                    (:instance acl2-ln-of-stirling-constant))))))

  (local
   (defthm lemma-6
       (implies (and (posp n)
                     (i-large n))
                (i-close (acl2-ln (factorial n))
                         (+ (acl2-ln (expt n n))
                            (- n)
                            (acl2-ln (acl2-sqrt n))
                            (acl2-ln (acl2-sqrt (* 2 (acl2-pi)))))))
     :hints (("Goal"
              :use ((:instance lemma-4)
                    (:instance stirling-constant-value))))))

  (local
   (defthm lemma-7
       (implies (and (posp n)
                     (i-large n))
                (i-close (acl2-ln (factorial n))
                         (+ (acl2-ln (expt n n))
                            (- n)
                            (* 1/2 (+ (acl2-ln n)
                                      (acl2-ln (* 2 (acl2-pi))))))))
     :instructions ((:use (:instance lemma-6))
                    (:use (:instance lemma-1 (x n)))
                    (:use (:instance lemma-1 (x (* 2 (acl2-pi)))))
                    :pro (:forwardchain 1)
                    (:forwardchain 2)
                    (:forwardchain 1)
                    (:contrapose 4)
                    (:dv 1)
                    (:dv 2)
                    (:dv 3)
                    := :nx := :top (:drop 3 5)
                    :bash)))

  (local
   (defthm lemma-8
       (implies (and (posp n)
                     (i-large n))
                (i-close (acl2-ln (factorial n))
                         (+ (acl2-ln (expt n n))
                            (- n)
                            (* 1/2 (acl2-ln (* 2 (acl2-pi) n))))))
     :hints (("Goal"
              :use ((:instance lemma-7)
                    (:instance ln-product-real
                               (x (* 2 (acl2-pi)))
                               (y n)))
              :in-theory (disable ln-product-real
                                  ln-product-complex)))))

  (defthm stirling-approximation-to-ln-factorial
      (implies (and (posp n)
                    (i-large n))
               (i-close (acl2-ln (factorial n))
                        (+ (acl2-ln (expt n n))
                           (- n)
                           (acl2-ln (acl2-sqrt (* 2 (acl2-pi) n))))))
    :hints (("Goal"
             :use ((:instance lemma-8)
                   (:instance lemma-1
                              (x (* 2 (acl2-pi) n)))))))
  )
