(in-package "ACL2")

(local (include-book "nonstd/nsa/norm" :dir :system))
(local (include-book "nonstd/nsa/factorial" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "arithmetic/sumlist" :dir :system))
(local (include-book "arithmetic/abs" :dir :system))
(include-book "nonstd/nsa/exp" :dir :system)
(include-book "nonstd/nsa/exp-continuous" :dir :system)

(local 
 (defun f-term (x counter)
   (/ (expt x counter)
      (factorial (+ counter 2)))))

(local
 (defun f-list (nterms counter x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0))
      nil
    (cons (f-term x counter)
	  (f-list (1- nterms) 
                  (1+ counter) 
                  x)))))

(local
 (defun f (x)
   (sumlist (f-list (i-large-integer) 0 x))))

; Now we show that (f x) is limited for limited x.
(local
 (encapsulate
  nil
  (local
   (defthm factorial-greater
     (implies (and (integerp counter)
                   (<= 0 counter))
              (< (factorial counter)
                 (factorial (+ counter 2))))
     :hints (("Goal" :in-theory (enable factorial)))
     :rule-classes (:linear)))

  (local
   (defthm norm-factorial-greater
     (implies (and (integerp counter)
                   (<= 0 counter))
              (<= (norm (factorial counter))
                  (norm (factorial (+ counter 2)))))
     :hints (("Goal"
              :use ((:instance factorial-greater)
                    (:instance
                     norm-preserves-<=-for-reals
                     (x (factorial counter))
                     (y (factorial (+ counter 2)))))))))
  
  (local
   (defthm f-term-<-exp-taylor-term                     
     (implies (and (acl2-numberp x)
                   (integerp counter)
                   (<= 0 counter))
              (<= (norm (f-term x counter))
                  (norm (taylor-exp-term x counter))))
     :hints (("Goal" :do-not-induct t
              :use ((:instance factorial-greater)
                    (:instance <-y-*-x-y
                               (y (NORM (EXPT X COUNTER)))
                               (x (/ (NORM (FACTORIAL COUNTER))
                                     (NORM (FACTORIAL (+ 2 COUNTER)))))))))))
  (local
   (defthm f-list-seq-norm-<=
     (implies (and (acl2-numberp x)
                   (integerp counter)
                   (<= 0 counter))
              (seq-norm-<= (f-list nterms counter x)
                           (taylor-exp-list nterms counter x)))
     :hints (("Goal" :in-theory (disable f-term taylor-exp-term )))))

  (defthm f-limited
    (implies (i-limited x)
             (i-limited (f x)))
    :hints (("Goal" :do-not-induct t
             :use (:instance comparison-test
                             (x (f-list (i-large-integer) 0 x))
                             (y (taylor-exp-list (i-large-integer) 0 x))))))
  ))

(local
 (defthm f-standard
   (implies
    (standard-numberp x)
    (standardp (standard-part (f x))))
   :hints (("Goal" :in-theory (disable f)
            :use (:instance f-limited)))))
  
; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
(defattach-system hide-with-comment-p constant-nil-function-arity-0)

(local
 (encapsulate
  nil
  (local (in-theory (disable f)))
  (local
   (defthm f-0-standard
     (STANDARDP (STANDARD-PART (hide (F 0))))
     :hints (("Goal" :expand ((:free (x) (hide x)))
              :use (:instance f-standard (x 0))))))

  (defun-std g (x)
    (standard-part (f (fix x))))))
(local
 (encapsulate
  nil
  (local
   (defun fxx-term (x counter)
     (/ (* x x (expt x counter))
        (factorial (+ counter 2)))))

  (local 
   (defun fxx-list (nterms counter x)
     (if (or (zp nterms)
             (not (integerp counter))
             (< counter 0))
         nil
       (cons (fxx-term x counter)
             (fxx-list (1- nterms) 
                       (1+ counter) 
                       x)))))

  (local
   (defthm times-in
     (equal (* x x (sumlist (f-list nterms counter x)))
            (sumlist (fxx-list nterms counter x)))))

  (local
   (defthm f-term-to-taylor-exp-term
     (implies (and (integerp counter)
                   (<= 0 counter))
              (equal (* x x (f-term x counter))
                     (* (taylor-exp-term x (+ counter 2)))))
     :hints (("Goal" :do-not-induct t))))
         

  (local
   (defthm fxx-to-taylor-exp
     (implies (and (integerp counter)
                   (<= 0 counter))
              (equal (fxx-list nterms counter x)
                     (taylor-exp-list nterms (+ 2 counter) x)))))

 
  (defthm take-apart-taylor-exp-list
    (implies (not (zp nterms))
             (equal (+ 1 x (* x x (sumlist (f-list nterms 0 x))))
                    (sumlist (taylor-exp-list (+ nterms 2) 0 x)))))))


(local 
 (defthm take-apart-taylor-exp-list-large
   (equal (+ 1 x (* x x (sumlist (f-list (i-large-integer) 0 x))))
          (sumlist (taylor-exp-list (+ (i-large-integer) 2) 0 x)))
   :hints (("Goal" :use 
            (:instance take-apart-taylor-exp-list
                       (nterms (i-large-integer)))))))


(local
 (defthm f-list-close-taylor-exp-list
   (implies (i-limited x)
            (i-close (+ 1 x (* x x (sumlist (f-list (i-large-integer) 0 x))))
                     (sumlist (taylor-exp-list (i-large-integer) 0 x))))
   :hints (("Goal"
            :use (:instance exp-convergent
                            (N (i-large-integer))
                            (M (+ (i-large-integer) 2)))))))

(local 
 (encapsulate
  nil
  (in-theory (enable i-close i-small))
  (defthm g-close-taylor-exp-list-lemma
    (implies (standard-numberp x)
             (equal (+ 1 x (* x x (standard-part (f x))))
                    (standard-part  (sumlist (taylor-exp-list (i-large-integer) 0 x)))))
    :hints (("Goal"
             :in-theory (disable taylor-exp-list-split
                                 take-apart-taylor-exp-list-large
                                 take-apart-taylor-exp-list
                                 f-list-close-taylor-exp-list
                                 )
             :use ((:instance f-list-close-taylor-exp-list)
                   (:instance f-limited)))))))


(local
 (defthm-std g-close-taylor-exp-list
   (implies (acl2-numberp x)
            (equal (+ 1 x (* x x (g x)))
                   (acl2-exp x)))
   :hints (("Goal"
            :in-theory (disable f)))))

(local
 (encapsulate
  nil
  (local 
   (defthm arith-lemma
     (implies (and (acl2-numberp x)
                   (not (equal x 0))
                   (equal (+ 1 x (* x x g))
                          e))
              (equal (+ 1 (* x g))
                     (/ (- e 1) x)))))
                

  (defthm-std thm2
    (implies (and (acl2-numberp x)
                  (not (equal x 0)))
             (equal (/ (- (acl2-exp x) 1)
                       x)
                    (+ 1 (* x (g x)))))
    :hints (("Goal"
             :in-theory (disable acl2-exp g)
             :use (:instance arith-lemma
                             (g (g x))
                             (e (acl2-exp x))))))))

;;; theorem 3
 
(local
 (defthm expt-norm
   (implies (and (acl2-numberp x)
                 (<= (norm x) 1)
                 (integerp n)
                 (<= 0 n))
            (<= (norm (expt x n)) 1))
   :hints (("Subgoal *1/5"
            :in-theory (disable <-y-*-y-x)
            :use (:instance <-y-*-y-x
                            (y (norm x))
                            (x (norm (expt x (- n 1)))))))))

(local
 (defthm f-term-subone-<=-1
   (implies (and (acl2-numberp x) (<= (norm x) 1)
                 (integerp counter) (<= 0 counter))
            (<= (norm (f-term x counter))
                (norm (f-term 1 counter))))))

(local
 (defthm norm-of-real-sum
   (implies (and (realp a)
                 (realp b)
                 (<= 0 a)
                 (<= 0 b))
            (equal (norm (+ a b))
                   (+ (norm a) (norm b))))
   :hints (("Goal" :use (:instance norm-distributivity
                                   (x 1))))))
                        

(local
 (defthm f-term-real
   (implies (realp x)
            (realp (f-term x counter)))
   :rule-classes (:type-prescription)))
(local
 (defthm f-term-positive
   (implies (and (realp x)
                 (<= 0 x))
            (<= 0 (f-term x counter)))
   :rule-classes (:type-prescription)))

(local
 (defthm sumlist-f-real
   (implies (realp x)
            (realp (sumlist (f-list nterms counter x))))))
(local
 (defthm sumlist-f-positive
   (implies (and (realp x)
                 (<= 0 x))
            (<= 0 (sumlist (f-list nterms counter x))))))

(local
 (encapsulate
  nil

  (local
   (defthm sum-less
     (implies (and (<= x y)
                   (<= a b))
              (<= (+ x a)
                  (+ y b)))))

  (defthm norm-f-list-subone-<=-1
    (implies (and (acl2-numberp x) (<= (norm x) 1)
                  (integerp counter) (<= 0 counter)
                  (integerp nterms) (<= 0 nterms))
             (<= (norm (sumlist (f-list nterms counter x)))
                 (norm (sumlist (f-list nterms counter 1)))))
    :hints (("Goal" :in-theory (disable f-term SUM-LESS NORM-TRIANGLE-INEQUALITY))
           
            ("Subgoal *1/6"
             :do-not-induct t
             :use ((:instance norm-triangle-inequality
                              (a (F-TERM X COUNTER))
                              (b (SUMLIST (F-LIST (+ -1 NTERMS)
                                                  (+ 1 COUNTER)
                                                  X))))
                   (:instance sum-less
                              (a (NORM (F-TERM X COUNTER)))
                              (b (NORM (F-TERM 1 COUNTER)))
                              (x (NORM (SUMLIST (F-LIST (+ -1 NTERMS)
                                                        (+ 1 COUNTER)
                                                        X))))
                              (y (NORM (SUMLIST (F-LIST (+ -1 NTERMS)
                                                        (+ 1 COUNTER)
                                                        1)))))))))))

(local
 (defthm f-subone-<=-1
   (implies (and (acl2-numberp x) (<= (norm x) 1))
            (<= (norm (f x))
                (norm (f 1))))))

(local
 (defthm f-subone-<=-1-std
   (implies (and (acl2-numberp x) (<= (norm x) 1))
            (<= (standard-part (norm (f x)))
                (standard-part (norm (f 1)))))))


(local
 (defthm 1-not-large
   (not (i-large 1))))

(local
 (defthm between-0-and-1-limited
   (implies (and (realp x)
                 (<= 0 x)
                 (<= x 1))
            (i-limited x))
   :hints (("Goal"
            :use ((:instance abs-x->-0 (x x))
                  (:instance abs-x->-0 (x 1))
                  (:instance large-if->-large
                             (y 1))
                  (:instance 1-not-large))))))

(local
 (defthm x-limited-for-subone-norm
   (implies (and (acl2-numberp x)
                 (<= (norm x) 1))
            (i-limited (norm x)))))

(local
 (defthm standard-part-in
   (implies (and (acl2-numberp x) (<= (norm x) 1))
            (equal (standard-part (norm (f x)))
                   (norm (standard-part (f x)))))
   :hints (("Goal" :in-theory (disable f)
            :use (:instance limited-norm)))))

(local
 (defthm-std norm-g-subone-<=-norm-g-1
   (implies (and (acl2-numberp x)
                 (<= (norm x) 1))
            (<= (norm (g x))
                (norm (g 1))))
   :hints (("Goal" :in-theory (disable f )
            :use ((:instance standard-part-in (x 1))
                  (:instance f-subone-<=-1-std))))))

(local
 (defthm between-0-and-limited
   (implies (and (realp x)
                 (realp y)
                 (<= 0 x)
                 (<= x y)
                 (i-limited y))
            (i-limited x))
   :hints (("Goal"
            :use ((:instance abs-x->-0 (x x))
                  (:instance abs-x->-0 (x 1))
                  (:instance large-if->-large)
                  (:instance 1-not-large))))))

(local
 (defthm g-1-limited
   (i-limited (g 1))
   :hints (("Goal" :in-theory (disable f)
            :expand ((:free (x) (hide x)))
            :use (:instance f-limited (x 1))))))

(local
 (defthm g-subone-limited
   (implies (and (acl2-numberp x)
                 (<= (norm x) 1))
            (i-limited (norm (g x))))
   :hints (("Goal"
            :in-theory (disable g)
            :use ((:instance limited-norm (x (g 1)))
                  (:instance  between-0-and-limited
                              (x (norm (g x)))
                              (y (norm (g 1)))))))))
           
;; theorem 4
(local
 (encapsulate
  nil
  (local
   (defthm thm4-lemma
     (implies (and (acl2-numberp x)
                   (i-small x))
              (i-small (norm x)))))

  (local
   (defthm standard-less-to-actual-less
     (implies (and (realp x)
                   (realp y)
                   (< (standard-part x) (standard-part y)))
              (< x y))))

  (local
   (defthmd small-less-1
     (implies (and (realp x)
                   (i-small x))
              (< x 1))
     :hints (("Goal" :in-theory (enable i-small)
              :use (:instance  standard-less-to-actual-less
                               (y 1))))))

  (local 
   (defthm norm-subone-for-small
     (implies (and (acl2-numberp x)
                   (i-small x))
              (<= (norm x) 1))
     :hints (("Goal" 
              :use ((:instance  thm4-lemma)
                    (:instance small-less-1 (x (norm x))))))))

  (defthm g-x-limited-for-small
    (implies (and (acl2-numberp x)
                  (i-small x))
             (i-limited (g x)))
    :hints (("Goal" :use (:instance limited-norm (x (g x))))))))


(local
 (defthm thm4
   (implies (and (acl2-numberp dx)
                 (i-small dx)
                 (not (equal dx 0)))
            (i-close (/ (- (acl2-exp dx) 1)
                        dx)
                     1))))

;;; theorem 5
(include-book "nonstd/nsa/exp-sum" :dir :system)
(include-book "defderivative")

(local
 (defderivative-fns (acl2-exp x) x))


(local
 (defthm factor-exp-out-of-difference
   (implies (and (acl2-numberp x)
                 (acl2-numberp dx))
            (equal (acl2-exp-difference x dx)
                   (* (acl2-exp x)
                      (- (acl2-exp dx)
                         1))))))


(local
 (defthm factor-exp-out-of-differential
   (implies (and (acl2-numberp x)
                 (acl2-numberp dx))
            (equal (acl2-exp-differential x dx)
                   (* (acl2-exp x) 
                      (/ (- (acl2-exp dx)
                            1)
                         dx))))))
      
(local
 (defthm close-to-1-is-limited
   (implies (and (acl2-numberp x)
                 (i-close x 1))
            (i-limited x))))

(local
 (defthm multiply-by-1ish-stays-close
   (implies (and (i-limited y)
                 (i-close z 1))
            (i-close y (* z y)))))
 

(defthm exp-limited-for-limited
  (implies (i-limited x)  
           (i-limited (acl2-exp x)))
  :hints (("Goal" 
           :in-theory (disable acl2-exp)
           :use (:instance i-close-limited-2
                           (x (acl2-exp x) )
                           (y (acl2-exp (standard-part x)))))))

(local
 (defthm all-but-factored-part-small
   (implies (and (i-limited x)
                 (i-small dx)
                 (not (equal dx 0))
                 (acl2-numberp dx))
            (i-close (* (acl2-exp x) 
                        (/ (- (acl2-exp dx)
                              1)
                           dx))
                     (acl2-exp x)))
   :hints (("Goal"
            :use (:instance multiply-by-1ish-stays-close
                            (y x)
                            (z (/ (- (acl2-exp dx)
                                     1)
                                  dx)))))))

(local
 (defthm differential-exp-close-to-exp
   (implies (and (i-limited x)
                 (i-small dx)
                 (not (equal dx 0))
                 (acl2-numberp dx))
            (i-close (acl2-exp-differential x dx)
                     (acl2-exp x)))))

(local (defthm small-difference
         (implies (i-close x y)
                  (i-small (- y x)))))

(local (defthm move-negate-out-of-denom
         (implies (and (acl2-numberp x)
                       (not (equal x 0)))
                  (equal (/ (- x))
                         (- (/ x))))))

(defthm acl2-exp-derivative
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-exp x) (acl2-exp y))
                       (- x y))
                    (acl2-exp x)))
  :hints (("Goal"
           :in-theory (disable i-small i-close acl2-exp exp-sum 
                               FACTOR-EXP-OUT-OF-DIFFERENCE
                               FACTOR-EXP-OUT-OF-DIFFERENTIAL)
           :use ((:instance differential-exp-close-to-exp
                           (x x)
                           (dx (- y x)))
                 (:instance small-difference (x x) ( y y))
                 (:instance move-negate-out-of-denom
                            (x (- x y)))))))

(in-theory (disable i-close i-small acl2-exp))

(defthmd elem-acl2-exp-close
  (implies (and (acl2-numberp x) (standardp x)
                (acl2-numberp y)
                (i-close x y) (not (equal x y)))
           (i-close (/ (- (acl2-exp x) (acl2-exp y))
                       (- x y))
                    (acl2-exp x)))
  :hints (("Goal" :use (:instance acl2-exp-derivative))))

(defthmd elem-acl2-exp-number
  (implies (acl2-numberp x)
           (acl2-numberp (acl2-exp x))))

(defthm-std elem-acl2-exp-standard
  (implies (and (standardp x) (acl2-numberp x))
           (standardp (acl2-exp x))))
(in-theory (disable elem-acl2-exp-standard))

(defthmd elem-acl2-exp-continuous
  (implies (and (acl2-numberp x)
                (standardp x)
                (acl2-numberp y)
                (i-close x y))
           (i-close (acl2-exp x) (acl2-exp y))))

(defthmd elem-acl2-exp-prime-number
  (implies (acl2-numberp x)
           (acl2-numberp (acl2-exp x))))
(defthm-std elem-acl2-exp-prime-standard
  (implies (and (standardp x) (acl2-numberp x))
           (standardp (acl2-exp x))))
(in-theory (disable elem-acl2-exp-prime-standard))
(defthmd elem-acl2-exp-prime-continuous
  (implies (and (acl2-numberp x)
                (standardp x)
                (acl2-numberp y)
                (i-close x y))
           (i-close (acl2-exp x) (acl2-exp y))))

(include-book "differentiator")

(def-elem-derivative acl2-exp
  elem-acl2-exp
  (acl2-numberp x)
  (acl2-exp x))
