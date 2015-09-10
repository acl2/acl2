; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

;;;**************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************
(in-package "ACL2")

;BOZO make log-proofs.lisp

(include-book "ground-zero")

(local (include-book "../../arithmetic/top"))
(local (include-book "lognot"))
(local (include-book "bits"))
(local (include-book "bitn"))
(local (include-book "lnot"))
(local (include-book "logior"))
(local (include-book "logand"))
(local (include-book "logxor"))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))



;rename! mod-lognot-by-2
(defthm mod-logior-9
  (implies (integerp i)
           (iff (= (mod (lognot i) 2) 0)
                (not (= (mod i 2) 0))))
  :hints (("Goal" :in-theory (enable mod-by-2)
           )))



(defthm mod-logior-10
  (implies (and (integerp i)
                (integerp j))
           (iff (and (= (mod i 2) 0) (= (mod j 2) 0))
                (= (mod (logior i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use mod-logior-by-2
           :in-theory (set-difference-theories
                       (enable mod-by-2)
                       '(logior)))))
;move
(local
 (defun log-induct-3 (x y z)
   (if (and (integerp x) (>= x 0)
            (integerp y) (>= y 0)
            (integerp z) (>= z 0))
       (if (or (= x 0) (= y 0) (= z 0))
           ()
         (log-induct-3 (fl (/ x 2)) (fl (/ y 2)) (fl (/ z 2))))
     ())))



(local
 (defthm logior-logand-1
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp z) (>= z 0))
            (equal (logior (mod x 2)
                           (logand  (mod y 2) (mod z 2)))
                   (logand (logior (mod x 2) (mod y 2))
                           (logior (mod x 2) (mod z 2)))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod012 (m x))
                         (:instance mod012 (m y))
                         (:instance mod012 (m z)))))))

(local (defthm logior-logand-2
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0))
            (equal (logand (logior (mod x 2) (mod y 2)) (mod x 2))
                   (mod x 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod012 (m x))
                         (:instance mod012 (m y)))))))

;nice lemma?
(local
 (defthm logior-logand-3
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0))
            (= (logand (logior x y) x)
               x))
   :rule-classes ()
   :hints (("Goal" :induct (log-induct x y))
           ("Subgoal *1/2" :use ((:instance logior-logand-2)
                                 (:instance fl-mod-equal

                                            (y (logand (logior x y) x))))))))
;BOZO export!
;gen?
(defthm logior-logand
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y)
                (integerp z)
                (<= 0 z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2" :use ((:instance logior-logand-1)
                                (:instance fl-mod-equal
                                           (x (logior x (logand y z)))
                                           (y (logand (logior x y) (logior x z))))))
	  ("Subgoal *1/1" :use ((:instance logior-logand-3)
				(:instance logior-logand-3 (y z))))))

;BOZO export!
(defthm logior-logand-alt
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y)
                (integerp z)
                (<= 0 z))
           (equal (logior (logand y z) x)
                  (logand (logior x y) (logior x z))))
  :hints (("Goal" :use ( logior-logand)))
  :rule-classes ())



(local
 (defthm logand-logior-1
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp z) (>= z 0))
            (equal (logand (mod x 2)
                           (logior  (mod y 2) (mod z 2)))
                   (logior (logand (mod x 2) (mod y 2))
                           (logand (mod x 2) (mod z 2)))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod012 (m x))
                         (:instance mod012 (m y))
                         (:instance mod012 (m z)))))))

(defthm LOGAND-LOGIOR
  (implies (and (integerp x) (<= 0 x)
                (integerp y) (<= 0 y)
                (integerp z) (<= 0 z))
           (equal (logand x (logior y z))
                  (logior (logand x y) (logand x z))))
  :rule-classes ()
  :hints (("Goal" :induct (log-induct-3 x y z))
	  ("Subgoal *1/2" :use ((:instance logand-logior-1)
                                (:instance fl-mod-equal
                                           (x (logand x (logior y z)))
                                           (y (logior (logand x y) (logand x z))))))))
(defthm logand-logior-alt
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp z) (>= z 0))
           (equal (logand (logior y z) x)
                  (logior (logand y x) (logand z x))))
  :rule-classes ()
  :hints (("goal" :use ((:instance logand-logior)))))



;I should be able to prove mod-logand without appealing to logior!
;Rather, I should try to prove mod-logior from mod-logand.

;not about logand!
(local
 (defthm mod-logand-1
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0))
            (= x (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
                         (mod x (expt 2 n)))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance quot-mod (m x) (n (expt 2 n)))
                         (:instance or-dist-b (x (fl (/ x (expt 2 n)))) (y (mod x (expt 2 n)))) ;yuck!
                         (:instance mod-bnd-1 (m x) (n (expt 2 n)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
                         )))))

(local
 (defthm mod-logand-2
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (>= n 0))
            (= (logand x y)
               (logior (logand (* (expt 2 n) (fl (/ x (expt 2 n))))
                               y)
                       (logand (mod x (expt 2 n))
                               y))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod-logand-1)
;			(:instance mod>=0 (m x) (n (expt 2 n)))
                         (:instance logand-logior
                                    (x y)
                                    (y (* (expt 2 n) (fl (/ x (expt 2 n)))))
                                    (z (mod x (expt 2 n))))
                         )))))

(local
 (defthm mod-logand-3
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand x y)
		(logior (* (expt 2 n)
			   (logand (fl (/ x (expt 2 n)))
				   (fl (/ y (expt 2 n)))))
			(logand (mod x (expt 2 n))
				y))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-logand-2)
			(:instance and-dist-b (x (fl (/ x (expt 2 n))))))))))

(local
 (defthm mod-logand-4
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (>= n 0))
            (= (logand x y)
               (+ (* (expt 2 n)
                     (logand (fl (/ x (expt 2 n)))
                             (fl (/ y (expt 2 n)))))
                  (logand (mod x (expt 2 n))
                          y))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod-logand-3)
                         (:instance or-dist-b
                                    (x (logand (fl (/ x (expt 2 n)))
                                               (fl (/ y (expt 2 n)))))
                                    (y (logand (mod x (expt 2 n))
                                               y)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
                         (:instance mod-bnd-1 (m x) (n (expt 2 n)))
                         (:instance logand-bnd (x (mod x (expt 2 n))))
                         )))))

(defthm mod-logand-aux
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (= (mod (logand x y) (expt 2 n))
              (logand (mod x (expt 2 n)) y)))
  :rule-classes ()
  :hints (("goal" :use ((:instance mod-logand-4)
			(:instance mod-mult-eric
				   (x (logand (mod x (expt 2 n)) y))
				   (y (expt 2 n))
				   (a (logand (fl (/ x (expt 2 n))) (fl (/ y (expt 2 n))))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))
			(:instance logand-bnd (x (mod x (expt 2 n))))
			(:instance mod-does-nothing (m (logand (mod x (expt 2 n)) y)) (n (expt 2 n)))))))

;generalize (mod y (expt 2 n)) to anything < 2^n?
(defthm and-dist-d
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (mod y (expt 2 n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance mod-logand-aux (x y) (y x))
;			(:instance and-dist-a)
			(:instance mod-does-nothing (m (logand x y)) (n (expt 2 n)))))))

;compare to mod-logand-aux
;looks like we can wrap the mod around x or y or both (same for bits of logand?)
(defthm mod-logand
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (equal (mod (logand x y) (expt 2 n))
                  (logand (mod x (expt 2 n)) (mod y (expt 2 n)))))
  :hints (("goal" :use (mod-logand-aux
			(:instance and-dist-d (x (mod x (expt 2 n))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))))))

(encapsulate
 ()

 (local (defthm bits-logand-1
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logand (+ (* (expt 2 j) (bits x i j))
                                      (bits x (1- j) 0))
                                   (+ (* (expt 2 j) (bits y i j))
                                      (bits y (1- j) 0)))))
               :rule-classes ()
               :hints (("Goal" :in-theory (enable bits
                                                  )
                        :use ((:instance mod-logand (n (1+ i)))
                              (:instance expt-split (r 2) (i 1) (j i))
                              (:instance bits-plus-bits (n i) (p j) (m 0))
                              (:instance bits-plus-bits (x y) (n i) (p j) (m 0)))))))

 (local (defthm bits-logand-2
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logand (logior (* (expt 2 j) (bits x i j))
                                           (bits x (1- j) 0))
                                   (logior (* (expt 2 j) (bits y i j))
                                           (bits y (1- j) 0)))))
               :rule-classes ()
               :hints (("Goal" :use (bits-logand-1
                     ;                       (:instance bits< (i (1- j)) (j 0))
                     ;                      (:instance bits< (x y) (i (1- j)) (j 0))
                                     (:instance or-dist-b (x (bits x i j)) (n j) (y (bits x (1- j) 0)))
                                     (:instance or-dist-b (x (bits y i j)) (n j) (y (bits y (1- j) 0))))))))

 (local (defthm bits-logand-3
               (implies (and (integerp a) (>= a 0)
                             (integerp b) (>= b 0)
                             (integerp c) (>= c 0)
                             (integerp d) (>= d 0))
                        (= (logand (logior a b) (logior c d))
                           (logior (logior (logand a c) (logand c b))
                                   (logior (logand b d) (logand a d)))))
               :rule-classes ()
               :hints (("Goal" :use ((:instance logand-logior (x (logior a b)) (y c) (z d))
                                     (:instance logand-logior-alt (y a) (z b) (x c))
                                     (:instance logand-logior-alt (y a) (z b) (x d))

                     ;			(:instance bit-basic-d (x (logand a d)) (y (logand b d)))
                                     )))))

 (local (defthm bits-logand-4
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logior (logior (logand (* (expt 2 j) (bits x i j))
                                                   (* (expt 2 j) (bits y i j)))
                                           (logand (* (expt 2 j) (bits y i j))
                                                   (bits x (1- j) 0)))
                                   (logior (logand (bits x (1- j) 0)
                                                   (bits y (1- j) 0))
                                           (logand (* (expt 2 j) (bits x i j))
                                                   (bits y (1- j) 0))))))

               :rule-classes ()
               :hints (("Goal" :use (bits-logand-2
                     ;                 (:instance expt-pos (x j))
                                     (:instance bits-logand-3
                                                (a (* (expt 2 j) (bits x i j)))
                                                (b (bits x (1- j) 0))
                                                (c (* (expt 2 j) (bits y i j)))
                                                (d (bits y (1- j) 0))))))))

 (local (defthm bits-logand-5
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (logand (* (expt 2 j) (bits x i j))
                                   (* (expt 2 j) (bits y i j)))
                           (* (expt 2 j) (logand (bits x i j) (bits y i j)))))
               :rule-classes ()
               :hints (("Goal" :use (
                     ;                 (:instance expt-pos (x j))
                                     (:instance and-dist-b (n j) (x (bits x i j)) (y (* (expt 2 j) (bits y i j)))))))))



 (local (defthm bits-logand-7
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (logand (* (expt 2 j) (bits x i j))
                                   (bits y (1- j) 0))
                           0))
               :rule-classes ()
               :hints (("Goal" :in-theory (enable logand)
                        :use (
;                              bits-logand-6
                              (:instance fl-unique (x (/ (bits y (1- j) 0) (expt 2 j))) (n 0))
                     ;                 (:instance expt-pos (x j))
                     ;                (:instance expt-pos (x (- 1 j)))
                     ;                 (:instance bits< (x y) (i (1- j)) (j 0))
                     ;                 (:instance bit-basic-a (x (bits x i j)))
                              (:instance and-dist-b (n j) (x (bits x i j)) (y (bits y (1- j) 0))))))))

 (local (defthm bits-logand-8
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logior (logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
                                           0)
                                   (logior (logand (bits x (1- j) 0)
                                                   (bits y (1- j) 0))
                                           0))))
               :rule-classes ()
               :hints (("Goal" :use (bits-logand-4
                                     bits-logand-5
                                     bits-logand-7
                                     (:instance bits-logand-7 (x y) (y x)))))))

 (local (defthm bits-logand-9
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
                                   (logand (bits x (1- j) 0)
                                           (bits y (1- j) 0)))))
               :rule-classes ()
               :hints (("Goal" :use (bits-logand-8
                     ;			(:instance bit-basic-b (x (* (expt 2 j) (logand (bits x i j) (bits y i j)))))
                     ;			(:instance bit-basic-b (x (logand (bits x (1- j) 0) (bits y (1- j) 0))))
                                     )))))

 (local (defthm bits-logand-10
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
                                   (bits (logand x y) (1- j) 0))))
               :rule-classes ()
               :hints (("Goal" :in-theory (enable
                                           bits
                                           )
                        :use (bits-logand-9
                              (:instance mod-logand (n j)))))))

 (local (defthm bits-logand-11
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (+ (* (expt 2 j) (logand (bits x i j) (bits y i j)))
                              (bits (logand x y) (1- j) 0))))
               :rule-classes ()
               :hints (("Goal" :use (bits-logand-10

                     ;                 (:instance bits< (x (logand x y)) (i (1- j)) (j 0))
                                     ;yuck!
                                     (:instance or-dist-b
                                                (x (logand (bits x i j) (bits y i j)))
                                                (y (bits (logand x y) (1- j) 0))
                                                (n j)))))))

 (local (defthm bits-logand-12
               (implies (and (integerp x) (>= x 0)
                             (integerp y) (>= y 0)
                             (integerp i) (>= i j)
                             (integerp j) (> j 0))
                        (= (bits (logand x y) i 0)
                           (+ (* (expt 2 j) (bits (logand x y) i j))
                              (bits (logand x y) (1- j) 0))))
               :rule-classes ()
               :hints (("Goal" :use (
                                     (:instance bits-plus-bits (x (logand x y)) (n i) (p j) (m 0)))))))

 (defthm bits-logand
   (implies (and     ;(<= i j)
             (case-split (natp x)) ;drop?
             (case-split (natp y)) ;drop?
             (case-split (natp i))
             (case-split (natp j))
             )
            (equal (bits (logand x y) i j)
                   (logand (bits x i j) (bits y i j))))
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable bits)
                               '(ACL2::CANCEL_TIMES-EQUAL-CORRECT))
            :use (bits-logand-11
                  bits-logand-12
                  (:instance cancel-equal-*
                             (a (expt 2 j))
                             (r (logand (bits x i j) (bits y i j)))
                             (s (bits (logand x y) i j)))

                  (:instance mod-logand (n (1+ i)))
                  ))))
 )



;prove from bits-logand?
(defthm bitn-logand
  (implies (and (integerp x) ; (>= x 0)
                (integerp y) ; (>= y 0)
                (integerp n) (>= n 0)
                )
           (equal (bitn (logand x y) n)
                  (logand (bitn x n) (bitn y n))))
  :hints (("goal" :induct (op-dist-induct x y n))
	  ("subgoal *1/1" :use ( ;(:instance mod)
				(:instance bitn-rec-0)
				(:instance bitn-rec-0 (x y))
				(:instance bitn-rec-0 (x (logand x y)))))
	  ("subgoal *1/2" :use ((:instance bitn-rec-pos (n n))
				(:instance bitn-rec-pos (n n) (x y))
				(:instance bitn-rec-pos (n n) (x (logand x y)))
;				(:instance logand-fl)
                                ))))

(local (defthm bits-logior-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (+ (* (expt 2 j) (bits x i j))
			   (bits x (1- j) 0))
			(+ (* (expt 2 j) (bits y i j))
			   (bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits
                                     )
		  :use ((:instance mod-logior (n (1+ i)))
			(:instance expt-split (r 2) (i 1) (j i))
			(:instance bits-plus-bits (n i) (p j) (m 0))
			(:instance bits-plus-bits (x y) (n i) (p j) (m 0)))))))

(local (defthm bits-logior-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (logior (* (expt 2 j) (bits x i j))
				(bits x (1- j) 0))
			(logior (* (expt 2 j) (bits y i j))
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal"
           :use (bits-logior-1
;                 (:instance bits< (i (1- j)) (j 0))
;                 (:instance bits< (x y) (i (1- j)) (j 0))
                 (:instance or-dist-b (x (bits x i j)) (n j) (y (bits x (1- j) 0)))
                 (:instance or-dist-b (x (bits y i j)) (n j) (y (bits y (1- j) 0))))))))

(local (defthm bits-logior-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (logior (* (expt 2 j) (bits x i j))
				(* (expt 2 j) (bits y i j)))
			(logior (bits x (1- j) 0)
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal"
           :use (bits-logior-2
;                 (:instance expt-pos (x j))
)))))

(local (defthm bits-logior-5
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (* (expt 2 j) (logior (bits x i j) (bits y i j)))
			(bits (logior x y) (1- j) 0))))
    :otf-flg t
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits mod-logior
                                     )
           :use (bits-logior-4
                 (:instance or-dist-c (n j) (x (bits x i j)) (y (bits y i j))))))))

(local (defthm bits-logior-6
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(+ (* (expt 2 j) (logior (bits x i j) (bits y i j)))
		   (bits (logior x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal"
           :use (bits-logior-5
;                 (:instance bits< (x (logior x y)) (i (1- j)) (j 0))
                 (:instance or-dist-b
                            (x (logior (bits x i j) (bits y i j)))
                            (y (bits (logior x y) (1- j) 0))
                            (n j)))))))

(local (defthm bits-logior-7
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(+ (* (expt 2 j) (bits (logior x y) i j))
		   (bits (logior x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal" :use (
			(:instance bits-plus-bits (x (logior x y)) (n i) (p j) (m 0)))))))

(defthm bits-logior
    (implies (and ;(>= i j)
                  (case-split (natp x))
                  (case-split (natp y))
                  (case-split (natp i))
                  (case-split (natp j))
                  )
	     (equal (bits (logior x y) i j)
		    (logior (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bits ;natp
                                     )
                              '(;COLLECT-CONSTANTS-IN-<-OF-SUMS
;                                a4 a9
                                ACL2::CANCEL_TIMES-EQUAL-CORRECT ;unfortunate
                                CANCEL-COMMON-FACTORS-IN-EQUAL ;unfortunate
                                ;INTEGER-TIGHTEN-BOUND
                                ))
		  :use (bits-logior-6
			bits-logior-7
			(:instance cancel-equal-*
				   (a (expt 2 j))
				   (r (logior (bits x i j) (bits y i j)))
				   (s (bits (logior x y) i j)))
			(:instance mod-logior (n (1+ i)))
;			(:instance expt-pos (x j))
                        ))))

;someday prove from bits-logior (will have to generalize bits-logior?)?
(defthm bitn-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n)
                  (>= n 0))
	     (equal (bitn (logior x y) n)
                    (logior (bitn x n) (bitn y n))))
  :hints (("goal" :induct (op-dist-induct x y n))
	  ("subgoal *1/1" :use (;(:instance logior-mod)
				(:instance bitn-rec-0)
				(:instance bitn-rec-0 (x y))
				(:instance bitn-rec-0 (x (logior x y)))))
	  ("subgoal *1/2" :use ((:instance bitn-rec-pos (n n))
				(:instance bitn-rec-pos (n n) (x y))
				(:instance bitn-rec-pos (n n) (x (logior x y)))
				;(:instance logior-fl)
                                ))))

(defthm and-bits-a
    (implies (and (integerp x) (>= x 0)
		  (integerp k) (>= k 0))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ()
  :hints (("goal"  :in-theory (enable expt)
           :induct (or-dist-induct x k))
	  ("subgoal *1/1" :use ((:instance logand-def (i x) (j 1))
				(:instance mod012 (m x))
				(:instance bitn-rec-0)))
	  ("subgoal *1/2" :use ((:instance logand-def (i x) (j (expt 2 k)))
				(:instance mod-2*i (i (expt 2 (1- k))))
				(:instance fl-int (x (expt 2 (1- k))))
				(:instance bitn-rec-pos (n k))))))

(defthm and-bits-b
  (implies (and (integerp x) (>= x 0)
                (integerp k) (>= k 0))
           (= (logior x (expt 2 k))
              (+ x
                 (* (expt 2 k)
                    (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("goal"  :in-theory (enable expt) :induct (or-dist-induct x k))
	  ("subgoal *1/1" :use ((:instance logior-def (i x) (j 1))
				(:instance mod012 (m x))
				(:instance quot-mod (m x) (n 2))
				(:instance bitn-rec-0)))
	  ("subgoal *1/2" :use ((:instance logior-def (i x) (j (expt 2 k)))
				(:instance mod-2*i (i (expt 2 (1- k))))
				(:instance quot-mod (m x) (n 2))
				(:instance fl-int (x (expt 2 (1- k))))
				(:instance bitn-rec-pos (n k))))))

;move?
(local
 (defthm fl-2**n-1/2
    (implies (and (integerp n) (> n 0))
	     (= (fl (/ (1- (expt 2 n)) 2))
		(1- (expt 2 (1- n)))))
    :hints (("Goal" :in-theory (enable expt)))
  :rule-classes ()))

;move?
(local
 (defthm mod-2**n-1/2
   (implies (and (integerp n) (> n 0))
            (= (mod (1- (expt 2 n)) 2)
               1))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable expt)
            :use ((:instance mod-2*i+1 (i (1- (expt 2 (1- n)))))
                  (:instance mod012 (m (1- (expt 2 n)))))))))

(local
 (defthm logand-slice-<-0
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (> n 0)
                 (< x (expt 2 n)))
            (= (logand x (- (expt 2 n) 1))
               (bits x (1- n) 0)))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable logand-ones)
            :use (;(:instance logand-slice-<-0-1)
                  (:instance mod-does-nothing (m x) (n (expt 2 n))))))))

(local
 (defthm logand-slice-<-pos-1
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n))
                 (integerp k) (> k 0)
                 (< k n))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* 2 (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k)))))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable expt)
            :use ((:instance logand-def (i x) (j (- (expt 2 n) (expt 2 k))))
                  (:instance expt-weak-monotone (n k) (m n))
                  (:instance mod-2*i (i (- (expt 2 (1- n)) (expt 2 (1- k))))))))))

(local
(defthm logand-slice-<-pos-2
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits (fl (/ x 2)) (- n 2) (1- k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt)
           :use ((:instance logand-slice-<-pos-1))))))

(local
 (defthm logand-slice-<-pos-3
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n))
                 (integerp k) (> k 0)
                 (< k n)
                 (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
                    (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* (expt 2 k) (fl (/ (mod (fl (/ x 2)) (expt 2 (1- n))) (expt 2 (1- k)))))))
   :rule-classes ()
   :hints (("Goal" :in-theory (e/d ( bits) (bits-fl)) ;BOZO why?
            :use ((:instance logand-slice-<-pos-2))))))

;Looping rules in this lemma led to a discussion on the acl2-help list about looping rules (due to subterms
;not be simplified).
(local
 (defthm logand-slice-<-pos-4
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n)))
            (= (mod (fl (* 1/2 x)) (expt 2 (1- n)))
               (fl (* 1/2 x))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod-does-nothing (m (fl (/ x 2))) (n (expt 2 (1- n))))
                         (:instance fl-def-linear (x (/ x 2))))
            :in-theory (set-difference-theories
                        (enable expt)
                        '( ;mod-equal
                          mod-does-nothing
                           mod-upper-bound-2
                           mod-upper-bound-linear
                           mod-non-negative-linear
                           mod-bnd-1
;                           mod-bnd-2
                           mod-bnd-3
                           ))))))

(local
 (defthm logand-slice-<-pos-5
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n))
                 (integerp k) (> k 0)
                 (< k n)
                 (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
                    (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* (expt 2 k) (fl (/ (fl (/ x 2)) (expt 2 (1- k)))))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance logand-slice-<-pos-3)
                         (:instance logand-slice-<-pos-4))))))

(local
 (defthm logand-slice-<-pos-6
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n))
                 (integerp k) (> k 0)
                 (< k n)
                 (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
                    (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* (expt 2 k) (fl (/ x (expt 2 k))))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable expt)
            :use ((:instance logand-slice-<-pos-5)
                  (:instance fl/int-rewrite (x (/ x 2)) (n (expt 2 (1- k)))))))))

(local
(defthm logand-slice-<-pos-7
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n))
	     (= (fl (/ x (expt 2 k)))
		(bits x (1- n) k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
           :use ((:instance mod-does-nothing (m x) (n (expt 2 n))))))))

(local
(defthm logand-slice-<-pos
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (integerp k) (> k 0)
		  (< k n)
		  (= (logand (fl (/ x 2)) (- (expt 2 (1- n)) (expt 2 (1- k))))
		     (* (expt 2 (1- k)) (bits (fl (/ x 2)) (- n 2) (1- k)))))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-slice-<-pos-6)
			(:instance logand-slice-<-pos-7))))))

;move?
(local
 (defun and-bits-induct (x n k)
   (if (and (integerp k) (>= k 0))
       (if (= k 0)
           (list x n k)
         (and-bits-induct (fl (/ x 2)) (1- n) (1- k)))
     ())))

(local
 (defthm logand-slice-<
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (< x (expt 2 n))
                 (integerp k) (>= k 0)
                 (< k n))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* (expt 2 k) (bits x (1- n) k))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable expt)
            :induct (and-bits-induct x n k))
           ("Subgoal *1/1" :use ((:instance logand-slice-<-0)))
           ("Subgoal *1/2" :use ((:instance logand-slice-<-pos))))))

(local
 (defthm logand-slice-1
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (integerp k) (>= k 0)
                 (< k n))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (logand (mod x (expt 2 n)) (- (expt 2 n) (expt 2 k)))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance and-dist-d (x (- (expt 2 n) (expt 2 k))) (y x))
                         (:instance expt-weak-monotone (n k) (m n))
                         )))))

(local
 (defthm logand-slice-2
   (implies (and (integerp x) (>= x 0)
                 (integerp n) (>= n 0)
                 (integerp k) (>= k 0)
                 (< k n))
            (= (logand x (- (expt 2 n) (expt 2 k)))
               (* (expt 2 k) (bits (mod x (expt 2 n)) (1- n) k))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance logand-slice-1)
                         (:instance logand-slice-< (x (mod x (expt 2 n))))
                         (:instance mod-bnd-1 (m x) (n (expt 2 n)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
                         )))))

(defthm logand-slice
  (implies (and (integerp x) (>= x 0)
                (integerp n) (>= n 0)
                (integerp k) (>= k 0)
                (< k n))
           (= (logand x (- (expt 2 n) (expt 2 k)))
              (* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bits) ;yuck?
           :use ((:instance logand-slice-2)))))



;move these to logxor.lisp?
(encapsulate
 ()
 (local (defthm logxor-rewrite-1
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (logior (logand (fl (/ x 2)) (lnot (fl (/ y 2)) (1- n)))
                              (logand (fl (/ y 2)) (lnot (fl (/ x 2)) (1- n))))
                      (logior (logand (fl (/ x 2)) (fl (/ (lnot y n) 2)))
                              (logand (fl (/ y 2)) (fl (/ (lnot x n) 2))))))
          :rule-classes ()
          :hints (("Goal" :in-theory (e/d (bvecp) ( lnot))
                   :use ((:instance lnot-fl-original (k 1))
                         (:instance lnot-fl-original (k 1) (x y)))))))

 (local (defthm logxor-rewrite-2
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (logior (logand (fl (/ x 2)) (fl (/ (lnot y n) 2)))
                              (logand (fl (/ y 2)) (fl (/ (lnot x n) 2))))
                      (logior (fl (/ (logand x (lnot y n)) 2))
                              (fl (/ (logand y (lnot x n)) 2)))))
          :rule-classes ()
          :hints (("Goal" :in-theory (disable ;logand-fl-rewrite
                                      lnot)
                   :use ( ;(:instance logand-fl (y (lnot y n)))
;(:instance logand-fl (x y) (y (lnot x n)))
                         )))))

 (local (defthm logxor-rewrite-3
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (logior (logand (fl (/ x 2)) (lnot (fl (/ y 2)) (1- n)))
                              (logand (fl (/ y 2)) (lnot (fl (/ x 2)) (1- n))))
                      (logior (fl (/ (logand x (lnot y n)) 2))
                              (fl (/ (logand y (lnot x n)) 2)))))
          :rule-classes ()
          :hints (("Goal" :use ((:instance logxor-rewrite-1)
                                (:instance logxor-rewrite-2))))))

 (local (defthm logxor-rewrite-4
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (logior (fl (/ (logand x (lnot y n)) 2))
                              (fl (/ (logand y (lnot x n)) 2)))
                      (fl (/ (logior (logand x (lnot y n))
                                     (logand y (lnot x n)))
                             2))))
          :rule-classes ()
          :hints (("Goal" :use ( ;(:instance logior-fl
;                        (i (logand x (lnot y n)))
;                       (j (logand y (lnot x n))))
                                )))))

 (local (defthm logxor-rewrite-5
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (logior (logand (fl (/ x 2)) (lnot (fl (/ y 2)) (1- n)))
                              (logand (fl (/ y 2)) (lnot (fl (/ x 2)) (1- n))))
                      (fl (/ (logior (logand x (lnot y n))
                                     (logand y (lnot x n)))
                             2))))
          :rule-classes ()
          :hints (("Goal" :use ((:instance logxor-rewrite-3)
                                (:instance logxor-rewrite-4))))))

 (local (defthm logxor-rewrite-6
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n))
                        (= (logxor (fl (/ x 2)) (fl (/ y 2)))
                           (logior (logand (fl (/ x 2)) (lnot (fl (/ y 2)) (1- n)))
                                   (logand (fl (/ y 2)) (lnot (fl (/ x 2)) (1- n))))))
                   (= (fl (/ (logxor x y) 2))
                      (fl (/ (logior (logand x (lnot y n))
                                     (logand y (lnot x n)))
                             2))))
          :rule-classes ()
          :hints (("Goal" :use ((:instance logxor-rewrite-5)
                                (:instance fl-logxor-by-2 (i x) (j y)))))))



 (local (defthm logxor-rewrite-8
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (mod (logxor x y) 2)
                      (logior (logand (mod x 2) (lnot (mod y 2) 1))
                              (logand (mod y 2) (lnot (mod x 2) 1)))))
          :rule-classes ()
          :hints (("Goal" ;:in-theory (disable logxor)
                   :use ( ;(:instance logxor-mod (i x) (j y))
                         (:instance mod012 (m x))
                         (:instance mod012 (m y)))))))

 (local (defthm logxor-rewrite-9
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (mod (logxor x y) 2)
                      (logior (logand (mod x 2) (mod (lnot y n) 2))
                              (logand (mod y 2) (mod (lnot x n) 2)))))
          :rule-classes ()
          :hints (("Goal" :in-theory (disable lnot logxor)
                   :use ((:instance logxor-rewrite-8)
                         )))))

 (local (defthm logxor-rewrite-10
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (mod (logxor x y) 2)
                      (logior (mod (logand x (lnot y n)) 2)
                              (mod (logand y (lnot x n)) 2))))
          :rule-classes ()
          :hints (("Goal" ;:in-theory (disable logxor)
                   :use ((:instance logxor-rewrite-9)
                         )))))

 (local (defthm logxor-rewrite-11
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n)))
                   (= (mod (logxor x y) 2)
                      (mod (logior (logand x (lnot y n))
                                   (logand y (lnot x n)))
                           2)))
          :rule-classes ()
          :hints (("Goal" ;:in-theory (disable logxor)
                   :use ((:instance logxor-rewrite-10))))))

 (local (defthm logxor-rewrite-12
          (implies (and (integerp n) (> n 1)
                        (integerp x) (>= x 0) (< x (expt 2 n))
                        (integerp y) (>= y 0) (< y (expt 2 n))
                        (= (logxor (fl (/ x 2)) (fl (/ y 2)))
                           (logior (logand (fl (/ x 2)) (lnot (fl (/ y 2)) (1- n)))
                                   (logand (fl (/ y 2)) (lnot (fl (/ x 2)) (1- n))))))
                   (= (logxor x y)
                      (logior (logand x (lnot y n))
                              (logand y (lnot x n)))))
          :rule-classes ()
          :hints (("Goal" ;:in-theory (disable logxor)
                   :use ((:instance logxor-rewrite-6)
                         (:instance logxor-rewrite-11)
                         (:instance quot-mod
                                    (m (logxor x y))
                                    (n 2))
;			(:instance logxor-nat (i x) (j y))
                         (:instance quot-mod
                                    (m (logior (logand x (lnot y n))
                                               (logand y (lnot x n))))
                                    (n 2)))))))


;move?
 (local
  (defun logxor-induct (x y n)
    (if (and (integerp n) (>= n 1))
        (if (= n 1)
            (list x y)
          (logxor-induct (fl (/ x 2)) (fl (/ y 2)) (1- n)))
      ())))

 (local (defthm x01
          (implies (and (integerp x)
                        (>= x 0)
                        (< x 2))
                   (or (= x 0) (= x 1)))
          :rule-classes ()))

;move to logxor.lisp?
;it seems gross that this series uses lnot...
 (defthmd LOGXOR-REWRITE
   (implies (and (< x (expt 2 n))
                 (< y (expt 2 n))
                 (integerp n) (>= n 1) ;gen?
                 (integerp x) (>= x 0)
                 (integerp y) (>= y 0))
            (= (logxor x y)
               (logior (logand x (lnot y n))
                       (logand y (lnot x n)))))
   :hints (("Goal" :in-theory (disable lnot logxor)
            :induct (logxor-induct x y n))
           ("Subgoal *1/2" :in-theory (set-difference-theories
                                       (enable expt-split)
                                       '(a15))
            :use (logxor-rewrite-12))
           ("Subgoal *1/1" :in-theory (enable lnot)
            :use ((:instance x01)
                  (:instance x01 (x y))
                  (:instance lnot-fl-original (x 0) (k 1))))))
 )

;n is a free var
(defthmd logxor-rewrite-2
    ;; ! Do we really want to get rid of logxor?
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n)
		  (not (= n 0)))
	     (equal (logxor x y)
		    (logior (logand x (lnot y n))
			    (logand y (lnot x n)))))
    :rule-classes ((:rewrite :match-free :all))
    :hints (("Goal" :in-theory (enable bvecp)
             :use (logxor-rewrite))))


(defthm bitn-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp n))
                (case-split (>= n 0))
                )
           (equal (bitn (logxor x y) n)
                  (logxor (bitn x n) (bitn y n))))
  :hints (("Goal" :induct (op-dist-induct x y n))
	  ("Subgoal *1/1" :use ( ;(:instance logxor-mod (i x) (j y))
				(:instance bitn-rec-0)
				(:instance bitn-rec-0 (x y))
				(:instance bitn-rec-0 (x (logxor x y)))))
	  ("Subgoal *1/2" :use ((:instance bitn-rec-pos (n n))
				(:instance bitn-rec-pos (n n) (x y))
				(:instance bitn-rec-pos (n n) (x (logxor x y)))
                                ))))





(encapsulate
 ()

 (local (defthm bits-logxor-1
               (implies (and (integerp x) (>= x 0) (< x (expt 2 n))
                             (integerp y) (>= y 0) (< y (expt 2 n))
                             (integerp n) (>= n i)
                             (integerp i) (>= i j)
                             (integerp j) (>= j 0)
                             )
                        (= (bits (logxor x y) i j)
                           (logior (logand (bits x i j) (bits (lnot y n) i j))
                                   (logand (bits y i j) (bits (lnot x n) i j)))))
               :rule-classes ()
               :hints (("Goal" :in-theory (disable lnot-bvecp lnot bvecp)
                        :use (logxor-rewrite
                              lnot-bvecp
                              (:instance lnot-bvecp (x y))
                              (:instance bits-logior (x (logand x (lnot y n))) (y (logand y (lnot x n))))

                              (:instance bits-logand (y (lnot y n)))
                              (:instance bits-logand (x y) (y (lnot x n))))))))

 (local (defthm bits-logxor-2
               (implies (and (integerp x) (>= x 0) (< x (expt 2 n))
                             (integerp y) (>= y 0) (< y (expt 2 n))
                             (integerp n) (> n i)
                             (integerp i) (>= i j)
                             (integerp j) (>= j 0))
                        (= (bits (logxor x y) i j)
                           (logior (logand (bits x i j) (lnot (bits y i j) (1+ (- i j))))
                                   (logand (bits y i j) (lnot (bits x i j) (1+ (- i j)))))))
               :rule-classes ()
               :hints (("Goal" :in-theory (set-difference-theories
                                           (enable bvecp)
                                           '(lnot-bvecp lnot))
                        :use (bits-logxor-1
                              (:instance bits-lnot (n n))
                              (:instance bits-lnot (x y) (n n)))))))


 (local (defthm bits-logxor-aux
          (implies (and (bvecp x n) ; Free variable n is bound here
                        (bvecp y n)
                        (natp n)
                        (natp i)
                        (natp j)
                        (> n i)
                        (>= i j))
                   (equal (bits (logxor x y) i j)
                          (logxor (bits x i j) (bits y i j))))
          :rule-classes nil
          :hints (("Goal" :in-theory (e/d (bvecp) ( lnot-bvecp lnot))
                   :use (bits-logxor-2
                         (:instance logxor-rewrite (x (bits x i j)) (y (bits y i j)) (n (1+ (- i j))))
;                         (:instance bits<)
 ;                        (:instance bits< (x y))
                         )))))

;a nice fact?  make into a better lemma?
 (local (defthm hack1
               (implies (natp x)
                        (> (expt 2 x) x))

               :rule-classes ()))

 (defthm bits-logxor
   (implies (and (case-split (natp x))
                 (case-split (natp y))
                 (case-split (natp i))
                 (case-split (natp j))
                 ;(>= i j)
                 )
            (equal (bits (logxor x y) i j)
                   (logxor (bits x i j) (bits y i j))))
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable bvecp natp expt-split)
                               '())
            :use ((:instance hack1 (x (+ i x y)))
                  (:instance bits-logxor-aux (n (+ i x y)))))))
 )

