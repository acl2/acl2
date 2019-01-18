(in-package "RTL")

(include-book "definitions")
(local (include-book "bits"))
(local (include-book "log"))

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

; binary-cat lemmas
(local-defthm bvecp-0 (bvecp 0 k)
  :hints (("goal" :in-theory (enable bvecp))))

(encapsulate ()

  (defthmd cat-bvecp-2
    (implies (and (<= (+ a0 a1) a)
                  (case-split (integerp a)))
             (bvecp (cat x1 a1 x0 a0) a))))


(local-defthmd binary-cat-2
              (implies (and (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a1)
                            (natp a0))
                       (equal (cat x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0)))))
              :hints (("Goal" :in-theory (enable binary-cat))))


(local-defthmd bcevp-sum-2
              (implies (and (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0)))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-2)
                                    (:instance binary-cat-2)))))

(local-defthmd binary-cat-3
              (implies (and (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                               (x1 x2)
                                               (a1 a2)
                                               (x0 (cat x1 a1 x0 a0))
                                               (a0 (+ a0 a1)))
                                    (:instance binary-cat-2)
                                    (:instance bcevp-sum-2
                                               (a (+ a0 a1)))))))



(defthmd cat-bvecp-3
    (implies (and (<= (+ a0 a1 a2) a)
                  (case-split (integerp a)))
             (bvecp (cat x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-3
              (implies (and (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1))))
                              a))
              :hints (("Goal" :use ((:instance binary-cat-3)
                                    (:instance cat-bvecp-3)))))



(local-defthmd binary-cat-4
              (implies (and (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x3)
                                        (a1 a3)
                                        (x0 (cat x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2)))
                                    (:instance binary-cat-3)
                                    (:instance bcevp-sum-3
                                               (a (+ a0 a1 a2)))))))



(defthmd cat-bvecp-4
    (implies (and (<= (+ a0 a1 a2 a3) a)
                  (case-split (integerp a)))
             (bvecp (cat x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-4
              (implies (and (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-4)
                                    (:instance binary-cat-4)))))





(local-defthmd binary-cat-5
              (implies (and (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x4 a4 x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2)))
                                 (* x4 (expt 2 (+ a0 a1 a2 a3))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x4)
                                        (a1 a4)
                                        (x0 (cat x3 a3 x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2 a3)))
                                    (:instance binary-cat-4)
                                    (:instance bcevp-sum-4
                                               (a (+ a0 a1 a2 a3)))))))



(defthmd cat-bvecp-5
    (implies (and (<= (+ a0 a1 a2 a3 a4) a)
                  (case-split (integerp a)))
             (bvecp (cat x4 a4 x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-5
              (implies (and (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3 a4) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2)))
                                 (* x4  (expt 2 (+ a0 a1 a2 a3))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-5)
                                    (:instance binary-cat-5)))))





(local-defthmd binary-cat-6
              (implies (and (bvecp x5 a5)
                            (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a5)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0))
                       (equal (cat x5 a5 x4 a4 x3 a3 x2 a2 x1 a1 x0 a0)
                              (+ x0
                                 (* x1 (expt 2 a0))
                                 (* x2 (expt 2 (+ a0 a1)))
                                 (* x3 (expt 2 (+ a0 a1 a2)))
                                 (* x4 (expt 2 (+ a0 a1 a2 a3)))
                                 (* x5 (expt 2 (+ a0 a1 a2 a3 a4))))))
              :hints (("Goal" :use ((:instance binary-cat-2
                                        (x1 x5)
                                        (a1 a5)
                                        (x0 (cat x4 a4 x3 a3 x2 a2 x1 a1 x0 a0))
                                        (a0 (+ a0 a1 a2 a3 a4)))
                                    (:instance binary-cat-5)
                                    (:instance bcevp-sum-5
                                               (a (+ a0 a1 a2 a3 a4)))))))


(defthmd cat-bvecp-6
    (implies (and (<= (+ a0 a1 a2 a3 a4 a5) a)
                  (case-split (integerp a)))
             (bvecp (cat x5 a5 x4 a4 x3 a3 x2 a2  x1 a1 x0 a0) a))
    :hints (("Goal" :in-theory (enable cat-bvecp-2))))


(local-defthmd bcevp-sum-6
              (implies (and (bvecp x5 a5)
                            (bvecp x4 a4)
                            (bvecp x3 a3)
                            (bvecp x2 a2)
                            (bvecp x1 a1)
                            (bvecp x0 a0)
                            (natp a5)
                            (natp a4)
                            (natp a3)
                            (natp a2)
                            (natp a1)
                            (natp a0)
                            (equal (+ a0 a1 a2 a3 a4 a5) a))
                       (bvecp (+ x0
                                 (* x1  (expt 2 a0))
                                 (* x2  (expt 2 (+ a0 a1)))
                                 (* x3  (expt 2 (+ a0 a1 a2)))
                                 (* x4  (expt 2 (+ a0 a1 a2 a3)))
                                 (* x5  (expt 2 (+ a0 a1 a2 a3 a4))))
                              a))
              :hints (("Goal" :use ((:instance cat-bvecp-6)
                                    (:instance binary-cat-6)))))

;;;**********************************************************************
;;;			Radix-4 Booth Encoding
;;;**********************************************************************

(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))

(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
	(sum-theta (1- m) y))))

(defrule sum-theta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta m y)))
  :prep-lemmas (
    (defrule sum-theta-lemma-i
      (implies (and (not (zp m))
                    (integerp k)
                    (integerp y)
                    (<= 0 k)
                    (<= k m))
               (equal (sumbits y (* 2 k))
                      (+ (sum-theta k y)
                         (* (expt 2 (* 2 k))
                            (bitn y (+ -1 (* 2 k)))))))
      :rule-classes ()))
  :enable (sumbits-thm)
  :use (:instance sum-theta-lemma-i
                  (k m))
  :rule-classes ())

(defun bmux4 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (0  0)))

(local (defruled bmux4-reduce-to
  (implies (and (integerp zeta)
                (<= zeta 2)
                (<= -2 zeta)
                (integerp n)
                (bvecp x (+ -1 n))
                (>= n 0))
           (equal (bmux4 zeta x n)
                  (if (<= 0 zeta)
                      (* zeta x)
                    (+ -1 (expt 2 n)
                       (* zeta x)))))
  :enable (bits-lognot)
  :disable (acl2::|(lognot (* 2 x))|)
  :cases ((= zeta -1)
          (= zeta -2))
  :hints (
    ("subgoal 2" :cases ((>= n 1)))
    ("subgoal 1" :cases ((not (>= n 1))
                         (not (bvecp (* 2 x) n))))
    ("subgoal 1.1" :in-theory (enable bvecp)))))

(defun neg (x) (if (< x 0) 1 0))

(local (defrule bvecp-neg
  (bvecp (neg x) 1)
  :rule-classes (
    :rewrite
    (:linear :corollary (<= (neg x) 1)))))

(encapsulate ((zeta (i) t))
 (local (defun zeta (i) (declare (ignore i)) 0))
 (defthm zeta-bnd
     (and (integerp (zeta i))
	  (<= (zeta i) 2)
	  (>= (zeta i) -2))))

(local (defrule integerp-zeta
  (integerp (zeta i))
  :rule-classes :type-prescription))

(local (defrule zeta-bounds
  (and (>= (zeta i) -2) (<= (zeta i) 2))
  :rule-classes :linear))

(local (defrule natp-bmux4-zeta
  (implies
    (natp x)
    (natp (bmux4 (zeta i) x n)))
  :rule-classes :type-prescription))

(local (acl2::with-arith5-nonlinear-help (defrule bvecp-bmux4-zeta
  (implies
    (and (bvecp x (1- n)) (natp n))
    (bvecp (bmux4 (zeta i) x n) n))
  :enable (bmux4-reduce-to bvecp)
  :disable (bmux4))))

(local (defrule natp-bmux4-theta
  (implies
    (natp x)
    (natp (bmux4 (theta i y) x n)))
  :use (:functional-instance natp-bmux4-zeta
         (zeta (lambda (i) (theta i y))))
  :rule-classes :type-prescription))

(local (defrule bvecp-bmux4-theta
  (implies
    (and (bvecp x (1- n)) (natp n))
    (bvecp (bmux4 (theta i y) x n) n))
  :use (:functional-instance bvecp-bmux4-zeta
         (zeta (lambda (i) (theta i y))))))

(defun pp4 (i x n)
  (if (zerop i)
      (cat 1 1
	   (bitn (lognot (neg (zeta i))) 0) 1
	   (bmux4 (zeta i) x n) n)
    (cat 1 1
	 (bitn (lognot (neg (zeta i))) 0) 1
	 (bmux4 (zeta i) x n) n
	 0 1
	 (neg (zeta (1- i))) 1
	 0 (* 2 (1- i)))))

(defun sum-zeta (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 2 (1- m))) (zeta (1- m)))
       (sum-zeta (1- m)))))

(defun sum-pp4 (x m n)
  (if (zp m)
      0
    (+ (pp4 (1- m) x n)
       (sum-pp4 x (1- m) n))))

(acl2::with-arith5-nonlinear-help (defrule booth4-thm
  (implies (and (not (zp n))
                (not (zp m))
                (bvecp x (1- n)))
           (= (+ (expt 2 n)
                 (sum-pp4 x m n))
              (+ (expt 2 (+ n (* 2 m)))
                 (* x (sum-zeta m))
                 (- (* (expt 2 (* 2 (1- m))) (neg (zeta (1- m))))))))
  :prep-lemmas (
    (defrule pp4-reduce-to-1
      (implies (and (integerp n)
                    (integerp i)
                    (< 0 i)
                    (bvecp x (+ -1 n))
                    (> n 0))
               (equal (pp4 i x n)
                      (+ (* (- 3 (neg (zeta i))) (expt 2 (+ n (* 2 i))))
                         (* (bmux4 (zeta i) x n) (expt 2 (* 2 i)))
                         (* (neg (zeta (+ -1 i))) (expt 2 (+ -2 (* 2 i)))))))
      :use (:instance binary-cat-6
             (x5 1) (a5 1)
             (x4 (bitn (lognot (neg (zeta i))) 0)) (a4 1)
             (x3 (bmux4 (zeta i) x n)) (a3 n)
             (x2 0) (a2 1)
             (x1 (neg (zeta (1- i)))) (a1 1)
             (x0 0) (a0 (+ -2 (* 2 i))))
      :disable (bmux4))
    (defrule pp4-reduce-to-2
      (implies (and (integerp n)
                    (bvecp x (+ -1 n))
                    (> n 0))
               (equal (pp4 0 x n)
                      (+ (* (- 3 (neg (zeta 0))) (expt 2 n))
                         (bmux4 (zeta 0) x n))))
      :enable (binary-cat-3)
      :disable (bmux4)))
  :enable (bits-lognot bmux4-reduce-to)
  :disable (pp4 bmux4)
  :rule-classes ()))

(defun pp4-theta (i x y n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (theta i y))) 0) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (theta i y))) 0) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4-theta (1- m) x y n)
       (sum-pp4-theta x y (1- m) n))))

(defrule booth4-corollary-1
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (+ (expt 2 n)
		   (sum-pp4-theta x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (not (zp n))
                    (not (zp m))
                    (bvecp x (1- n))
                    (bvecp y (1- (* 2 m))))
               (= (+ (expt 2 n)
                     (sum-pp4-theta x y m n))
                  (+ (expt 2 (+ n (* 2 m)))
                     (* x (sum-theta m y))
                     (- (* (expt 2 (* 2 (1- m))) (neg (theta (1- m) y)))))))
      :use (:functional-instance booth4-thm
             (zeta (lambda (i) (theta i y)))
             (sum-zeta (lambda (m) (sum-theta m y)))
             (pp4  (lambda (i x n) (pp4-theta i x y n)))
             (sum-pp4  (lambda (x m n) (sum-pp4-theta x y m n))))))
  :use sum-theta-lemma
  :rule-classes ())

(defun pp4p-theta (i x y n)
   (if (zerop i)
       (cat (bitn (lognot (neg (theta i y))) 0) 1
            (neg (theta i y)) 1
            (neg (theta i y)) 1
	    (bmux4 (theta i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (theta i y))) 0) 1
	  (bmux4 (theta i y) x n) n
	  0 1
	  (neg (theta (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4p-theta (x y m n)
  (if (zp m)
      0
    (+ (pp4p-theta (1- m) x y n)
       (sum-pp4p-theta x y (1- m) n))))

(defrule booth4-corollary-2
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
		  (bvecp y (1- (* 2 m))))
	     (= (bits (sum-pp4p-theta x y m n) (1- (+ n (* 2 m))) 0)
                (* x y)))
  :prep-lemmas (
    (defrule pp4p-theta-1
      (implies (not (zp k))
               (equal (pp4p-theta k x y n)
                      (pp4-theta k x y n)))
      :disable (bmux4 neg theta))
    (defrule pp4p-theta-3
      (implies (and (not (zp n)) (bvecp x (1- n)))
               (equal (pp4p-theta 0 x y n)
                      (+ (pp4-theta 0 x y n) (expt 2 n))))
      :use (:instance binary-cat-4
             (x3 (bitn (lognot (neg (theta 0 y))) 0)) (a3 1)
             (x2 (neg (theta 0 y))) (a2 1)
             (x1 (neg (theta 0 y))) (a1 1)
             (x0 (bmux4 (theta 0 y) x n)) (a0 n))
      :enable (binary-cat-3)
      :disable (bmux4 theta))
    (defrule pp4p-theta-4
      (implies (and (not (zp n))
                    (bvecp x (1- n))
                    (not (zp m)))
               (equal (sum-pp4p-theta x y m n)
                      (+ (expt 2 n) (sum-pp4-theta x y m n))))
      :disable (pp4-theta pp4p-theta)
      :hints (("Subgoal *1/2" :cases ((= m 1))))))
  :enable (bvecp-monotone)
  :use (booth4-corollary-1
        (:instance bits-tail (x (* x y)) (i (1- (+ n (* 2 m)))))
        (:instance bvecp-product (m (1- n)) (n (1- (* 2 m))))
        (:instance bits-plus-mult-2
         (n (1- (+ n (* 2 m)))) (m 0) (k (+ n (* 2 m))) (x (* x y)) (y 1)))
  :rule-classes ())


(encapsulate ()

(local (include-book "arithmetic-5/top" :dir :system))

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)|
                          |(mod (+ x (mod a b)) y)|
                          simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                          ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| mod-theorem-one-b))

(defun theta (i y)
  (+ (bitn y (1- (* 2 i)))
     (bitn y (* 2 i))
     (* -2 (bitn y (1+ (* 2 i))))))

(defun sum-theta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (theta (1- m) y))
	(sum-theta (1- m) y))))

(defthm sum-theta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 2 m))))
	     (equal y (sum-theta m y)))
  :rule-classes ())

(defund mag (i y)
  (if (member (bits y (1+ (* 2 i)) (1- (* 2 i))) '(3 4))
      2
    (if (member (bits y (* 2 i) (1- (* 2 i))) '(1 2))
        1
      0)))

(defthm mag-0-1-2
  (member (mag i y) '(0 1 2))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable mag))))

(defund nbit (i y)
  (bitn y (1+ (* 2 i))))

(defthm nbit-0-1
  (member (nbit i y) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable nbit))))

(defthmd theta-rewrite
  (implies (and (natp y) (natp i))
           (equal (theta i y)
                  (if  (= (nbit i y) 1)
                       (- (mag i y))
                       (mag i y))))
  :hints (("Goal" :in-theory (enable nbit mag)
                  :use ((:instance bitn-0-1 (x y) (n (1- (* 2 i))))
                        (:instance bitn-0-1 (x y) (n (* 2 i)))
                        (:instance bitn-0-1 (x y) (n (1+ (* 2 i))))
			(:instance bitn-plus-bits (x y) (n (1+ (* 2 i))) (m (1- (* 2 i))))
			(:instance bitn-plus-bits (x y) (n (* 2 i)) (m (1- (* 2 i))))))))

(defund bmux4p (i x y n)
  (if  (= (nbit i y) 1)
       (bits (lognot (* (mag i y) x)) (1- n) 0)
       (* (mag i y) x)))

(defthmd bvecp-bmux4p
  (implies (and (not (zp n))
                (bvecp x (1- n)))
	   (bvecp (bmux4p i x y n) n))
  :hints (("Goal" :nonlinearp t
                  :use (mag-0-1-2
                        (:instance bits-bounds (x (lognot (* (mag i y) x))) (i (1- n)) (j 0)))
                  :in-theory (enable bmux4p bvecp))))

(local-in-theory (disable ACL2::|(lognot (* 2 x))|))

(defthmd bmux4p-rewrite
  (implies (and (not (zp n))
                (not (zp m))
	        (bvecp x (1- n))
	        (bvecp y (1- (* 2 m)))
		(natp i)
		(< i m))
           (equal (bmux4p i x y n)
                  (+ (* (theta i y) x)
                     (* (1- (expt 2 n)) (nbit i y)))))
  :hints (("Goal" :use (mag-0-1-2 nbit-0-1)
                  :in-theory (enable bvecp bmux4p theta-rewrite bits-lognot))))

(defund pp4p (i x y n)
  (if (zerop i)
      (cat (if (= (nbit 0 y) 0) 1 0) 1
           (nbit 0 y) 1
           (nbit 0 y) 1
           (bmux4p 0 x y n) n)
    (cat 1 1
         (lognot (nbit i y)) 1
         (bmux4p i x y n) n
         0 1
         (nbit (1- i) y) 1
         0 (* 2 (1- i)))))

(local-in-theory (disable theta))

(defthmd pp4p0-rewrite
  (implies (and (not (zp n))
                (not (zp m))
	        (bvecp x (1- n))
	        (bvecp y (1- (* 2 m))))
           (equal (pp4p 0 x y n)
                  (+ (expt 2 (+ n 2))
                     (* (theta 0 y) x)
                     (- (nbit 0 y)))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bvecp pp4p bmux4p-rewrite binary-cat)
                  :use ((:instance bvecp-bmux4p (i 0))
		        (:instance nbit-0-1 (i 0))))))

(defthmd pp4p-rewrite
  (implies (and (not (zp n))
                (not (zp m))
	        (bvecp x (1- n))
	        (bvecp y (1- (* 2 m)))
                (not (zp i))
                (< i m))
           (equal (pp4p i x y n)
                  (+ (expt 2 (+ n (* 2 i) 1))
                     (expt 2 (+ n (* 2 i)))
                     (* (expt 2 (* 2 i)) (theta i y) x)
                     (* (expt 2 (* 2 (1- i))) (nbit (1- i) y))
                     (- (* (expt 2 (* 2 i)) (nbit i y))))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bvecp pp4p bmux4p-rewrite binary-cat)
                  :use (bvecp-bmux4p nbit-0-1
		        (:instance nbit-0-1 (i (1- i)))))))

(defun sum-pp4p (x y m n)
  (if (zp m)
      0
    (+ (pp4p (1- m) x y n)
       (sum-pp4p x y (1- m) n))))

(local-defthmd booth-lemma-1
  (implies (and (not (zp n))
                (not (zp m))
	        (bvecp x (1- n))
	        (bvecp y (1- (* 2 m)))
                (not (zp k))
                (<= k m))
           (equal (sum-pp4p x y k n)
                  (+ (* x (sum-theta k y))
                     (expt 2 (+ n (* 2 k)))
                     (- (* (expt 2 (* 2 (1- k))) (nbit (1- k) y))))))
  :hints (("Goal" :induct (sum-pp4p x y k n))
          ("Subgoal *1/2" :use (pp4p0-rewrite))
          ("Subgoal *1/1" :use (pp4p0-rewrite (:instance pp4p-rewrite (i (1- k)))) :nonlinearp t)))

(defthmd booth4-corollary-3
  (implies (and (not (zp n))
                (not (zp m))
	        (bvecp x (1- n))
	        (bvecp y (1- (* 2 m))))
           (equal (sum-pp4p x y m n)
                  (+ (* x y) (expt 2 (+ n (* 2 m))))))
  :hints (("Goal" :in-theory (enable nbit)
                  :use (sum-theta-lemma (:instance booth-lemma-1 (k m))))))

)

;;;**********************************************************************
;;;                Statically Encoded Multiplier Arrays
;;;**********************************************************************

(defun m-mu-chi (i mode)
  (cond ((equal mode 'mu)
         (if (zp i)  1
           (cons (cons 1  i) 1)))
        ((equal mode 'chi)
         (if (zp i)  0
           (cons (cons 1  i) 0)))))

(mutual-recursion
 (defun mu (i y)
   (declare (xargs :measure (m-mu-chi i 'mu)))
     (+ (bits y (1+ (* 2 i)) (* 2 i)) (chi i y)))

 (defun chi (i y)
   (declare (xargs :measure (m-mu-chi i 'chi)))
   (if (zp i)
       0
     (if (>= (mu (1- i) y) 3)
	 1
       0))))

(local (defrule chi-bound
  (<= (chi i y) 1)
  :expand (chi i y)
  :rule-classes :linear))

(local (defrule bits2-bound
  (implies
    (<= i (1+ j))
    (<= (bits x i j) 3))
  :cases ((bvecp (bits x i j) 2))
  :rule-classes :linear))

(local (defrule mu-bound
  (<= (mu i y) 4)
  :rule-classes :linear))

(defun phi (i y)
  (if (= (bits (mu i y) 1 0) 3)
      -1
    (bits (mu i y) 1 0)))

(defrule phi-bnd
    (member (phi i y) '(-1 0 1 2)))

(local (defrule phi-bnd-linear
  (and (>= (phi i y) -1)
       (<= (phi i y) 2))
  :rule-classes :linear))

(defun sum-odd-powers-of-2 (m)
  (if (zp m)
      0
    (+ (expt 2 (1- (* 2 m)))
       (sum-odd-powers-of-2 (1- m)))))

(local (acl2::with-arith5-nonlinear-help (defruled sum-odd-powers-of-2-equal
  (implies (natp m)
           (equal (sum-odd-powers-of-2 m)
                  (* 2/3 (1- (expt 2 (* 2 m)))))))))

(acl2::with-arith5-nonlinear-help (defrule chi-m
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal (chi m y) 0))
  :prep-lemmas (
    (defrule lemma
      (implies (and (natp m)
                    (natp y)
                    (<= (bits y (+ -1 (* 2 m)) 0) (sum-odd-powers-of-2 m)))
	       (equal (chi m y) 0))
      :induct (sub1-induction m)
      :enable (sum-odd-powers-of-2-equal)
      :hints (
        ("subgoal *1/2"
          :use (:instance bits-plus-bits
                 (x y)
                 (n (+ -1 (* 2 m)))
                 (m 0)
                 (p (+ -2 (* 2 m))))
         :cases ((= (bits y (+ -1 (* 2 m)) (+ -2 (* 2 m))) 3))))))
  :cases ((bvecp y (* 2 m)))
  :hints (("subgoal 2" :in-theory (enable sum-odd-powers-of-2-equal bvecp)))
  :rule-classes()))

(defrule phi-m-1
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (>= (phi (1- m) y) 0))
  :disable (sum-odd-powers-of-2 sum-odd-powers-of-2-equal)
  :use (chi-m)
  :cases ((zp m)
          (bvecp (mu (1- m) y) 2)
          (= (mu (1- m) y) 4))
  :hints (("subgoal 4" :in-theory (enable bvecp)))
  :rule-classes())

(defun sum-phi (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (phi (1- m) y))
	(sum-phi (1- m) y))))

(defrule sum-phi-lemma
    (implies (and (natp m)
		  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (equal y (sum-phi m y)))
  :prep-lemmas (
    (defruled phi-equal
      (implies
        (natp m)
        (equal (phi m y)
               (+ (* -4 (chi (1+ m) y))
                  (bits y (+ 1 (* 2 m)) (* 2 m))
                  (chi m y))))
      :cases ((= (mu m y) 4)
              (= (mu m y) 3)
              (= (mu m y) 2)))
    (defrule lemma
      (implies (natp m)
               (equal (bits y (+ -1 (* 2 m)) 0)
                      (+ (sum-phi m y)
                         (* (chi m y) (expt 2 (* 2 m))))))
      :induct (sub1-induction m)
      :enable (phi-equal)
      :disable (phi)
      :hints (
        ("subgoal *1/2" :cases (
          (= (bits y (+ -1 (* 2 m)) 0)
             (+ (bits y (+ -3 (* 2 m)) 0)
                (* (bits y (+ -1 (* 2 m)) (+ -2 (* 2 m))) (expt 2 (+ -2 (* 2 m))))))))
        ("subgoal *1/2.2" :use (:instance bits-plus-bits
                                 (x y)
                                 (n (+ -1 (* 2 m)))
                                 (m 0)
                                 (p (+ -2 (* 2 m))))))
        :rule-classes ()))
  :use (lemma chi-m)
  :cases ((bvecp y (* 2 m)))
  :hints (("subgoal 2" :in-theory (enable sum-odd-powers-of-2-equal bvecp)))
  :rule-classes ())

(defun pp4-phi (i x y n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (phi i y))) 0) 1
	    (bmux4 (phi i y) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (phi i y))) 0) 1
	  (bmux4 (phi i y) x n) n
	  0 1
	  (neg (phi (1- i) y)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-phi (x y m n)
  (if (zp m)
      0
    (+ (pp4-phi (1- m) x y n)
       (sum-pp4-phi x y (1- m) n))))

(defrule static-booth
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (1- n))
                  (natp y)
		  (<= y (sum-odd-powers-of-2 m)))
	     (= (+ (expt 2 n)
		   (sum-pp4-phi x y m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (not (zp n))
                    (not (zp m))
                    (bvecp x (1- n)))
               (= (+ (expt 2 n)
                     (sum-pp4-phi x y m n))
                  (+ (expt 2 (+ n (* 2 m)))
                     (* x (sum-phi m y))
                     (- (* (expt 2 (* 2 (1- m))) (neg (phi (1- m) y)))))))
      :disable (phi bmux4 neg)
      :use (:functional-instance booth4-thm
             (zeta (lambda (i) (phi i y)))
             (sum-zeta (lambda (m) (sum-phi m y)))
             (pp4  (lambda (i x n) (pp4-phi i x y n)))
             (sum-pp4  (lambda (x m n) (sum-pp4-phi x y m n))))
      :rule-classes ()))
  :disable (sum-pp4-phi sum-phi phi sum-odd-powers-of-2)
  :use (lemma phi-m-1 sum-phi-lemma)
  :rule-classes ())

;;;**********************************************************************
;;;                Encoding Redundant Representations
;;;**********************************************************************

(defun gamma (i a b c)
   (if (zp i)
       (bitn c 0)
     (logior (bitn  a (+ -1  (* 2 i)))
 	     (bitn  b (+ -1  (* 2 i))))))

(local (defrule bvecp-gamma
  (bvecp (gamma i a b c) 1)
  :rule-classes (
    (:forward-chaining :trigger-terms ((gamma i a b c)))
    (:type-prescription :corollary (natp (gamma i a b c)))
    (:linear :corollary (<= (gamma i a b c) 1)))))

(defun delta (i a b c d)
  (if (zp i)
      (bitn d 0)
    (logand (logior (logand (bitn a (+ -2 (* 2 i)))
			    (bitn b (+ -2 (* 2 i))))
		    (logior (logand (bitn a (+ -2 (* 2 i)))
				    (gamma (1- i) a b c))
			    (logand (bitn b (+ -2 (* 2 i)))
				    (gamma (1- i) a b c))))
	    (lognot (logxor (bitn a (1- (* 2 i)))
			    (bitn b (1- (* 2 i))))))))

(local (defrule bvecp-delta
  (bvecp (delta i a b c d) 1)
  :disable (gamma logand-commutative acl2::|(logand y x)|)
  :rule-classes (
    (:forward-chaining :trigger-terms ((delta i a b c d)))
    (:type-prescription :corollary (natp (delta i a b c d)))
    (:linear :corollary (<= (delta i a b c d) 1)))))

(local (defrule delta-0
  (implies (bvecp d 1) (equal (delta 0 a b c d) d))))

(defun psi (i a b c d)
  (if (not (natp i))
      0
    (+ (bits a (1+ (* 2 i)) (* 2 i))
       (bits b (1+ (* 2 i)) (* 2 i))
       (gamma i a b c)
       (delta i a b c d)
       (* -4 (+ (gamma (1+ i) a b c)
                (delta (1+ i) a b c d))))))

(defrule psi-m-1
    (implies (and (natp m)
                  (>= m 1)
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (and (equal (gamma m a b c) 0)
		  (equal (delta m a b c d) 0)
		  (>= (psi (1- m) a b c d) 0)))
  :enable (bvecp-monotone)
  :disable (gamma delta)
  :expand ((gamma m a b c) (delta m a b c d))
  :cases ((not (= (bitn a (- (* 2 m) 1)) 0))
          (not (= (bitn b (- (* 2 m) 1)) 0)))
  :rule-classes ())

(defun sum-psi (m a b c d)
   (if (zp m)
       0
     (+ (* (expt 2 (* 2 (1- m))) (psi (1- m) a b c d))
	(sum-psi (1- m) a b c d))))

(defrule sum-psi-lemma
    (implies (and (natp m)
                  (<= 1 m) ;; add
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1))
	     (equal (+ a b c d) (sum-psi m a b c d)))
  :prep-lemmas (
    (defrule lemma-k
      (implies (and (natp k)
                    (bvecp c 1)
                    (bvecp d 1))
               (equal (+ (bits a (+ -1 (* 2 k)) 0)
                         (bits b (+ -1 (* 2 k)) 0)
                         c d)
                      (+ (sum-psi k a b c d)
                         (* (expt 2 (* 2 k))
                            (+ (gamma k a b c)
                               (delta k a b c d))))))
      :disable (delta)
      :induct (sum-psi k a b c d)
      :hints (
        ("subgoal *1/2" :use (
          (:instance bits-plus-bits
            (x a)
            (n (+ -1 (* 2 k)))
            (m 0)
            (p (+ -2 (* 2 k))))
          (:instance bits-plus-bits
            (x b)
            (n (+ -1 (* 2 k)))
            (m 0)
            (p (+ -2 (* 2 k)))))))
    :rule-classes ()))
  :enable (bvecp-monotone)
  :disable (sum-psi gamma delta)
  :cases ((not (equal (gamma m a b c) 0))
          (not (equal (delta m a b c d) 0)))
  :hints (
    ("subgoal 3" :use (:instance lemma-k (k m)))
    ("subgoal 2" :in-theory (enable gamma))
    ("subgoal 1" :in-theory (enable delta)))
  :rule-classes ())

(defruled psi-bnd
  (and (integerp (psi i a b c d))
       (<= (psi i a b c d) 2)
       (>= (psi i a b c d) -2))
  :prep-lemmas (
    (defrule bits-expand-specific
      (implies (natp i)
               (equal (bits x (+ 1 (* 2 i)) (* 2 i))
                      (+ (* 2 (bitn x (+ 1 (* 2 i))))
                         (bitn x (* 2 i)))))
      :use (:instance bits-plus-bits
             (n (+ 1 (* 2 i)))
             (m (* 2 i))
             (p (+ 1 (* 2 i))))))
  :disable (gamma delta)
  :expand ((gamma (+ 1 i) a b c)
           (delta (+ 1 i) a b c d))
  :use ((:instance bitn-0-1 (x a) (n (1+ (* 2 i))))
        (:instance bitn-0-1 (x b) (n (1+ (* 2 i))))
        (:instance bitn-0-1 (x a) (n (* 2 i)))
        (:instance bitn-0-1 (x b) (n (* 2 i)))))

(defun pp4-psi (i x a b c d n)
   (if (zerop i)
       (cat 1 1
	    (bitn (lognot (neg (psi i a b c d))) 0) 1
	    (bmux4 (psi i a b c d) x n) n)
     (cat 1 1
	  (bitn (lognot (neg (psi i a b c d))) 0) 1
	  (bmux4 (psi i a b c d) x n) n
	  0 1
	  (neg (psi (1- i) a b c d)) 1
	  0 (* 2 (1- i)))))

(defun sum-pp4-psi (x a b c d m n)
  (if (zp m)
      0
    (+ (pp4-psi (1- m) x a b c d n)
       (sum-pp4-psi x a b c d (1- m) n))))

(defrule redundant-booth
    (implies (and (natp m)
                  (<= 1 m)
                  (not (zp n))
		  (bvecp x (1- n))
		  (bvecp a (- (* 2 m) 2))
		  (bvecp b (- (* 2 m) 2))
		  (bvecp c 1)
		  (bvecp d 1)
		  (= y (+ a b c d)))
	     (= (+ (expt 2 n)
		   (sum-pp4-psi x a b c d m n))
		(+ (expt 2 (+ n (* 2 m)))
		   (* x y))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (not (zp n))
                    (not (zp m))
                    (bvecp x (1- n))
                    (bvecp a (- (* 2 m) 2))
                    (bvecp b (- (* 2 m) 2))
                    (bvecp c 1)
                    (bvecp d 1))
               (= (+ (expt 2 n)
                     (sum-pp4-psi x a b c d m n))
                  (+ (expt 2 (+ n (* 2 m)))
                     (* x (sum-psi m a b c d))
                     (- (* (expt 2 (* 2 (1- m))) (neg (psi (1- m) a b c d)))))))
      :disable (psi bmux4 neg)
      :use (:functional-instance booth4-thm
             (zeta (lambda (i) (psi i a b c d)))
             (sum-zeta (lambda (m) (sum-psi m a b c d)))
             (pp4  (lambda (i x n) (pp4-psi i x a b c d n)))
             (sum-pp4  (lambda (x m n) (sum-pp4-psi x a b c d m n))))
      :rule-classes ()))
  :disable (sum-pp4-psi sum-psi psi)
  :use (lemma psi-m-1 sum-psi-lemma)
  :rule-classes ())

;;;**********************************************************************
;;;			Radix-8 Booth Encoding
;;;**********************************************************************

(defun eta (i y)
  (+ (bitn y (1- (* 3 i)))
     (bitn y (* 3 i))
     (* 2 (bitn y (1+ (* 3 i))))
     (* -4 (bitn y (+ 2 (* 3 i))))))

(defun sum-eta (m y)
   (if (zp m)
       0
     (+ (* (expt 2 (* 3 (1- m))) (eta (1- m) y))
	(sum-eta (1- m) y))))

(defrule sum-eta-lemma
    (implies (and (not (zp m))
		  (bvecp y (1- (* 3 m))))
	     (equal y (sum-eta m y)))
  :prep-lemmas (
    (defrule sum-eta-lemma-i
      (implies (and (not (zp m))
                    (integerp k)
                    (integerp y)
                    (<= 0 k)
                    (<= k m))
               (equal (sumbits y (* 3 k))
                      (+ (sum-eta k y)
                         (* (expt 2 (* 3 k))
                            (bitn y (+ -1 (* 3 k)))))))
       :hints (("subgoal *1/2" :expand ((sumbits y (* 3 k))
                                        (sumbits y (+ -1 (* 3 k)))
                                        (sumbits y (+ -2 (* 3 k))))))
      :rule-classes ()))
  :enable (sumbits-thm)
  :use (:instance sum-eta-lemma-i
         (k m))
  :rule-classes ())

(defun bmux8 (zeta x n)
  (case zeta
    (1  x)
    (-1 (bits (lognot x) (1- n) 0))
    (2  (* 2 x))
    (-2 (bits (lognot (* 2 x)) (1- n) 0))
    (3  (* 3 x))
    (-3 (bits (lognot (* 3 x)) (1- n) 0))
    (4  (* 4 x))
    (-4 (bits (lognot (* 4 x)) (1- n) 0))
    (0  0)))

(local (acl2::with-arith5-nonlinear-help (defruled bmux8-reduce-to
  (implies (and (integerp zeta)
                (<= zeta 4)
                (<= -4 zeta)
                (integerp n)
                (bvecp x (+ -2 n))
                (>= n 0))
           (equal (bmux8 zeta x n)
                  (if (<= 0 zeta)
                      (* zeta x)
                    (+ -1 (expt 2 n)
                       (* zeta x)))))
  :enable (bits-lognot)
  :cases ((= n 1)
          (>= n 2))
  :disable (acl2::|(lognot (* 2 x))|)
  :hints (
    ("subgoal 2" :in-theory (enable bvecp))
    ("subgoal 1" :cases ((>= zeta 0)))
    ("subgoal 1.2" :cases ((bvecp (* (- zeta) x) n)))
    ("subgoal 1.2.2" :in-theory (enable bvecp))))))

(encapsulate ((xi (i) t))
 (local (defun xi (i) (declare (ignore i)) 0))
 (defthm xi-bnd
     (and (integerp (xi i))
	  (<= (xi i) 4)
	  (>= (xi i) -4))))

(local (defrule integerp-xi
  (integerp (xi i))
  :rule-classes :type-prescription))

(local (defrule xi-bounds
  (and (>= (xi i) -4) (<= (xi i) 4))
  :rule-classes :linear))

(local (defrule natp-bmux8-xi
  (implies
    (natp x)
    (natp (bmux8 (xi i) x n)))
  :rule-classes :type-prescription))

(local (acl2::with-arith5-nonlinear-help (defrule bvecp-bmux8-xi
  (implies
    (and (bvecp x (+ -2 n)) (natp n))
    (bvecp (bmux8 (xi i) x n) n))
  :enable (bmux8-reduce-to bvecp)
  :disable (bmux8))))

(local (defrule natp-bmux8-eta
  (implies
    (natp x)
    (natp (bmux8 (eta i y) x n)))
  :use (:functional-instance natp-bmux8-xi
         (xi (lambda (i) (eta i y))))
  :rule-classes :type-prescription))

(local (defrule bvecp-bmux8-eta
  (implies
    (and (bvecp x (+ -2 n)) (natp n))
    (bvecp (bmux8 (eta i y) x n) n))
  :use (:functional-instance bvecp-bmux8-xi
         (xi (lambda (i) (eta i y))))))

(defun pp8 (i x n)
  (if (zerop i)
      (cat 3 2
	   (bitn (lognot (neg (xi i))) 0) 1
	   (bmux8 (xi i) x n) n)
    (cat 3 2
	 (bitn (lognot (neg (xi i))) 0) 1
	 (bmux8 (xi i) x n) n
	 0 2
	 (neg (xi (1- i))) 1
	 0 (* 3 (1- i)))))

(defun sum-xi (m)
  (if (zp m)
      0
    (+ (* (expt 2 (* 3 (1- m))) (xi (1- m)))
       (sum-xi (1- m)))))

(defun sum-pp8 (x m n)
  (if (zp m)
      0
    (+ (pp8 (1- m) x n)
       (sum-pp8 x (1- m) n))))


(acl2::with-arith5-nonlinear-help (defrule booth8-thm
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2)))
	     (= (+ (expt 2 n)
		   (sum-pp8 x m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x (sum-xi m))
		   (- (* (expt 2 (* 3 (1- m))) (neg (xi (1- m))))))))
  :prep-lemmas (
    (defrule pp8-reduce-to-1
      (implies (and (integerp n)
                    (integerp i)
                    (< 0 i)
                    (bvecp x (+ -2 n))
                    (> n 0))
               (equal (pp8 i x n)
                     (+ (* (- 7 (neg (xi i))) (expt 2 (+ n (* 3 i))))
                        (* (bmux8 (xi i) x n) (expt 2 (* 3 i)))
                        (* (neg (xi (+ -1 i))) (expt 2 (+ -3 (* 3 i)))))))
      :use (:instance binary-cat-6
        (x5 3) (a5 2)
        (x4 (bitn (lognot (neg (xi i))) 0)) (a4 1)
        (x3 (bmux8 (xi i) x n)) (a3 n)
        (x2 0) (a2 2)
        (x1 (neg (xi (1- i)))) (a1 1)
        (x0 0) (a0 (+ -3 (* 3 i))))
      :disable (bmux8))
    (defrule pp8-reduce-to-2
      (implies (and (integerp n)
                    (bvecp x (+ -2 n))
                    (> n 0))
               (equal (pp8 0 x n)
                      (+ (* (- 7 (neg (xi 0))) (expt 2 n))
                         (bmux8 (xi 0) x n))))
      :enable (binary-cat-3)
      :disable (bmux8)))
  :enable (bits-lognot bmux8-reduce-to)
  :disable (pp8 bmux8)
  :rule-classes ()))

(defun pp8-eta (i x y n)
  (if (zerop i)
      (cat 3 2
	   (bitn (lognot (neg (eta i y))) 0) 1
	   (bmux8 (eta i y) x n) n)
    (cat 3 2
	 (bitn (lognot (neg (eta i y))) 0) 1
	 (bmux8 (eta i y) x n) n
	 0 2
	 (neg (eta (1- i) y)) 1
	 0 (* 3 (1- i)))))

(defun sum-pp8-eta (x y m n)
  (if (zp m)
      0
    (+ (pp8-eta (1- m) x y n)
       (sum-pp8-eta x y (1- m) n))))

(defrule booth8-corollary
    (implies (and (not (zp n))
		  (not (zp m))
		  (bvecp x (- n 2))
		  (bvecp y (1- (* 3 m))))
	     (= (+ (expt 2 n)
		   (sum-pp8-eta x y m n))
		(+ (expt 2 (+ n (* 3 m)))
		   (* x y))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (not (zp n))
                    (not (zp m))
                    (bvecp x (+ -2 n))
                    (bvecp y (1- (* 3 m))))
               (= (+ (expt 2 n)
                     (sum-pp8-eta x y m n))
                  (+ (expt 2 (+ n (* 3 m)))
                     (* x (sum-eta m y))
                     (- (* (expt 2 (* 3 (1- m))) (neg (eta (1- m) y)))))))
      :use (:functional-instance booth8-thm
             (xi (lambda (i) (eta i y)))
             (sum-xi (lambda (m) (sum-eta m y)))
             (pp8  (lambda (i x n) (pp8-eta i x y n)))
             (sum-pp8  (lambda (x m n) (sum-pp8-eta x y m n))))))
  :use sum-eta-lemma
  :rule-classes ())
