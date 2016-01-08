(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(include-book "markstein")
(local (include-book "basic"))
(local (include-book "float"))
(local (include-book "round"))

;; The following lemmas from arithmetic-5 have given me trouble:

(local (in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|)))

(defund h-excps (d p)
  (if (zp d)
      ()
    (cons (- 2 (* (expt 2 (- 1 p)) d))
          (h-excps (1- d) p))))

(local-defthm h-1
  (implies (and (integerp p)
                (integerp d)
                (> p 1)
                (> d 0)
                (<= d (expt 2 (1- p))))
           (> (* (expt 2 (- 1 p)) d) 0))
  :rule-classes ())

(local-defthm h-2
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x 0)
                (<= y z))
           (<= (* x y) (* x z)))
  :rule-classes ())

(local-defthm h-3
  (implies (and (integerp p)
                (integerp d)
                (> p 1)
                (> d 0)
                (<= d (expt 2 (1- p)))
                (rationalp (expt 2 (- 1 p)))
                (>= (expt 2 (- 1 p)) 0)
                (rationalp (expt 2 (1- p))))
           (<= (* (expt 2 (- 1 p)) d) (* (expt 2 (- 1 p)) (expt 2 (1- p)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance h-2 (x (expt 2 (- 1 p))) (y d) (z (expt 2 (1- p))))))))

(local-defthm h-4
  (implies (and (integerp p)
                (integerp d)
                (> p 1)
                (> d 0)
                (<= d (expt 2 (1- p))))
           (<= (* (expt 2 (- 1 p)) d) 1))
  :rule-classes ()
  :hints (("Goal" :use (h-3))))

(local-defthm h-5
  (implies (and (integerp p)
                (integerp d)
                (> p 1)
                (> d 0)
                (<= d (expt 2 (1- p))))
           (= (expo (- 2 (* (expt 2 (- 1 p)) d))) 0))
  :rule-classes ()
  :hints (("Goal" :use (h-1 h-4
                        (:instance expo-unique (x (- 2 (* (expt 2 (- 1 p)) d))) (n 0))))))

(local-defthm h-6
  (implies (and (integerp p)
                (integerp d)
                (> p 1)
                (> d 0)
                (<= d (expt 2 (1- p))))
           (exactp (- 2 (* (expt 2 (- 1 p)) d)) p))
  :rule-classes ()
  :hints (("Goal" :use (h-5)
                  :in-theory (enable exactp2))))

(local-defthm h-7
  (implies (and (rationalp b)
                (integerp p)
                (integerp d)
                (> p 1)
                (<= 1 b)
                (< b 2)
                (> d 0)
                (<= d (expt 2 (1- p)))
                (exactp b p)
                (> b (- 2 (* (expt 2 (- 1 p)) d))))
           (>= b (- 2 (* (expt 2 (- 1 p)) (1- d)))))
  :rule-classes ()
  :hints (("Goal" :use (h-5 h-6
                        (:instance fp+2 (x (- 2 (* (expt 2 (- 1 p)) d))) (y b) (n p))))))

(defun natp-induct (n)
  (if (zp n)
      n
    (natp-induct (1- n))))

(local-defthm h-8
  (implies (and (rationalp b)
                (integerp p)
                (integerp d)
                (> p 1)
                (<= 1 b)
                (< b 2)
                (>= d 0)
                (<= d (expt 2 (1- p)))
                (exactp b p)
                (not (member b (h-excps d p))))
           (< b (- 2 (* (expt 2 (- 1 p)) d))))
  :rule-classes ()
  :hints (("Goal" :induct (natp-induct d))
          ("Subgoal *1/1" :in-theory (enable h-excps))
          ("Subgoal *1/2" :use (h-7) :in-theory (enable h-excps))))

(local-defthm h-9
  (implies (and (integerp p)
                (> p 1))
           (and (< (expt 2 (- (1+ p))) 1/2)
                (< (expt 2 (- (1+ p))) 1)
                (< (expt 2 (- (1+ p))) (expt 2 (- p)))))
  :rule-classes ())

(local-defthm h-10
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (>= yp 1)
                (< yp (1+ (expt 2 (- (1+ p))))))
           (and (< yp 2)
                (< yp (1+ (expt 2 (- p))))))
  :rule-classes ()
  :hints (("Goal" :use h-9
                  :in-theory
                  #!acl2(disable normalize-factors-gather-exponents
                                 simplify-products-gather-exponents-<
                                 |(< (expt x n) (expt x m))|
                                 expt-is-increasing-for-base->-1))))

(local-defthm h-11
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (> yp (- 1 (expt 2 (- (1+ p))))))
           (>= yp 1/2))
  :rule-classes ()
  :hints (("goal" :use h-9
                  :in-theory
                  #!acl2(disable normalize-factors-gather-exponents
                                 simplify-products-gather-exponents-<
                                 |(< (expt x n) (expt x m))|
                                 expt-is-increasing-for-base->-1))))

(local-defthm h-12
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (>= yp 1)
                (< yp (1+ (expt 2 (- (1+ p))))))
           (= (rne yp p) 1))
  :rule-classes ()
  :hints (("Goal" :use (h-10
                        (:instance exactp-2**n (n 0) (m p))
                        (:instance rne-down (x yp) (a 1) (n p))))))

(local-defthm h-14
  (implies (and (integerp p)
                (> p 1))
           (= (expt 2 (- p)) (* 2 (expt 2 (- (1+ p))))))
  :rule-classes ())

(local-defthm h-15
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (< yp 1)
                (> yp (- 1 (expt 2 (- (1+ p))))))
           (and (rationalp (fp- 1 p))
                (= (fp+ (fp- 1 p) p) 1)
                (> (fp- 1 p) 0)
                (exactp (fp- 1 p) p)
                (> yp (+ (fp- 1 p) (expt 2 (- (expo (fp- 1 p)) p))))))
  :rule-classes ()
  :hints (("goal" :use (h-9 h-10 h-14
                        (:instance exactp-2**n (n 0) (m p))
                        (:instance exactp-fp- (x 1) (n p))
                        (:instance expo-unique (x (fp- 1 p)) (n -1)))
                  :in-theory
                  #!acl2(disable normalize-factors-gather-exponents
                                 simplify-products-gather-exponents-<
                                 |(< (expt x n) (expt x m))|
                                 expt-is-increasing-for-base->-1))))

(local-defthm h-16
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (< yp 1)
                (> yp (- 1 (expt 2 (- (1+ p))))))
           (= (rne yp p) 1))
  :rule-classes ()
  :hints (("goal" :use (h-15
                        (:instance rne-up (x yp) (a (fp- 1 p)) (n p))))))

(local-defthm h-17
  (implies (and (rationalp yp)
                (integerp p)
                (> p 1)
                (< (abs (- 1 yp)) (expt 2 (- (1+ p)))))
           (= (rne yp p) 1))
  :rule-classes ()
  :hints (("goal" :use (h-16 h-12))))

(local-defthm h-18
  (let ((y (rne yp p)))
    (implies (and (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 yp)) ep))
             (< (abs (- 1 y)) (expt 2 (- p)))))
  :rule-classes ()
  :hints (("goal" :use (h-17))))

(local-defthm h-19
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (> b 0)
                (<= (abs (- 1 (* b yp))) ep))
           (and (<= (* b yp) (+ 1 ep))
                (>= (* b yp) (- 1 ep))))
  :rule-classes ())

(local-defthm h-20
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (> x 0)
                (<= y z))
           (<= (/ y x) (/ z x)))
  :rule-classes ())

(local-defthm h-21
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (rationalp (* b yp))
                (rationalp (+ 1 ep))
                (rationalp (- 1 ep))
                (> b 0)
                (<= (abs (- 1 (* b yp))) ep))
           (and (<= (/ (* b yp) b) (/ (+ 1 ep) b))
                (>= (/ (* b yp) b) (/ (- 1 ep) b))))
  :rule-classes ()
  :hints (("Goal" :use (h-19
                        (:instance h-20 (x b) (y (* b yp)) (z (+ 1 ep)))
                        (:instance h-20 (x b) (z (* b yp)) (y (- 1 ep))))
                  :in-theory (theory 'minimal-theory))))

(local-defthm h-22
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (> b 0)
                (<= (abs (- 1 (* b yp))) ep))
           (and (<= yp (/ (+ 1 ep) b))
                (>= yp (/ (- 1 ep) b))))
  :rule-classes ()
  :hints (("Goal" :use (h-21))))

(local-defthm h-23
  (implies (and (rationalp b)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1))
           (>= b (1+ (expt 2 (- 1 p)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp+2 (x 1) (y b) (n p)))
                  :in-theory (enable exactp2))))

(local-defthm h-24
  (implies (and (integerp p)
                (> p 1))
           (< (expt 2 (- (1+ p))) (expt 2 (- 1 p))))
  :rule-classes ())

(local-defthm h-25
  (implies (and (rationalp b)
                (rationalp ep)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1)
                (< ep (expt 2 (- (1+ p)))))
           (> b (+ 1 ep)))
  :rule-classes ()
  :hints (("Goal" :use (h-23 h-24)
                  :in-theory (theory 'minimal-theory))))

(local-defthm h-26
  (implies (and (rationalp b)
                (rationalp x)
                (> b 1)
                (> b x))
           (< (/ x b) 1))
  :rule-classes ())

(local-defthm h-27
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1)
                (< ep (expt 2 (- (1+ p))))
                (<= (abs (- 1 (* b yp))) ep))
           (< yp 1))
  :rule-classes ()
  :hints (("Goal" :use (h-22 h-25
                        (:instance h-26 (x (+ 1 ep)))))))

(local-defthm h-28
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1)
                (< ep (expt 2 (- (1+ p))))
                (<= (abs (- 1 (* b yp))) ep))
           (<= (expo yp) -1))
  :rule-classes ()
  :hints (("Goal" :use (h-27
                        (:instance expo<= (x yp) (n -1))))))

(local-defthm h-29
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1)
                (< ep (expt 2 (- (1+ p))))
                (<= (abs (- 1 (* b yp))) ep))
           (<= (expt 2 (- (expo yp) p))
               (expt 2 (- (1+ p)))))
  :rule-classes ()
  :hints (("Goal" :use (h-28))))

(local-defthm h-30
  (implies (and (rationalp b)
                (rationalp yp)
                (rationalp ep)
                (integerp p)
                (> p 1)
                (exactp b p)
                (> b 1)
                (< ep (expt 2 (- (1+ p))))
                (<= (abs (- 1 (* b yp))) ep))
           (<= (abs (- yp (rne yp p)))
               (expt 2 (- (1+ p)))))
  :rule-classes ()
  :hints (("Goal" :use (h-29
                        (:instance rne-diff (x yp) (n p)))
                  :in-theory (theory 'minimal-theory))))

(local-defthm h-31
  (let ((d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp ep)
                  (integerp p))
             (<= (* (expt 2 (* 2 p)) ep) d)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable cg))))

(local-defthm h-32
  (let ((d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp ep)
                  (rationalp (* (expt 2 (* 2 p)) ep))
                  (rationalp (expt 2 (* 2 p)))
                  (rationalp d)
                  (> (expt 2 (* 2 p)) 0)
                  (integerp p))
             (<= (/ (* (expt 2 (* 2 p)) ep) (expt 2 (* 2 p))) (/  d (expt 2 (* 2 p))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance h-20 (x (expt 2 (* 2 p))) (y (* (expt 2 (* 2 p)) ep)) (z (cg (* (expt 2 (* 2 p)) ep))))))))

(local-defthm h-33
  (let ((d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp ep)
                  (integerp p))
             (<= ep (* (expt 2 (- (* 2 p))) d))))
  :rule-classes ()
  :hints (("Goal" :use (h-32))))

(local-defthm h-34
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (> x 0)
                (< y z))
           (< (* x y) (* x z)))
  :rule-classes ())

(local-defthm h-35
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp z)
                (>= x 0)
                (<= y z))
           (<= (* y x) (* z x)))
  :rule-classes ())

(local-defthm h-36
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp d)
                (< 0 b)
                (< b d)
                (<= 0 a)
                (<= a c)
                (< 0 c))
           (< (* a b) (* c d)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance h-35 (x b) (y a) (z c))
                        (:instance h-34 (x c) (y b) (z d)))
                  :in-theory (theory 'minimal-theory))))

(local-defthm h-39
  (implies (and (rationalp ep)
                (integerp p)
                (> p 1)
                (< ep (expt 2 (- (1+ p)))))
           (< (* (expt 2 (* 2 p)) ep) (expt 2 (1- p))))
  :rule-classes ())

(local-defthm h-40
  (implies (and (rationalp ep)
                (integerp p)
                (> p 1)
                (rationalp b)
                (rationalp ep)
                (<= (abs (- 1 (* b yp))) ep)
                (< ep (expt 2 (- (1+ p)))))
           (<= 0 (* (expt 2 (* 2 p)) ep)))
  :rule-classes ())

(local (acl2::with-arith5-nonlinear-help (defthm h-41
  (let ((d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (<= 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (and (<= 0 d)
                  (<= d (expt 2 (1- p))))))
  :rule-classes ()
  :hints (("Goal" :use (h-39 h-40
                        (:instance n>=cg-linear (n (expt 2 (1- p))) (x (* (expt
                                                                           2 (* 2 p)) ep)))))))))


(local-defthm h-42
  (let ((y (rne yp p))
        (d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (< 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (< (* b (abs (- yp y)))
                (* (expt 2 (- (1+ p))) (- 2 (* (expt 2 (- 1 p)) d))))))
  :rule-classes ()
  :hints (("Goal" :use (h-30 h-41
                        (:instance h-8 (d (cg (* (expt 2 (* 2 p)) ep))))
                        (:instance h-36 (a (abs (- yp (rne yp p))))
                                        (c (expt 2 (- (1+ p))))
                                        (d (- 2 (* (expt 2 (- 1 p)) (cg (* (expt 2 (* 2 p)) ep))))))))))

(local-defthm h-43
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp b)
                (< 1 b))
           (<= (abs (+ x (* b y))) (+ (abs x) (* b (abs y)))))
  :rule-classes ())

(local-defthm h-44
(let ((y (rne yp p)))
    (implies (and (rationalp b)
                  (< 1 b)
                  (rationalp yp)
                  (integerp p)
                  (> p 1))
             (<= (abs (- 1 (* b y)))
                 (+ (abs (- 1 (* b yp))) (* b (abs (- yp y)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance h-43 (x (- 1 (* b yp))) (y (- yp (rne yp p))))))))

(local-defthm h-45
  (let ((y (rne yp p))
        (d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (< 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (< (abs (- 1 (* b y))) (expt 2 (- p)))))
  :rule-classes ()
  :hints (("Goal" :use (h-33 h-42 h-44))))

(defthm harrison-lemma
  (let ((y (rne yp p))
        (d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (<= 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (< (abs (- 1 (* b y))) (expt 2 (- p)))))
  :rule-classes ()
  :hints (("Goal" :use (h-17 h-45))))
