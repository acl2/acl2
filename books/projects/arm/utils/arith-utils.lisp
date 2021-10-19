;; Cuong Chau <ckc8687@gmail.com>

;; October 2021

(in-package "RTL")

(include-book "macros")
(include-book "rtl/rel11/lib/top-alt" :dir :system)

;; ======================================================================

(defthmd integerp-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (* x y)))
  :rule-classes :type-prescription)

(defthm rationalp-abs
  (implies (rationalp x)
           (rationalp (abs x)))
  :rule-classes :type-prescription)

(defthmd integerp-abs
  (implies (integerp x)
           (integerp (abs x)))
  :rule-classes :type-prescription)

(defthmd abs-of-zero
  (equal (equal (abs x) 0)
         (equal x 0)))

(defthmd int+1<=
  (implies (and (< x y)
                (integerp x)
                (integerp y))
           (<= (1+ x) y)))

;; EXPT

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthm expt-lemma-1
    (implies (and (<= 1 (* x (expt r i)))
                  (<= 1 x)
                  (< x r)
                  (rationalp x)
                  (rationalp r)
                  (integerp i))
             (<= 0 i))
    :rule-classes nil)

  (defthm expt-lemma-2
    (implies (and (integerp (* x (expt 2 i)))
                  (not (integerp (* x (expt 2 j))))
                  (integerp x)
                  (integerp i)
                  (integerp j))
             (< j i))
    :rule-classes nil))

(local (arith-5-for-rtl))

(defthm expt-lemma-3
  (implies (and (rationalp r)
                (<= 1 r)
                (natp i))
           (<= 1 (expt r i)))
  :rule-classes :linear)

(defthm expt-lemma-4a
  (implies (and (<= 1 x)
                (< x r)
                (<= 1 y)
                (< y r)
                (rationalp x)
                (rationalp y)
                (rationalp r)
                (integerp i)
                (integerp j))
           (equal (equal (* x (expt r i)) (* y (expt r j)))
                  (and (equal x y)
                       (equal i j))))
  :hints (("Goal"
           :nonlinearp t
           :use ((:instance expt-lemma-1
                            (i (- i j)))
                 (:instance expt-lemma-3
                            (i (1- (- i j)))))))
  :rule-classes nil)

(defthm expt-lemma-4b
  (implies (and (<= 2 r)
                (<= 1 x)
                (< x r)
                (<= 1 y)
                (< y r)
                (rationalp x)
                (rationalp y)
                (rationalp r)
                (integerp i)
                (integerp j))
           (equal (< (* x (expt r i)) (* y (expt r j)))
                  (or (< i j)
                      (and (equal i j)
                           (< x y)))))
  :hints (("Goal"
           :nonlinearp t
           :use ((:instance expt-lemma-1
                            (i (- i j)))
                 (:instance expt-lemma-3
                            (i (1- (- i j)))))))
  :rule-classes nil)

(defthm expt-lemma-5
  (implies (and (< x (expt r i))
                (<= 1 r)
                (<= i j)
                (rationalp r)
                (integerp i)
                (integerp j))
           (< x (expt r j)))
  :rule-classes :linear)

(defthmd-nl expt-lemma-6
  (implies (and (< x (expt r (- i)))
                (< 0 r)
                (rationalp r))
           (< (* x (expt r i))
              1))
  :rule-classes :linear)

(defthmd-nl expt-lemma-7
  (implies (and (< x (expt 2 n))
                (integerp n))
           (< (+ (expt 2 n) x)
              (expt 2 (1+ n))))
  :rule-classes :linear)

(defthmd-nl expt-lemma-8
  (implies (and (bvecp x n1)
                (bvecp y n2)
                (natp n1)
                (integerp n2))
           (< (+ (* x (expt 2 n2)) y)
              (expt 2 (+ n1 n2))))
  :rule-classes :linear)

(defthmd expt-lemma-9
  (implies (and (integerp i)
                (integerp j)
                (<= i j))
           (<= (expt 2 i) (expt 2 j)))
  :rule-classes :linear)

;; LOGXOR

(defthm natp-logxor
  (implies (and (natp x)
                (natp y))
           (natp (logxor x y)))
  :hints (("Goal" :in-theory (enable logxor)))
  :rule-classes :type-prescription)

(defthm logxor-of-bits-<=-1
  (implies (and (<= 0 x)
                (<= x 1)
                (<= 0 y)
                (<= y 1))
           (<= (logxor x y) 1))
  :hints (("Goal" :in-theory (enable logxor
                                     lognot
                                     logand
                                     logior)))
  :rule-classes :linear)

(defthmd logxor-of-bits-rewrite
  (implies (and (bitp x)
                (bitp y))
           (equal (logxor x y)
                  (if (equal x y) 0 1))))

;; MOD

(defthm mod-=-0-is-0
  (implies (and (acl2-numberp x)
                (< (abs x) n))
           (equal (equal (mod x n) 0)
                  (equal x 0))))

(defthmd mod-integerp-lemma
  (implies (and (equal (mod x n) (mod y n))
                (rationalp x)
                (integerp y)
                (integerp n))
           (integerp x)))

(defthmd-nl mod-equality-preserved
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (< (abs (- x y)) n))
           (equal (equal (mod x n) (mod y n))
                  (equal x y))))

;; Other lemmas

(defthmd-nl arith-1
  (implies (and (<= a 1/2)
                (<= 1 x)
                (< x 2)
                (<= 1 y)
                (rationalp a)
                (rationalp x)
                (rationalp y))
           (< (* a x) y))
  :rule-classes :linear)

