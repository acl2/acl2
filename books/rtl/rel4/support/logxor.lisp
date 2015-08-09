(in-package "ACL2")

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(include-book "ground-zero")
(local (include-book "logeqv"))
(local (include-book "logorc1"))
(local (include-book "lognot"))
(local (include-book "../arithmetic/top"))

(defthm logxor-integerp-type
  (integerp (logxor i j))
  :rule-classes :type-prescription)

(defthm logxor-0
  (implies (case-split (integerp i))
           (equal (logxor 0 i)
                  i))
  :hints (("goal" :in-theory (enable logxor))))

(defthm logxor-non-negative-integer-type-prescription
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (<= 0 (logxor i j))
                (integerp (logxor i j))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logxor))))

(defthm logxor-non-negative
  (implies (and (<= 0 i)
                (<= 0 j)
                )
           (<= 0 (logxor i j)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("goal" :in-theory (enable logxor))))

(defthm logxor-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (integerp (* 1/2 (logxor i j)))
                  (or (and (integerp (* 1/2 i))
                           (integerp (* 1/2 j)))
                      (and (not (integerp (* 1/2 j)))
                           (not (integerp (* 1/2 i)))))))
  :hints (("goal" :in-theory (enable logxor))))


(defthm logxor-commutative
  (equal (logxor j i)
         (logxor i j))
  :hints (("goal" :in-theory (enable logxor))))

(defthm logxor-with-non-integer-arg
  (implies (not (integerp i))
           (and (equal (logxor i j)
                       (ifix j))
                (equal (logxor j i)
                       (ifix j))))
  :hints (("goal" :in-theory (enable logxor))))

;do we really want to go to lognot?
(defthm logxor-with-an-arg-of-minus-one
  (implies (case-split (integerp i))
           (equal (logxor -1 i)
                  (lognot i)))
  :hints (("goal" :in-theory (enable logxor))))

(defthmd floor-logxor-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (floor (logxor i j) 2)
                  (logxor (floor i 2) (floor j 2))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable logxor)
                              '(lognot logeqv floor)))))

(defthm fl-logxor-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logxor i j)))
                  (logxor (fl (* 1/2 i)) (fl (* 1/2 j)))))
  :hints (("goal" :in-theory (enable logxor))))

(defthm mod-logxor-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (mod (logxor i j) 2)
                  (logxor (mod i 2) (mod j 2))))
  :hints (("Goal" :in-theory (enable mod-by-2))))



(defthmd logxor-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logxor i j)
                  (+ (* 2 (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logxor (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logxor t t))))
  :hints (("goal" :use (:instance fl-mod-equal
                                  (x (logxor i j))
                                  (y (+ (* 2 (logxor (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logxor (mod i 2) (mod j 2)))))
           :in-theory (enable mod-by-2))))

;i'm not sure which way this rule should go but note that both parts of this rule rewrite to the same rhs
(defthm lognot-logxor
  (and (equal (logxor (lognot i) j)
              (lognot (logxor i j)))
       (equal (logxor j (lognot i))
              (lognot (logxor i j))))
  :hints (("goal" :in-theory (enable logxor ))))

(defthm logxor-associative
  (equal (logxor (logxor i j) k)
         (logxor i (logxor j k)))
  :hints (("subgoal *1/2" :use ( ;(:instance logxor-assoc-1)
                                (:instance fl-mod-equal
                                           (x (logxor (logxor i j) k))
                                           (y (logxor i (logxor j k))))))
          ("goal" :in-theory (enable logxor-def mod-by-2)
           :induct ( logand-three-args-induct i j k))
          ))

(defthm logxor-commutative-2
  (equal (logxor j i k)
         (logxor i j k))
  :hints (("Goal" :in-theory (disable LOGXOR-ASSOCIATIVE
                                      logxor-commutative)
           :use (LOGXOR-ASSOCIATIVE
                 logxor-commutative
                 (:instance LOGXOR-ASSOCIATIVE (j i) (i j))))))

(defthm logxor-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logxor i j k)
                  (logxor (logxor i j) k))))

(defthm logxor-self
  (equal (logxor i i) 0)
  :hints (("goal" :in-theory (enable logxor))))

(defthmd logxor-def-rewrite
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                )
           (equal (logxor x y)
                  (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
                     (logxor (mod x 2) (mod y 2)))))
  :hints (("Goal" :in-theory (enable logxor-def)))
  :rule-classes ((:definition :controller-alist ((binary-logxor t t)))))

;gen?
(defthm logxor-upper-bound-tight
  (implies (and (< i (expt 2 n))
                (< j (expt 2 n))
                (integerp i) (>= i 0)
                (integerp j) (>= j 0)
                (integerp n) (>= n 0)
                )
           (<= (logxor i j) (1- (expt 2 n))))
  :hints (("Goal" :induct (op-dist-induct i j n))
	  ("Subgoal *1/2" :in-theory (set-difference-theories
                                      (enable expt-split
                                              )
                                      '(a15))
           :use ((:instance logxor-def)
                 (:instance mod012 (x i))
                 (:instance mod012 (x j))))))

;change var names
(defthm logxor-upper-bound
  (implies (and (< i (expt 2 n))
                (< j (expt 2 n))
                (integerp i) (>= i 0)
                (integerp j) (>= j 0)
                (integerp n) (>= n 0)
                )
           (< (logxor i j) (expt 2 n)))
  :hints (("Goal" :in-theory (disable logxor-upper-bound-tight)
           :use (:instance  logxor-upper-bound-tight))))

(defthm logxor-bvecp
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n) ;gen?
		  )
	     (bvecp (logxor x y) n))
  :hints (("Goal" :in-theory (enable bvecp))))