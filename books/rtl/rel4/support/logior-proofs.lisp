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

;the order of these matters (lognot should come late)
(local (include-book "logand"))
(local (include-book "lognot"))
(local (include-book "../arithmetic/top")) ;try

(local (in-theory (enable evenp)))

;split?
(defthm logior-with-non-integer-arg
  (implies (not (integerp i))
           (and (equal (logior i j)
                       (ifix j))
                (equal (logior j i)
                       (ifix j))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-0
  (implies (case-split (integerp j))
           (equal (logior 0 j)
                  j))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-commutative
  (equal (logior j i)
         (logior i j))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-associative
  (equal (logior (logior i j) k)
         (logior i (logior j k)))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-commutative-2
  (equal (logior j i k)
         (logior i j k))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logior i j k)
                  (logior (logior i j) k))))

(defthm logior-with-an-arg-of-minus-one
  (implies (case-split (integerp i))
           (equal (logior -1 i) -1))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-negative-integerp-type
  (and (implies (and (<= 0 i)
                     (<= 0 j))
                (and (integerp (logior i j))
                     (<= 0 (logior i j)))))
  :rule-classes ( :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-negative
  (and (implies (and (<= 0 i)
                     (<= 0 j))
                (<= 0 (logior i j)))))

(defthm logior-equal-0
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (equal (logior i j) 0)
                  (and (equal i 0) (equal j 0))))
  :hints (("goal" :in-theory (enable logior))))

(defthm logior-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (integerp (* 1/2 (logior i j)))
                  (and (integerp (* 1/2 i))
                       (integerp (* 1/2 j)))))
  :hints (("goal" :in-theory (enable logior))))

(defthm logior-negative-1
  (implies (and (< i 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< (logior i j) 0)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-negative-2
  (implies (and (< j 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< (logior i j) 0)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-negative-3
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< (logior i j) 0)
                  (or (< i 0)
                      (< j 0))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-positive
  (implies (and (<= i 0)
                (<= j 0)
                )
           (<= (logior i j) 0))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-self
  (implies (case-split (integerp i))
           (equal (logior i i) i))
    :hints (("Goal" :in-theory (enable logior))))

(defthm logior-simp-1
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logior (* 2 i) (* 2 j))
                  (* 2 (logior i j))))
  :hints (("Goal" :in-theory (enable logior))))




(defthm logior-positive
  (implies (and (< 0 i)
                (< 0 j)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< 0 (logior i j))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-positive-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (< 0 (logior i j))
                  (and (<= 0 i)
                       (<= 0 j)
                       (or (< 0 i)
                           (< 0 j)))))
  :hints (("Goal" :in-theory (enable logior))))


(defthm logior-negative-5
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< -1 (logior i j))
                  (AND (< -1 I) (< -1 J))
                  ))
  :hints (("Goal" :cases ((equal j -1) (equal i -1))
           :in-theory (enable logior))))

(defthm logior-i-lognot-i
  (implies (case-split (integerp i))
           (equal (logior i (lognot i))
                  -1))
  :hints (("goal" :in-theory (enable logior)
           :induct (log-induct i (lognot i)))))

;move? odd...
(defthm fl-expression-rewrites-to-last-bit
  (implies (integerp i)
           (equal (+ I (* -2 (FL (* 1/2 I))))
                  (if (evenp i)
                      0
                    1))))

(defthm fl-logior-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logior i j)))
                  (logior (fl (/ i 2)) (fl (/ j 2)))))
  :hints (("goal" :in-theory (enable logior))))


(defthm floor-logior-by-2
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (floor (logior i j) 2)
                    (logior (floor i 2) (floor j 2)))))

(defthm mod-logior-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (mod (logior i j) 2)
                  (logior (mod i 2) (mod j 2))))
  :hints (("goal" :in-theory (enable mod-by-2))))

(defthmd logior-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logior i j)
                  (+ (* 2 (logior (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logior (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logior t t))))
  :hints (("goal"; :in-theory (enable  mod)
           :use ((:instance mod-fl-2 (x (logior i j)) (y 2)))
;           :use ((:instance mod (x i) (y j)))
           )))






(local (include-book "bvecp")) ;;try


(local (defun ls-induct (k x)
   (if (zp k)
       x
     (ls-induct (1- k) (fl (/ x 2))))))

(local (defthm logior-ones-3-1
     (implies (and (integerp k) (> k 0))
              (= (fl (/ (1- (expt 2 k)) 2))
                 (1- (expt 2 (1- k)))))
   :rule-classes ()
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable expt)
                               '())
           :use ((:instance fl-unique (x (/ (1- (expt 2 k)) 2)) (n (1- (expt 2 (1- k))))))))))

(local (defthm logior-ones-3-2
              (implies (and (integerp k) (> k 0))
                       (= (mod (1- (expt 2 k)) 2) 1))
              :rule-classes ()
              :hints (("Goal" :in-theory (e/d (expt) (mod-2*i))
                       :use ((:instance mod012 (x (1- (expt 2 k))))
                             (:instance mod-mod-2-not-equal (x (1- (expt 2 k))))
                             (:instance mod-2*i (i (expt 2 (1- k))))
                             )))))

(local (defthm logior-ones-3
    (implies (and (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 k)))
	     (= (logior (1- (expt 2 k)) x)
		(1- (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt mod-mult-of-n)
           :induct (ls-induct k x))
	  ("Subgoal *1/2" :use (logior-ones-3-1
				logior-ones-3-2
				mod012
				(:instance quot-mod (m x) (n 2))
				(:instance quot-mod (m (logior (1- (expt 2 k)) x)) (n 2))
;				(:instance natp-logior (i (1- (expt 2 k))) (j x))
				(:instance fl-def-linear (x (/ x 2)))
;				(:instance logior-fl-2 (i (1- (expt 2 k))) (j x))
	;			(:instance logior-mod-2 (i (1- (expt 2 k))) (j x))
                                )))))

;make into a better form for rewriting?
;gen to make conclusion the cat of the high bits of x (none if x is a bvecp) with a vector of ones?
(defthm logior-ones
    (implies (and (natp n) ;gen?
		  (bvecp x n))
	     (equal (logior x (1- (expt 2 n)))
		    (1- (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable  bvecp)
           :use ((:instance logior-ones-3 (k n))))))

;rename
(defthm logior-1-x
    (implies (bvecp x 1)
	     (equal (logior 1 x) 1))
  :hints (("Goal" :use ((:instance logior-ones (n 1))))))


(local (defthm or-dist-a-helper
  (implies (and (< i (expt 2 n))
                (< j (expt 2 n))
                (integerp i)
                (>= i 0)
                )
           (< (logior i j) (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ;expt ;yuck
                              expt-split
                              )
           :induct (op-dist-induct i j n))
	  ("Subgoal *1/2" :use ((:instance logior-def)
				(:instance mod012 (x i))
				(:instance mod012 (x j))))
          ("Subgoal *1/3" :use ((:instance logior-def)
                                (:instance mod012 (x i))
				(:instance mod012 (x j))
                                )))))

;n is a free var
;rename
;consider :linear?
(defthm or-dist-a
  (implies (and (< i (expt 2 n))
                (< j (expt 2 n))
                )
           (< (logior i j) (expt 2 n)))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use ( or-dist-a-helper))))

(defthm logior-bvecp
  (implies (and (bvecp x n)
                (bvecp y n))
           (bvecp (logior x y) n))
  :hints (("Goal" :in-theory (enable bvecp))))




;gen?
;whoa.  this is a lower bound
;unfortunate to have to disable those rules..
(defthm logior-bnd
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (<= x (logior x y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d () (LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE
                                      FL-<-INTEGER
                                      FL->-INTEGER
                                      FL-LOGIOR-BY-2
                                      FL-OF-EVEN/2)
                                  )
           :induct (log-induct x y))
	  ("Subgoal *1/2" :use ((:instance logior-def (i x) (j y))
				(:instance quot-mod (m x) (n 2))
				(:instance mod012)
				(:instance mod012 (x y))
                                ))))



(local
;gen
 (defthm or-dist-b-1
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0)
                 (< y (expt 2 n)))
            (= (logior (* (expt 2 n) x) y)
               (+ (* 2 (logior (fl (* (expt 2 (1- n)) x))
                               (fl (/ y 2))))
                  (logior (mod (* (expt 2 n) x) 2)
                          (mod y 2)))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt-split)
            :use ((:instance logior-def (i (* (expt 2 n) x)) (j y)))))))

(local
 (defthm or-dist-b-2
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0)
                 (< y (expt 2 n)))
            (= (logior (* (expt 2 n) x) y)
               (+ (* 2 (logior (* (expt 2 (1- n)) x)
                               (fl (/ y 2))))
                  (mod y 2))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt) ;yuck
            :use ((:instance or-dist-b-1)
                  (:instance fl-int (x (* (expt 2 (1- n)) x)))
                  (:instance mod-2*i (i (* (expt 2 (1- n)) x))))))))

(local
 (defthm or-dist-b-3
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0)
                 (< y (expt 2 n))
                 (= (logior (* (expt 2 (1- n)) x)
                            (fl (/ y 2)))
                    (+ (* (expt 2 (1- n)) x)
                       (fl (/ y 2)))))
            (= (logior (* (expt 2 n) x) y)
               (+ (* (expt 2 n) x)
                  (* 2	(fl (/ y 2)))
                  (mod y 2))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt-split)
            :use ((:instance or-dist-b-2))))))

(local
 (defthm or-dist-b-4
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0)
                 (< y (expt 2 n))
                 (= (logior (* (expt 2 (1- n)) x)
                            (fl (/ y 2)))
                    (+ (* (expt 2 (1- n)) x)
                       (fl (/ y 2)))))
            (= (logior (* (expt 2 n) x) y)
               (+ (* (expt 2 n) x) y)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance or-dist-b-3)
                         (:instance quot-mod (m y) (n 2)))))))

;generalize to or of disjoint ranges?
(defthm OR-DIST-B
    (implies (and (< y (expt 2 n))
                  (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  )
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal"  :in-theory (enable expt)
           :induct (or-dist-induct y n))
	  ("Subgoal *1/2" :use ((:instance or-dist-b-4)))))



(local
 (defthm or-dist-c-1
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (logior (* (expt 2 n) x)
                       (* (expt 2 n) y))
               (+ (* 2 (logior (* (expt 2 (1- n)) x)
                               (* (expt 2 (1- n)) y)))
                  (logior (mod (* (expt 2 n) x) 2)
                          (mod (* (expt 2 n) y) 2)))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt)
            :use ((:instance logior-def (i (* (expt 2 n) x)) (j (* (expt 2 n) y))))))))

(local
 (defthm or-dist-c-2
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (logior (* (expt 2 n) x)
                       (* (expt 2 n) y))
               (* 2 (logior (* (expt 2 (1- n)) x)
                            (* (expt 2 (1- n)) y)))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt)
            :use ((:instance or-dist-c-1)
                  (:instance mod-2*i (i (* (expt 2 (1- n)) x)))
                  (:instance mod-2*i (i (* (expt 2 (1- n)) y))))))))

(local
 (defthm or-dist-c-3
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0)
                 (= (logior (* (expt 2 (1- n)) x)
                            (* (expt 2 (1- n)) y))
                    (* (expt 2 (1- n)) (logior x y))))
            (= (logior (* (expt 2 n) x)
                       (* (expt 2 n) y))
               (* (expt 2 n)
                  (logior x y))))
   :rule-classes ()
   :hints (("Goal"  :in-theory (enable expt)
            :use ((:instance or-dist-c-2))))))

;BOZO rename!
(defthm or-dist-c
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (= (logior (* (expt 2 n) x)
                      (* (expt 2 n) y))
              (* (expt 2 n) (logior x y))))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat n))
	  ("Subgoal *1/1" :use ((:instance or-dist-c-3)))))



(local
 (defthm mod-logior-1
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (logior x y)
               (logior (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
                               (mod x (expt 2 n)))
                       (logior (* (expt 2 n) (fl (/ y (expt 2 n))))
                               (mod y (expt 2 n))))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance quot-mod (m x) (n (expt 2 n)))
                         (:instance quot-mod (m y) (n (expt 2 n)))
                         (:instance mod-bnd-1 (m x) (n (expt 2 n)))
                         (:instance mod-bnd-1 (m y) (n (expt 2 n)))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
;		(:instance mod>=0 (m y) (n (expt 2 n)))
                         (:instance or-dist-b (x (fl (/ x (expt 2 n)))) (y (mod x (expt 2 n))))
                         (:instance or-dist-b (x (fl (/ y (expt 2 n)))) (y (mod y (expt 2 n)))))))))

(local
 (defthm mod-logior-3
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (logior x y)
               (logior (logior (* (expt 2 n) (fl (/ x (expt 2 n))))
                               (* (expt 2 n) (fl (/ y (expt 2 n)))))
                       (logior (mod x (expt 2 n))
                               (mod y (expt 2 n))))))
   :rule-classes ()
   :hints (("Goal" :use ( ;(:instance mod>=0 (m x) (n (expt 2 n)))
;(:instance mod>=0 (m y) (n (expt 2 n)))
                         (:instance mod-logior-1)
                         )))))


(local
 (defthm mod-logior-4
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (logior x y)
               (+ (* (expt 2 n)
                     (logior (fl (/ x (expt 2 n)))
                             (fl (/ y (expt 2 n)))))
                  (logior (mod x (expt 2 n))
                          (mod y (expt 2 n))))))
   :rule-classes ()
   :hints (("Goal"
            :use ((:instance mod-logior-3)
                         (:instance or-dist-c (x (fl (/ x (expt 2 n)))) (y (fl (/ y (expt 2 n)))))
                         (:instance or-dist-b
                                    (x (logior (fl (/ x (expt 2 n)))
                                               (fl (/ y (expt 2 n)))))
                                    (y (logior (mod x (expt 2 n))
                                               (mod y (expt 2 n)))))
                         (:instance mod-bnd-1 (m x) (n (expt 2 n)))
                         (:instance mod-bnd-1 (m y) (n (expt 2 n)))
;                         (:instance or-dist-a (x (mod x (expt 2 n))) (y (mod y (expt 2 n))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
;		(:instance mod>=0 (m y) (n (expt 2 n)))
                         )))))

(local
 (defthm mod-logior-5-not-by-2
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (> n 0))
            (= (mod (logior x y) (expt 2 n))
               (mod (logior (mod x (expt 2 n)) (mod y (expt 2 n)))
                    (expt 2 n))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance mod-logior-4)
                         (:instance mod-mult-eric
                                    (x (logior (mod x (expt 2 n)) (mod y (expt 2 n))))
                                    (y (expt 2 n))
                                    (a (logior (fl (/ x (expt 2 n)))
                                               (fl (/ y (expt 2 n))))))
                         (:instance n<=fl-linear (x (/ x (expt 2 n))) (n 0))
                         (:instance n<=fl-linear (x (/ y (expt 2 n))) (n 0))
;			(:instance logior-nat (i (fl (/ x (expt 2 n)))) (j (fl (/ y (expt 2 n)))))
;		(:instance logior-nat (i (mod x (expt 2 n))) (j (mod y (expt 2 n))))
;			(:instance mod>=0 (m x) (n (expt 2 n)))
;		(:instance mod>=0 (m y) (n (expt 2 n)))
                         )))))

(defthmd mod-logior
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0)
                )
           (equal (mod (logior x y) (expt 2 n))
                  (logior (mod x (expt 2 n)) (mod y (expt 2 n)))))
  :hints (("Goal" :use ((:instance mod-logior-5-not-by-2)
			(:instance mod-does-nothing
				   (x (logior (mod x (expt 2 n)) (mod y (expt 2 n))))
				   (y (expt 2 n)))
;/			(:instance mod>=0 (m x) (n (expt 2 n)))
	;		(:instance mod>=0 (m y) (n (expt 2 n)))
;			(:instance logior-nat (i (mod x (expt 2 n))) (j (mod y (expt 2 n))))
			(:instance mod-bnd-1 (m x) (n (expt 2 n)))
			(:instance mod-bnd-1 (m y) (n (expt 2 n)))
;			(:instance or-dist-a (x (mod x (expt 2 n))) (y (mod y (expt 2 n))))
                        ))))


#|


(defthmd logior-simp-1-alt
  (implies (and (syntaxp (and (should-have-a-2-factor-multiplied-in i)
                              (should-have-a-2-factor-multiplied-in j)))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (* 2 (logior i j))
                  (logior (* 2 i) (* 2 j))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-negative-6
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< (logior i j) -1)
                  (AND (< -1 I) (< -1 J))
                  ))
  :hints (("Goal" :cases ((equal j -1) (equal i -1))
           :in-theory (enable logior))))

;weird
;trying disabled
(defthmd logior-ones-when-one-arg-is-even
  (implies (and (integerp (* 1/2 j))
                (case-split (integerp j))
                (case-split (integerp i))
                )
           (and (equal (equal (logior i j) -1)
                       (and (not (integerp (* 1/2 i)))
                            (equal (logior (fl (/ i 2)) (fl (/ j 2))) -1)))
                (equal (equal (logior j i) -1)
                       (and (not (integerp (* 1/2 i)))
                            (equal (logior (fl (/ i 2)) (fl (/ j 2))) -1)))))
  :hints (("Goal" :in-theory (e/d (logior) (fl-int))))
  )


;move!
;disable?
;more general version loops
(defthm tighten-integer-bound
  (implies (integerp x)
           (equal (< x 1)
                  (<= x 0))))

;move!
;disable?
(defthm integer-<-fraction-expt-case
  (implies (and (< n 0)
                (integerp x))
           (equal (< X (EXPT 2 N))
                  (<= X 0)))
  :hints (("Goal" :in-theory (disable  EXPT-COMPARE)
           :use (:instance  EXPT-COMPARE
                            (lhs (expt 2 0))
                            (rhs (expt 2 n))))))

(local (include-book
        "../arithmetic/expt"))

(local (defun logior-+-hint (x i)
  (if (= (nfix i) 0)
      x
    (logior-+-hint (floor x 2) (1- i)))))

;follows from  OR-DIST-B?
(defthm logior-+
  (implies (and (integerp i)
                (<= 0 i)
                (integerp x)
                (<= 0 x)
                (< x (expt 2 i)))
           (equal (logior (expt 2 i) x)
                  (+ (expt 2 i) x)))
  :hints (("Goal" :induct (logior-+-hint x i)
                  :in-theory
                   (set-difference-theories
                       (enable logior logand lognot
                               functional-commutativity-of-minus-*-right
                               functional-commutativity-of-minus-*-left)
                       '(a2 a5))))
  :rule-classes nil)

|#


(defthm logior-non-negative-integerp
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (integerp (logior i j))
                (<= 0 (logior i j))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))