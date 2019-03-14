(in-package "RTL")
(include-book "verify-guards")
(local (include-book "lza"))

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

(local
 (acl2::with-arith5-help
  (defruled bits-default
    (implies (or (not (real/rationalp x))
                 (not (integerp i))
                 (not (integerp j)))
             (equal (bits x i j) 0))
    :enable (bits fl))))

(local
 (acl2::with-arith5-help
  (defruled bits-bounds-<=
    (implies (and (integerp i)
                  (integerp j)
                  (>= (- i j) -1))
             (<= (bits x i j) (1- (expt 2 (+ 1 i (- j))))))
    :rule-classes :linear
    :cases ((not (integerp (bits x i j)))
            (not (integerp (expt 2 (+ 1 i (- j))))))
    :use bits-bounds)))

(local
 (acl2::with-arith5-help
  (defruled bits-mod-fl-rewrite
    (implies (and (integerp i)
                  (integerp j))
             (equal (bits x i j)
                    (mod (fl (* x (expt 2 (- j)))) (expt 2 (+ 1 i (- j))))))
    :use (:instance bits-mod-fl
                    (i (1+ i))))))

(acl2::with-arith5-nonlinear-help
 (defrule fl-{x+y+z}/m
   (implies (and (real/rationalp x)
                 (real/rationalp y)
                 (real/rationalp z)
                 (real/rationalp m)
                 (< 0 m))
            (equal (fl (/ (+ x y z) m))
                   (+ (fl (/ x m))
                      (fl (/ y m))
                      (fl (/ z m))
                      (let ((s (+ (mod x m) (mod y m) (mod z m))))
                        (cond ((< s m) 0)
                              ((< s (* 2 m)) 1)
                              (t 2))))))
   :enable fl))

(defrule fl-{x+y}/m
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp m)
                (< 0 m))
           (equal (fl (/ (+ x y) m))
                  (+ (fl (/ x m))
                     (fl (/ y m))
                     (if (< (+ (mod x m) (mod y m)) m) 0 1))))
  :use (:instance fl-{x+y+z}/m
                  (z 0)))

(defrule fl-{x+y+cin}/m
  (implies (and (integerp x)
                (integerp y)
                (bvecp cin 1)
                (posp m))
           (equal (fl (/ (+ x y cin) m))
                  (+ (fl (/ x m))
                     (fl (/ y m))
                     (if (< (+ (mod x m) (mod y m) cin) m) 0 1))))
  :use ((:instance fl-{x+y+z}/m
                   (z cin))
        (:instance bvecp-0-1
                   (x cin)))
  :cases ((>= m 2))
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (integerp m)
                    (>= m 2))
               (equal (fl (/ m)) 0))
      :enable fl))))

(local
 (acl2::with-arith5-help
  (defruled bitn-x+y+cin
    (implies (and (integerp x)
                  (integerp y)
                  (bvecp cin 1)
                  (natp n))
             (equal (bitn (+ x y cin) n)
                    (logxor (bitn x n)
                            (bitn y n)
                            (if (< (+ (bits x (1- n) 0) (bits y (1- n) 0) cin)
                                   (expt 2 n))
                                0
                              1))))
    :enable (bitn-def bits-mod bvecp)
    :use (:instance fl-{x+y+cin}/m
                    (m (expt 2 n))))))

(defruledl bitn-x+y
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (bitn (+ x y) n)
                  (logxor (bitn x n)
                          (bitn y n)
                          (if (< (+ (bits x (1- n) 0) (bits y (1- n) 0))
                                 (expt 2 n))
                              0
                            1))))
  :use (:instance bitn-x+y+cin
                  (cin 0)))

;;;**********************************************************************
;;;                      Bit Vector Addition
;;;**********************************************************************

(defrule half-adder
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat (logand u v) 1 (logxor u v) 1)))
  :rule-classes ()
  :cases ((and (= u 0) (= v 0))
          (and (= u 0) (= v 1))
          (and (= u 1) (= v 0))))

(defrule add-2
  (implies (and (integerp x) (integerp y))
           (equal (+ x y)
                  (+ (logxor x y)
                     (* 2 (logand x y)))))
  :enable (logand lognot)
  :induct (logand x y)
  :hints (("subgoal *1/5" :use lemma))
  :rule-classes ()
  :prep-lemmas
  ((acl2::with-arith5-help
    (defruled lemma
      (implies (and (integerp x)
                    (integerp y)
                    (equal (+ (floor x 2) (floor y 2))
                           (+ (logxor (floor x 2) (floor y 2))
                              (* 2 (logand (floor x 2) (floor y 2))))))
               (equal (+ x y)
                      (+ (logxor x y) (* 2 (logand x y)))))))))

(defrule full-adder
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1))
           (equal (+ u v w)
                  (cat (logior (logand u v) (logior (logand u w) (logand v w))) 1
                       (logxor u (logxor v w)) 1)))
  :rule-classes ()
  :cases ((and (= u 0) (= v 0) (= w 0))
          (and (= u 0) (= v 0) (= w 1))
          (and (= u 0) (= v 1) (= w 0))
          (and (= u 0) (= v 1) (= w 1))
          (and (= u 1) (= v 0) (= w 0))
          (and (= u 1) (= v 0) (= w 1))
          (and (= u 1) (= v 1) (= w 0))))

(defrule add-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (= (+ x y z)
              (+ (logxor x (logxor y z))
                 (* 2 (logior (logand x y)
                              (logior (logand x z)
                                      (logand y z)))))))
  :rule-classes ()
  :disable floor
  :induct (my-induct x y z)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule measure-lemma1
      (<= (acl2-count (floor (ifix x) 2)) (acl2-count x))
      :rule-classes :linear))
   (acl2::with-arith5-help
    (defrule measure-lemma2
      (implies (and (not (zip x))
                    (not (= x -1)))
               (< (acl2-count (floor (ifix x) 2)) (acl2-count x)))
      :rule-classes :linear))
   (defun my-induct (x y z)
     (declare (xargs :measure (+ (acl2-count x) (acl2-count y) (acl2-count z))
                     :hints (("goal" :in-theory
                              (disable ifix floor acl2-count)))))
     (if (and (or (zip x) (= x -1))
              (or (zip y) (= y -1))
              (or (zip z) (= z -1)))
         (list x y x)
       (my-induct (floor (ifix x) 2) (floor (ifix y) 2) (floor (ifix z) 2))))
  (acl2::with-arith5-help
    (defrule  lemma
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z)
                    (equal (+ (floor x 2) (floor y 2) (floor z 2))
                           (+ (logxor (floor x 2) (floor y 2) (floor z 2))
                              (* 2 (logior
                                    (logand (floor x 2) (floor y 2))
                                    (logand (floor x 2) (floor z 2))
                                    (logand (floor y 2) (floor z 2)))))))
               (equal (+ x y z)
                      (+ (logxor x y z)
                         (* 2 (logior
                               (logand x y)
                               (logand x z)
                               (logand y z))))))))))

(defruled lutz-lemma
  (implies (and (integerp x) (integerp y) (natp n))
           (and (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                     (= (bits (logxor x y) (1- n) 0) (1- (expt 2 n))))
                (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                     (= (+ (bits x (1- n) 0) (bits y (1- n) 0))
                        (1- (expt 2 n)))))))

(defun rc-carry (x y k)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp k))))
  (if (zp k)
      0
    (logior (logand (bitn x (1- k)) (bitn y (1- k)))
	    (logior (logand (bitn x (1- k)) (rc-carry x y (1- k)))
		    (logand (bitn y (1- k)) (rc-carry x y (1- k)))))))

(defrulel bvecp-1-rc-carry
  (bvecp (rc-carry x y k) 1))

(defun rc-sum (x y k)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp k))))
  (if (zp k)
      0
    (cat (logxor (bitn x (1- k))
		 (logxor (bitn y (1- k)) (rc-carry x y (1- k))))
	 1
	 (rc-sum x y (1- k))
	 (1- k))))

(defrulel bvecp-rc-sum
  (bvecp (rc-sum x y k) k)
  :expand (bvecp 0 k))

(acl2::with-arith5-nonlinear-help
 (defrule ripple-carry
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (+ (bits x (1- n) 0) (bits y (1- n) 0))
                  (cat (rc-carry x y n) 1 (rc-sum x y n) n)))
  :rule-classes ()
  :induct (sub1-induction n)
  :disable (rc-carry rc-sum)
  :hints
  (("subgoal *1/2" :expand ((rc-carry x y n)
                            (rc-sum x y n))
    :use (:instance full-adder
                    (u (bitn x (1- n)))
                    (v (bitn y (1- n)))
                    (w (rc-carry x y (1- n)))))
   ("subgoal *1/1" :in-theory (enable rc-carry)))
  :prep-lemmas
  ((defrule lemma1
     (implies (and (posp n)
                   (bvecp x (1- n))
                   (bvecp y 1))
              (bvecp (+ x (* (expt 2 (1- n)) y)) n))
     :enable bvecp)
   (defrule lemma2
     (implies (posp n)
              (equal (bits x (1- n) 0)
                     (+ (* (expt 2 (1- n)) (bitn x (1- n)))
                        (bits x (+ -2 n) 0))))
     :use (:instance bitn-plus-bits
                     (n (1- n))
                     (m 0)))
   (defrule lemma3
     (implies (and (bvecp x 1)
                   (bvecp y n)
                   (natp n))
              (equal (cat x 1 y n)
                     (+ (* x (expt 2 n)) y)))
     :enable binary-cat))))

(defun gen (x y i j)
  (declare (xargs :measure (nfix (1+ i))
                  :guard (and (integerp x)
                              (integerp y))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  (bitn x i)
	(gen x y (1- i) j))
    0))

(defun prop (x y i j)
  (declare (xargs :measure (nfix (1+ i))
                  :guard (and (integerp x)
                              (integerp y))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  0
	(prop x y (1- i) j))
    1))

(defrule bvecp-1-gen
  (bvecp (gen x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((gen x y i j)))))

(defrule bvecp-1-prop
  (bvecp (prop x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((prop x y i j)))))

(acl2::with-arith5-nonlinear-help
 (defruled gen-val
   (implies (natp j)
            (equal (gen x y i j)
                   (if (>= (+ (bits x i j) (bits y i j))
                           (expt 2 (1+ (- i j))))
                       1
                     0)))
   :induct (gen x y i j)
   :hints
   (("subgoal *1/3" :in-theory (enable bits-default))
    ("subgoal *1/2" :use
     ((:instance bitn-plus-bits
                 (n i)
                 (m j))
      (:instance bitn-plus-bits
                 (x y)
                 (n i)
                 (m j))
      (:instance bitn-0-1
                 (n i))
      (:instance bitn-0-1
                 (x y)
                 (n i))))
    ("subgoal *1/1" :in-theory (enable bits-bounds-<=) :use
     ((:instance bitn-plus-bits
                 (n i)
                 (m j))
      (:instance bitn-plus-bits
                 (x y)
                 (n i)
                 (m j))
      (:instance bitn-0-1
                 (n i)))))))

(defruled gen-val-cor1
  (implies (natp j)
           (equal (gen x y i j)
                  (bitn (+ (bits x i j) (bits y i j))
			(1+ (- i j)))))
  :enable gen-val
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma
     (implies (and (bvecp x n)
                   (bvecp y n))
              (equal (bitn (+ x y) n)
                     (if (< (+ x y) (expt 2 n)) 0 1)))
     :enable (bitn-def bvecp fl)))))

(acl2::with-arith5-help
 (defruled gen-val-cor2
   (implies (and (integerp x)
                 (integerp y))
           (equal (+ (bits x i 0) (bits y i 0))
		  (+ (* (expt 2 (1+ i)) (gen x y i 0))
		     (bits (+ x y) i 0))))
   :enable (gen-val bits-mod bits-default)))

(acl2::with-arith5-nonlinear-help
 (defrule gen-special-case
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn (+ (bits x i j) (bits y i j)) (- i j)) 0))
           (equal (gen x y i j)
                  (logior (bitn x i) (bitn y i))))
  :rule-classes ()
  :enable (gen-val-cor1 bitn-bits bitn-x+y)
  :use ((:instance bitn-plus-bits
                   (n i)
                   (m j))
        (:instance bitn-plus-bits
                   (x y)
                   (n i)
                   (m j))
        (:instance bitn-0-1
                   (n i)))))

(defruled prop-val
  (implies (and (integerp i) (natp j) (>= i j))
           (equal (prop x y i j)
                  (if (= (+ (bits x i j) (bits y i j))
                         (1- (expt 2 (1+ (- i j)))))
                      1
                    0)))
  :induct (prop x y i j)
  :hints
  (("subgoal *1/2"
    :use ((:instance bitn-plus-bits
                     (n i)
                     (m j))
          (:instance bitn-plus-bits
                     (x y)
                     (n i)
                     (m j)))
    :cases ((and (= (bitn x i) 0) (= (bitn y i) 1))
            (and (= (bitn x i) 1) (= (bitn y i) 0))))
   ("subgoal *1/1" :in-theory (enable bitn-bits)))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defruled lemma0
      (implies (and (bvecp x n)
                    (posp n)
                    (equal (bitn x (1- n)) 0))
               (<= x (1- (expt 2 (1- n)))))
      :enable (bvecp bitn-def fl)
      :cases ((<= x (1- (expt 2 (1- n))))
              (>= x (expt 2 (1- n))))))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma
      (implies (and (bvecp x n)
                    (bvecp y n)
                    (equal (bitn x (1- n)) (bitn y (1- n)))
                    (posp n))
               (equal (equal (+ x y) (1- (expt 2 n))) nil))
      :cases ((= (bitn x (1- n)) 0) (= (bitn x (1- n)) 1))
      :enable bvecp
      :hints
      (("subgoal 2" :cases ((not (<= x (1- (expt 2 (1- n)))))
                            (not (<= y (1- (expt 2 (1- n)))))))
       ("subgoal 2.2" :use lemma0)
       ("subgoal 2.1" :use (:instance lemma0 (x y)))
       ("subgoal 1" :cases ((not (>= x (expt 2 (1- n))))
                            (not (>= y (expt 2 (1- n)))))))))))

(defruled prop-as-logxor
   (implies (and (natp i)
                 (natp j)
                 (<= j i)
                 (integerp x)
                 (integerp y))
            (equal (prop x y i j)
                   (if (equal (logxor (bits x i j) (bits y i j))
                              (1- (expt 2 (1+ (- i j)))))
                       1
                     0)))
   :enable prop-val
   :use (:instance lutz-lemma
                   (x (bits x i j))
                   (y (bits y i j))
                   (n (+ 1 i (- j)))))

(defrule gen-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (gen x y i j)
                  (logior (gen x y i (1+ k))
                          (logand (prop x y i (1+ k))
                                  (gen x y k j)))))
  :rule-classes ())

(defrule gen-extend-cor
  (implies (and (integerp x)
                (integerp y)
                (natp i)
                (natp j)
                (natp k)
                (> i k)
                (>= k j))
           (equal (gen x y i j)
                  (bitn (+ (bits x i (1+ k))
                           (bits y i (1+ k))
                           (gen x y k j))
                        (- i k))))
  :rule-classes ()
  :disable gen
  :use gen-extend
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma1
      (implies (and (bvecp x (1- n))
                    (bvecp y (1- n))
                    (bvecp g 1)
                    (posp n))
               (bvecp (+ x y g) n))
      :enable bvecp
      :cases ((not (<= x (1- (expt 2 (1- n)))))
              (not (<= y (1- (expt 2 (1- n)))))
              (not (<= g 1)))))
   (acl2::with-arith5-help
    (defrule lemma2
      (implies (and (bvecp x (1+ n))
                    (natp n))
               (equal (bitn x n)
                      (if (< x (expt 2 n)) 0 1)))
      :enable (bvecp bitn-def fl)))
   (acl2::with-arith5-help
    (defrule lemma3
      (implies (and (bvecp g 1)
                    (integerp x)
                    (integerp y)
                    (natp i)
                    (natp j)
                    (>= i j))
               (equal (logior (gen x y i j) (logand g (prop x y i j)))
                      (if (< (+ (bits x i j) (bits y i j) g)
                             (expt 2 (+ 1 i (- j))))
                          0
                        1)))
      :enable (bvecp gen-val prop-val)
      :cases ((<= (+ (bits x i j) (bits y i j)) (- (expt 2 (+ 1 i (- j))) 2))
              (= (+ (bits x i j) (bits y i j)) (1- (expt 2 (+ 1 i (- j)))))
              (>= (+ (bits x i j) (bits y i j)) (expt 2 (+ 1 i (- j))))
              (not (integerp (expt 2 (+ 1 i (- j))))))))))

(defrule prop-extend
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (> i k)
                (>= k j)
                (>= j 0))
           (equal (prop x y i j)
                  (logand (prop x y i (1+ k))
                          (prop x y k j))))
  :rule-classes ())

(acl2::with-arith5-help
 (defrule bits-sum
  (implies (and (integerp x) (integerp y))
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (gen x y (1- j) 0))
                        (- i j) 0)))
  :rule-classes ()
  :enable bits-mod-fl-rewrite
  :expand ((gen x y -1 0))
  :cases ((and (integerp i) (integerp j)))
  :hints
  (("subgoal 2" :in-theory (enable bits gen) :cases ((posp j)))
   ("subgoal 1" :in-theory (enable gen-val)
    :use (:instance fl-{x+y}/m
                     (m (expt 2 j)))))))

(acl2::with-arith5-help
 (defrule bits-sum-shift
   (implies (and (integerp x)
                 (integerp y)
                 (natp i)
                 (natp j)
                 (> j 0)
                 (>= i j))
            (equal (bits (+ (* (expt 2 j) x) y) i j)
                   (bits (+ (bits (* (expt 2 j) x) i j)
                            (bits y i j))
                         (- i j) 0)))
   :rule-classes ()
   :enable bits-mod-fl-rewrite
   :use (:instance lemma
                   (m (expt 2 j)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (integerp x)
                    (real/rationalp y)
                    (real/rationalp m)
                    (< 0 m))
               (equal (fl (/ (+ (* x m) y) m))
                      (+ x (fl (/ y m)))))
      :use (:instance fl-{x+y}/m
                      (x (* x m)))))))

(acl2::with-arith5-help
 (defruled bits-sum-swallow
   (implies (and (equal (bitn x k) 0)
                 (integerp x)
                 (natp y)
                 (integerp i)
                 (integerp j)
                 (integerp k)
                 (>= i j)
                 (> j k)
                 (>= k 0)
                 (<= y (expt 2 k)))
            (equal (bits (+ x y) i j)
                   (bits x i j)))
   :enable bits-mod-fl-rewrite
   :use (lemma1
         (:instance lemma2
                    (m (expt 2 j))))
   :prep-lemmas
   ((acl2::with-arith5-nonlinear-help
     (defruled lemma1
       (implies (and (= (bitn x k) 0)
                     (natp k)
                     (integerp j)
                     (< k j))
                (< (bits x (1- j) 0) (- (expt 2 j) (expt 2 k))))
       :cases ((not (= (bits x (1- j) 0)
                       (+ (* (expt 2 (1+ k)) (bits x (1- j) (1+ k)))
                          (bits x (1- k) 0))))
               (not (<= (bits x (1- j) (1+ k)) (1- (expt 2 (+ -1 j (- k))))))
               (not (<= (bits x (1- k) 0) (1- (expt 2 k)))))
       :hints
       (("subgoal 3" :use ((:instance bits-plus-bits
                                      (n (1- j))
                                      (m 0)
                                      (p (1+ k)))
                           (:instance bitn-plus-bits
                                      (n k)
                                      (m 0))))
        ("subgoal 2" :use (:instance bits-bounds
                                     (i (1- j))
                                     (j (1+ k))))
        ("subgoal 1" :use (:instance bits-bounds
                                     (i (1- k))
                                     (j 0))))
       :prep-lemmas
       ((defrule lemma
          (implies (and (natp n)
                        (integerp x)
                        (< x (expt 2 n)))
                   (<= x (1- (expt 2 n))))))))
    (defrule lemma2
      (implies (and (real/rationalp x)
                    (real/rationalp y)
                    (real/rationalp m)
                    (< 0 m)
                    (<= 0 y)
                    (< (+ (mod x m) y) m))
               (equal (fl (/ (+ x y) m))
                      (fl (/ x m))))
      :use fl-{x+y}/m
      :enable fl))))

(defruled bits-sum-cor
  (implies (and (integerp x)
                (integerp y)
                (>= i j)
                (>= j 0)
                (= (gen x y i j) 0)
                (= (gen x y (1- j) 0) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :use bits-sum
  :prep-lemmas
  ((acl2::with-arith5-help
    (defrule lemma
      (implies (and (= (gen x y i j) 0)
                    (>= j 0))
               (equal (bits (+ (bits x i j) (bits y i j)) (- i j) 0)
                      (+ (bits x i j) (bits y i j))))
      :enable (gen-val bvecp-bits-0 bvecp)
      :cases ((integerp j))
      :hints (("subgoal 2" :in-theory (enable bits)))))))

(local
 (acl2::with-arith5-nonlinear-help
  (defruled gen-sum-3
    (implies (and (integerp x)
                  (integerp y)
                  (integerp z)
                  (integerp j))
             (equal (+ (gen x y (1- j) 0)
                       (gen (+ x y) z (1- j) 0))
                    (let* ((m (expt 2 j))
                           (s (+ (mod x m) (mod y m) (mod z m))))
                      (cond ((< s m) 0)
                            ((< s (* 2 m)) 1)
                            (t 2)))))
    :enable (gen-val bits-mod)
    :cases ((natp j)))))

(acl2::with-arith5-help
 (defrule bits-sum-3
   (implies (and (integerp x) (integerp y) (integerp z))
            (equal (bits (+ x y z) i j)
                   (bits (+ (bits x i j)
                            (bits y i j)
                            (bits z i j)
                            (gen x y (1- j) 0)
                            (gen (+ x y) z (1- j) 0))
                         (- i j) 0)))
   :rule-classes ()
   :enable (bits-mod-fl-rewrite gen-sum-3)
   :cases ((and (integerp i) (integerp j)))
   :hints
   (("subgoal 2" :in-theory (enable bits gen) :cases ((posp j)))
    ("subgoal 1" :use (:instance fl-{x+y+z}/m
                                 (m (expt 2 j)))))))

(acl2::with-arith5-help
 (defrule bits-sum-plus-1
   (implies (and (integerp x)
                 (integerp y)
                 (integerp i)
                 (integerp j)
                 (>= i j)
                 (>= j 0))
            (equal (bits (+ 1 x y) i j)
                   (bits (+ (bits x i j)
                            (bits y i j)
                            (logior (prop x y (1- j) 0)
                                    (gen x y (1- j) 0)))
                         (- i j) 0)))
   :rule-classes ()
   :enable bits-mod-fl-rewrite
   :use (:instance fl-{x+y+cin}/m
                   (cin 1)
                   (m (expt 2 j)))
   :prep-lemmas
   ((defrule lemma
      (implies (and (integerp x)
                    (integerp y)
                    (integerp j)
                    (natp j))
               (equal (logior (prop x y (1- j) 0)
                              (gen x y (1- j) 0))
                      (if (< (+ (mod x (expt 2 j)) (mod y (expt 2 j)) 1)
                             (expt 2 j))
                          0
                        1)))
      :enable (prop-val gen-val bits-mod)
      :cases ((posp j))))))

(local
 (acl2::with-arith5-nonlinear-help
  (defruled sum-when-logand=0
    (implies (and (bvecp x n)
                  (bvecp y n)
                  (natp n)
                  (= (logand x y) 0))
             (<= (+ x y) (1- (expt 2 n))))
    :enable (logand bvecp)
    :induct (my-induct x y n)
    :hints (("subgoal *1/2" :use (:instance binary-logand
                                            (i x)
                                            (j y))))
    :prep-lemmas
    ((defun my-induct (x y n)
       (if (zp n)
           (list x y n)
         (my-induct (floor x 2) (floor y 2) (1- n))))))))

(defruled logand-gen-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand (bits x i j) (bits y i j)) 0))
           (equal (gen x y i j) 0))
  :enable gen-val
  :use (:instance sum-when-logand=0
                  (x (bits x i j))
                  (y (bits y i j))
                  (n (+ 1 i (- j)))))

(defrule logand-gen-0-cor
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand x y) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :rule-classes ()
  :enable bits-sum-cor
  :use (logand-gen-0
        bits-logand
        (:instance bits-logand
                   (i (1- j))
                   (j 0))
        (:instance logand-gen-0
                   (i (1- j))
                   (j 0))))

(acl2::with-arith5-nonlinear-help
 (defruled gen-plus
   (implies (and (integerp x)
                 (integerp y)
                 (integerp z)
                 (natp k)
                 (= (logand z y) 0)
                 (= (gen x y k 0) 1))
            (equal (gen (+ x y) z k 0) 0))
   :enable (bvecp bits-mod)
   :use ((:instance gen-sum-3
                    (j (1+ k)))
         (:instance sum-when-logand=0
                    (x (bits y k 0))
                    (y (bits z k 0))
                    (n (1+ k)))
         (:instance bits-logand
                    (x y)
                    (y z)
                    (i k)
                    (j 0)))))

(defruled gen-extend-3
  (implies (and (natp i)
                (natp j)
                (> i j)
                (integerp x)
                (integerp y)
                (bvecp z (1+ j))
                (= (logand y z) 0))
           (equal (gen (+ x y) z i 0)
                  (logand (prop x y i (1+ j))
                          (gen (+ x y) z j 0))))
  :enable (prop-val gen-plus)
  :disable (gen prop)
  :use ((:instance lemma1
                   (x (+ x y)))
        (:instance bits-sum
                   (j (1+ j))))
  :cases ((= (gen x y j 0) 0))
  :prep-lemmas
  ((defrule lemma1
     (implies (and (natp i)
                   (natp j)
                   (> i j)
                   (integerp x)
                   (bvecp z (1+ j)))
              (equal (gen x z i 0)
                     (if (= (bits x i (1+ j)) (1- (expt 2 (- i j))))
                         (gen x z j 0)
                       0)))
     :enable (prop-val gen-val bvecp-bits-0)
     :use ((:instance gen-extend
                      (y z)
                      (j 0)
                      (k j))
           (:instance bits-bounds
                      (j (1+ j)))))
   (acl2::with-arith5-nonlinear-help
    (defrule lemma2
      (implies (and (bvecp x n)
                    (bvecp y n)
                    (natp n))
               (equal (= (+ x y) (1- (expt 2 n)))
                      (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))))
      :enable (bvecp bits-mod)))))


;;;**********************************************************************
;;;                  Leading One Prediction
;;;**********************************************************************

(defund p0 (a b)
  (declare (xargs :guard (and (integerp a)
                              (integerp b))))
  (logxor a b))

(defund k0 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (logand (bits (lognot a) (1- n) 0) (bits (lognot b) (1- n) 0)))

(defund w0 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (bits (lognot (logxor (p0 a b) (* 2 (k0 a b n)))) (1- n) 0))

(defthmd p0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(integerp j))
	   (equal (bitn (p0 a b) j)
	          (if (= (bitn a j) (bitn b j))
		      0 1))))

(defthmd k0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(natp j)
                (natp n)
                (< j n))
	   (equal (bitn (k0 a b n) j)
	          (if (and (= (bitn a j) 0) (= (bitn b j) 0))
		      1 0))))

(defthmd w0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
                (not (zp j))
		(< j n))
	   (equal (bitn (w0 a b n) j)
	          (if (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j)))
		      1 0))))

(defthm lza-thm
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (and (>= (w0 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w0 a b n)))))))
  :rule-classes ())

(defthm lza-cor
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w0 a b n)))
               (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w0 a b n))))))
  :rule-classes ())

;;;**********************************************************************
;;;                    Trailing One Prediction
;;;**********************************************************************

(acl2::with-arith5-help
 (defrule top-thm-1
  (implies (and (natp k)
                (integerp a)
                (integerp b))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lognot (logxor a b)) k 0) 0)))
  :rule-classes ()
  :enable (bits-lognot)
  :disable (expt)
  :use ((:instance bits-sum-plus-1
                   (x a)
                   (y b)
                   (i k)
                   (j 0))
        (:instance lutz-lemma
                   (x a)
                   (y b)
                   (n (1+ k))))
  :prep-lemmas
  ((acl2::with-arith5-nonlinear-help
    (defrule lemma1
      (implies (and (bvecp x (1+ k))
                    (bvecp y (1+ k))
                    (natp k)
                    )
               (equal (equal (bits (+ 1 x y) k 0) 0)
                      (equal (+ x y) (1- (expt 2 (1+ k))))))
      :enable (bvecp bits-mod)))
   (defrule lemma2
     (implies (natp k)
              (equal (bits (expt 2 (1+ k)) k 0) 0))
     :enable bits-mod))))

(defrule top-thm-2
  (implies (and (natp n)
                (integerp a)
                (integerp b)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
                  (equal (bits (logxor (logxor a b)
                                       (cat (logior a b) n c 1))
                               k 0)
                         0)))
  :rule-classes ()
  :use lemma
  :prep-lemmas
  ((acl2::with-arith5-help
    (defruled lemma-sum=0
      (implies (and (integerp a)
                    (integerp b)
                    (bvecp c 1)
                    (posp k))
               (equal (equal (bits (+ a b c) k 0) 0)
                      (and (equal (bits (+ a b c) (1- k) 0) 0)
                           (= (logxor (bitn a k)
                                      (bitn b k)
                                      (if (>= (+ (bits a (1- k) 0)
                                                 (bits b (1- k) 0) c)
                                              (expt 2 k))
                                          1
                                        0))
                              0))))
      :enable bitn-x+y+cin
      :use ((:instance bitn-plus-bits (x (+ a b c)) (n k) (m 0))
            (:instance bitn-0-1 (x a) (n k))
            (:instance bitn-0-1 (x b) (n k)))))
   (acl2::with-arith5-help
    (defruled lemma-logxor=0
      (implies (and (integerp a)
                    (integerp b)
                    (posp k)
                    (natp n)
                    (< k n))
               (equal (equal (bits (logxor (logxor a b)
                                           (cat (logior a b) n c 1))
                                   k 0)
                             0)
                      (and (equal (bits (logxor (logxor a b)
                                                (cat (logior a b) n c 1))
                                        (1- k) 0)
                                  0)
                           (= (logxor (bitn a k)
                                      (bitn b k)
                                      (if (>= (+ (bitn a (1- k))
                                                 (bitn b (1- k)))
                                              1)
                                          1
                                        0))
                              0))))
      :enable (bitn-logxor bitn-logior bitn-cat)
      :use ((:instance bitn-plus-bits
                       (x (logxor a b (cat (logior a b) n c 1)))
                       (n k)
                       (m 0))
            (:instance bitn-0-1 (x a) (n (1- k)))
            (:instance bitn-0-1 (x b) (n (1- k)))
            (:instance bitn-0-1 (x a) (n k))
            (:instance bitn-0-1 (x b) (n k)))))
   (acl2::with-arith5-nonlinear-help
    (defruled lemma-carry
      (implies (and (integerp a)
                    (integerp b)
                    (bvecp c 1)
                    (posp k))
               (equal (>= (+ (bits a k 0) (bits b k 0) c) (expt 2 (1+ k)))
                      (>= (+ (bitn a k)
                             (bitn b k)
                             (if (>= (+ (bits a (1- k) 0)
                                        (bits b (1- k) 0)
                                        c)
                                     (expt 2 k))
                                 1
                               0))
                          2)))
      :use ((:instance bitn-plus-bits (x a) (n k) (m 0))
            (:instance bitn-plus-bits (x b) (n k) (m 0))
            (:instance bitn-0-1 (x a) (n k))
            (:instance bitn-0-1 (x b) (n k))
            (:instance bits-bounds (x a) (i (1- k)) (j 0))
            (:instance bits-bounds (x b) (i (1- k)) (j 0)))))
   (defruled lemma
     (implies
      (and (natp n)
           (integerp a)
           (integerp b)
           (natp k)
           (< k n)
           (bvecp c 1))
      (and (iff (equal (bits (+ a b c) k 0) 0)
                (equal (bits (logxor (logxor a b)
                                     (cat (logior a b) n c 1))
                             k 0)
                       0))
           (cond ((>= (+ (bits a k 0) (bits b k 0) c) (expt 2 (1+ k)))
                  (>= (+ (bitn a k) (bitn b k)) 1))
                 ((equal (bits (+ a b c) k 0) 0)
                  (= (+ (bitn a k) (bitn b k)) 0))
                 (t (<= (+ (bitn a k) (bitn b k)) 1)))))
     :induct (sub1-induction k)
     :hints
     (("subgoal *1/2"
       :use (lemma-sum=0
             lemma-logxor=0
             lemma-carry
             (:instance bvecp-0-1 (x (bitn a k)))))
      ("subgoal *1/1" :in-theory (enable bitn-x+y+cin bitn-logxor bitn-cat)
       :use (:instance bitn-0-1 (x a) (n 0)))))))
