; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   david@russinoff.com
;   1106 W 9th St., Austin, TX 78703
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;;**********************************************************************
;;;                      Bit Vector Addition
;;;**********************************************************************

(defsection-rtl |Bit Vector Addition| |Addition|

(defthm half-adder
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat (logand u v) 1 (logxor u v) 1)))
  :rule-classes ())

(defthm add-2
    (implies (and (integerp x) (integerp y))
	     (equal (+ x y)
		    (+ (logxor x y)
		       (* 2 (logand x y)))))
  :rule-classes ())

(defthm full-adder
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1))
           (equal (+ u v w)
                  (cat (logior (logand u v) (logior (logand u w) (logand v w))) 1
                       (logxor u (logxor v w)) 1)))
  :rule-classes ())

(defthm add-3
    (implies (and (integerp x)
		  (integerp y)
		  (integerp z))
	     (= (+ x y z)
		(+ (logxor x (logxor y z))
		   (* 2 (logior (logand x y)
				(logior (logand x z)
					(logand y z)))))))
    :rule-classes ())

(defthmd plus-logior-logand
  (implies (and (integerp x)
                (integerp y))
           (equal (+ x y)
                  (- (* 2 (logior x y))
                     (logxor x y)))))

(defthmd lutz-lemma
   (implies (and (integerp x) (integerp y) (natp n))
            (and (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                      (= (bits (logxor x y) (1- n) 0) (1- (expt 2 n))))
                 (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                      (= (+ (bits x (1- n) 0) (bits y (1- n) 0)) (1- (expt 2 n)))))))

(defund cbit (x y cin k)
  (if (zp k)
      cin
    (logior (logand (bitn x (1- k)) (bitn y (1- k)))
	    (logior (logand (bitn x (1- k)) (cbit x y cin (1- k)))
		    (logand (bitn y (1- k)) (cbit x y cin  (1- k)))))))

(defthmd ripple-carry-lemma
  (implies (and (integerp x)
                (integerp y)
                (bitp cin)
		(natp i))
	   (equal (bitn (+ x y cin) i)
		  (logxor (logxor (bitn x i) (bitn y i))
			  (cbit x y cin i)))))


;;;**********************************************************************
;;;                 Parallel Prefix Adders
;;;**********************************************************************

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

(defthm bvecp-1-gen
  (bvecp (gen x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((gen x y i j)))))

(defthm bvecp-1-prop
  (bvecp (prop x y i j) 1)
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((prop x y i j)))))

(defthmd gen-i-i
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (gen x y i i)
		  (logand (bitn x i) (bitn y i))))
  :hints (("Goal" :in-theory (enable gen) :use ((:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

(defthmd prop-i-i
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (prop x y i i)
		  (logxor (bitn x i) (bitn y i))))
  :hints (("Goal" :expand ((prop x y i i))
                  :use ((:instance bitn-0-1 (n i)) (:instance bitn-0-1 (x y) (n i))))))

(defthmd gen-val
  (implies (natp j)
           (equal (gen x y i j)
                  (if (>= (+ (bits x i j) (bits y i j))
                          (expt 2 (1+ (- i j))))
                      1
                    0))))

(defthm bits-sum
  (implies (and (integerp x) (integerp y))
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (gen x y (1- j) 0))
                        (- i j) 0)))
  :rule-classes ())

(defthmd prop-val
  (implies (and (integerp i) (natp j) (>= i j))
           (equal (prop x y i j)
                  (if (= (+ (bits x i j) (bits y i j))
                         (1- (expt 2 (1+ (- i j)))))
                      1
                    0))))

(defund gp (x y i j)
  (cons (gen x y i j) (prop x y i j)))

(defund gp0 (x y i)
  (gp x y i i))

(defund fco (gp1 gp2)
  (cons (logior (car gp1) (logand (cdr gp1) (car gp2)))
	(logand (cdr gp1) (cdr gp2))))

(defthmd fco-assoc
  (implies (and (bitp g1) (bitp p1)
		(bitp g2) (bitp p2)
		(bitp g3) (bitp p3))
	   (equal (fco (fco (cons g1 p1) (cons g2 p2))
		       (cons g3 p3))
		  (fco (cons g1 p1)
		       (fco (cons g2 p2) (cons g3 p3))))))

(defthmd gp-decomp
  (implies (and (integerp x)
		(integerp y)
		(natp j)
		(natp i)
		(natp k)
		(<= j k)
		(< k i))
	   (equal (fco (gp x y i (1+ k)) (gp x y k j))
		  (gp x y i j))))

(defthmd cbit-rewrite
  (implies (and (integerp x)
		(integerp y)
		(bitp cin)
		(natp i))
	   (equal (cbit x y cin (1+ i))
		  (logior (gen x y i 0)
			  (logand (prop x y i 0) cin)))))

(defun rc (x y i)
  (if (zp i)
      (gp0 x y 0)
    (fco (gp0 x y i) (rc x y (1- i)))))

(defthmd rc-correct
  (implies (and (integerp x)
		(integerp y)
		(natp i))
	   (equal (rc x y i)
		  (gp x y i 0))))

(defun lf (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< (mod i (expt 2 d)) (expt 2 (1- d)))
	(lf x y i (1- d))
      (fco (lf x y i (1- d))
	   (lf x y
	       (+ (chop i (- d)) (expt 2 (1- d)) -1)
	       (1- d))))))

(defthmd lf-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (lf x y i d)
		  (gp x y i (chop i (- d))))))

(defthmd lf-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (lf x y i n)
		  (gp x y i 0))))

(defund ks (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< i (expt 2 (1- d)))
	(ks x y i (1- d))
      (fco (ks x y i (1- d))
	   (ks x y (- i (expt 2 (1- d))) (1- d))))))

(defthmd ks-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (ks x y i d)
		  (gp x y i (max 0 (1+ (- i (expt 2 d))))))))

(defthmd ks-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (ks x y i n)
		  (gp x y i 0))))

(defund pi2 (k)
  (if (zp k)
      0
    (if (integerp (/ k 2))
	(1+ (pi2 (/ k 2)))
      0)))

(defthmd pi2-upper
  (implies (not (zp k))
	   (<= (expt 2 (pi2 k)) k)))

(defthmd pi2-lemma
  (implies (and (not (zp k)) (integerp p))
           (iff (integerp (/ k (expt 2 p)))
	        (<= p (pi2 k)))))

(defund bk0 (x y i d)
  (if (zp d)
      (gp0 x y i)
    (if (< (pi2 (1+ i)) d)
	(bk0 x y i (1- d))
      (fco (bk0 x y i (1- d))
	   (bk0 x y (- i (expt 2 (1- d))) (1- d))))))

(defund bk (x y i n)
  (declare (xargs :hints (("Goal" :use ((:instance pi2-upper (k (1+ i))))))))
  (let ((p (pi2 (1+ i))))
    (if (or (zp n) (not (bvecp i n)) (= i (1- (expt 2 p))))
        (bk0 x y i n)
      (fco (bk0 x y i n)
	   (bk x y (- i (expt 2 p)) n)))))

(defthmd bk0-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp d))
	   (equal (bk0 x y i d)
	          (gp x y i (1+ (- i (expt 2 (min (pi2 (1+ i)) d))))))))

(defthmd bk0-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (bk0 x y i n)
		  (gp x y i (1+ (- i (expt 2 (pi2 (1+ i)))))))))

(defthmd bk-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(bvecp i n))
	   (equal (bk x y i n)
		  (gp x y i 0))))

(defund hc0 (x y i k d)
  (let ((p (pi2 (1+ i))))
    (if (or (zp d) (< p k))
	(bk0 x y i k)
      (if (< i (expt 2 (+ k d -1)))
	  (hc0 x y i k (1- d))
	(fco (hc0 x y i k (1- d))
	     (hc0 x y (- i (expt 2 (+ k d -1))) k (1- d)))))))

(defund hc (x y i k n)
  (declare (xargs :hints (("Goal" :use ((:instance pi2-upper (k (1+ i))))))))
  (let ((p (pi2 (1+ i))))
    (if (or (zp n) (not (bvecp i n)) (>= (pi2 (1+ i)) k) (= i (1- (expt 2 p))))
	(hc0 x y i k (- n k))
      (fco (hc0 x y i k (- n k))
           (hc x y (- i (expt 2 p)) k n)))))

(defthmd hc0-correct-gen
  (implies (and (integerp x)
		(integerp y)
		(natp i)
		(natp k)
		(natp d)
		(>= (pi2 (1+ i)) k))
	   (let ((m (max 0 (- (1+ i) (expt 2 (+ k d))))))
	     (equal (hc0 x y i k d)
		    (gp x y i m)))))

(defthmd hc0-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(natp k)
		(<= k n)
		(bvecp i n)
		(integerp (/ (1+ i) (expt 2 k))))
	   (equal (hc0 x y i k (- n k))
		  (gp x y i 0))))

(defthmd hc-correct
  (implies (and (integerp x)
		(integerp y)
		(natp n)
		(natp k)
		(<= k n)
		(bvecp i n))
	   (equal (hc x y i k n)
		  (gp x y i 0))))
)

;;;**********************************************************************
;;;                  Leading One Prediction
;;;**********************************************************************

(defsection-rtl |Leading One Prediction| |Addition|

(defund u0 (x y n)
  (bits (logior x (lognot y)) (- n 2) 0))

(defthmd lza-thm-0-a
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2)))
	   (iff (equal (- x y) 1)
	        (equal (u0 x y n) 0))))

(defthmd lza-thm-0-b
  (implies (and (natp n)
                (> n 1)
                (natp x)
		(natp y)
		(= (expo x) (1- n))
		(= (expo y) (- n 2))
		(not (= (u0 x y n) 0)))
           (and (<= (expo (u0 x y n)) (expo (- x y)))
	        (<= (expo (- x y)) (1+ (expo (u0 x y n)))))))

(defund p0 (a b)
  (declare (xargs :guard (and (integerp a)
                              (integerp b))))
  (logxor a b))

(defund g0 (a b)
  (declare (xargs :guard (and (integerp a)
                              (integerp b))))
  (logand a b))

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

(defthmd g0-rewrite
  (implies (and (integerp a)
                (integerp b)
		(integerp j))
	   (equal (bitn (g0 a b) j)
	          (if (and (= (bitn a j) 1) (= (bitn b j) 1))
		      1 0))))

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

(defthmd lza-thm-1-case-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (+ a b) (expt 2 n)))
	   (equal (w0 a b n)
	          1)))

(defthm lza-thm-1-case-2
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (> (+ a b) (expt 2 n)))
           (and (>= (w0 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w0 a b n)))))
                (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w0 a b n)))
                    (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w0 a b n)))))))
  :rule-classes ())

(defund z1 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (logior (logand (logxor (bits (p0 a b) n 1) (k0 a b n))
		  (logxor (p0 a b) (* 2 (k0 a b n))))
	  (logand (logxor (bits (p0 a b) n 1) (g0 a b))
		  (logxor (p0 a b) (* 2 (g0 a b))))))

(defund w1 (a b n)
  (declare (xargs :guard (and (integerp a)
                              (integerp b)
                              (integerp n))))
  (bits (lognot (z1 a b n)) (- n 2) 0))

(defthmd w1-rewrite
  (implies (and (integerp a)
                (integerp b)
		(not (zp n))
                (not (zp j))
		(< j (1- n)))
	   (equal (bitn (w1 a b n) j)
	          (if (and (or (= (bitn (p0 a b) (1+ j)) (bitn (k0 a b n) j))
		               (= (bitn (p0 a b) j) (bitn (k0 a b n) (1- j))))
			   (or (= (bitn (p0 a b) (1+ j)) (bitn (g0 a b) j))
			       (= (bitn (p0 a b) j) (bitn (g0 a b) (1- j)))))
		      1 0))))

(defthmd lza-thm-2-case-1
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
                (= (+ a b) (1- (expt 2 n)))
		(natp i))
	   (equal (w1 a b n) 0)))

(defthmd lza-thm-2-case-2
  (implies (and (natp n)
                (> n 1)
                (bvecp a n)
                (bvecp b n)
		(or (= (+ a b) (expt 2 n))
		    (= (+ a b) (- (expt 2 n) 2))))
	   (equal (w1 a b n)
	          1)))

(defthm lza-thm-2-case-3
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (> (+ a b) (expt 2 n)))
           (and (>= (w1 a b n) 2)
                (or (= (expo (bits (+ a b) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (+ a b) (1- n) 0)) (1- (expo (w1 a b n)))))
                (or (= (expo (bits (+ a b 1) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (+ a b 1) (1- n) 0)) (1- (expo (w1 a b n)))))))
  :rule-classes ())

(defthm lza-thm-2-case-4
  (implies (and (not (zp n))
                (bvecp a n)
                (bvecp b n)
		(= (bitn (p0 a b) (1- n)) 1)
                (< (+ a b) (- (expt 2 n) 2)))
           (and (>= (w1 a b n) 2)
                (or (= (expo (bits (lognot (+ a b)) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (lognot (+ a b)) (1- n) 0)) (1- (expo (w1 a b n)))))
                (or (= (expo (bits (lognot (+ a b 1)) (1- n) 0)) (expo (w1 a b n)))
                    (= (expo (bits (lognot (+ a b 1)) (1- n) 0)) (1- (expo (w1 a b n)))))))
  :rule-classes ())


;; Leading zero counter:

(defund zseg (x k i)
  (if (zp k)
      (if (= (bitn x i) 0)
	  1
	0)
    (if (and (= (zseg x (1- k) (1+ (* 2 i))) 1)
	     (= (zseg x (1- k) (* 2 i)) 1))
	1
      0)))

(defund zcount (x k i)
  (if (zp k)
      0
    (if (= (zseg x (1- k) (1+ (* 2 i))) 1)
	(logior (expt 2 (1- k)) (zcount x (1- k) (* 2 i)))
      (zcount x (1- k) (1+ (* 2 i))))))

(defund clz (x n)
  (zcount x n 0))

(defthmd clz-thm
  (implies (and (natp n)
                (bvecp x (expt 2 n))
		(> x 0))
	   (equal (clz x n)
	          (- (1- (expt 2 n)) (expo x)))))

)

;;;**********************************************************************
;;;                    Trailing One Prediction
;;;**********************************************************************

(defsection-rtl |Trailing One Prediction| |Addition|

(defthm top-thm-1
  (implies (and (natp k)
                (integerp a)
                (integerp b))
           (equal (equal (bits (+ a b 1) k 0) 0)
		  (equal (bits (lognot (logxor a b)) k 0) 0)))
  :rule-classes ())

(defthm top-thm-2
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
  :rule-classes ())
)
