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

(defthmd lutz-lemma
   (implies (and (integerp x) (integerp y) (natp n))
            (and (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                      (= (bits (logxor x y) (1- n) 0) (1- (expt 2 n))))
                 (iff (= (bits (+ x y) (1- n) 0) (1- (expt 2 n)))
                      (= (+ (bits x (1- n) 0) (bits y (1- n) 0)) (1- (expt 2 n)))))))

(defun rc-carry (x y k)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp k))))
  (if (zp k)
      0
    (logior (logand (bitn x (1- k)) (bitn y (1- k)))
	    (logior (logand (bitn x (1- k)) (rc-carry x y (1- k)))
		    (logand (bitn y (1- k)) (rc-carry x y (1- k)))))))

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

(defthm ripple-carry
  (implies (and (integerp x)
                (integerp y)
                (natp n))
           (equal (+ (bits x (1- n) 0) (bits y (1- n) 0))
                  (cat (rc-carry x y n) 1 (rc-sum x y n) n)))
  :rule-classes ())

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

(defthmd gen-val
  (implies (natp j)
           (equal (gen x y i j)
                  (if (>= (+ (bits x i j) (bits y i j))
                          (expt 2 (1+ (- i j))))
                      1
                    0))))

(defthmd gen-val-cor1
  (implies (natp j)
           (equal (gen x y i j)
                  (bitn (+ (bits x i j) (bits y i j))
			(1+ (- i j))))))

(defthmd gen-val-cor2
  (implies (and (integerp x)
                (integerp y))
           (equal (+ (bits x i 0) (bits y i 0))
		  (+ (* (expt 2 (1+ i)) (gen x y i 0))
		     (bits (+ x y) i 0)))))

(defthm gen-special-case
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (bitn (+ (bits x i j) (bits y i j)) (- i j)) 0))
           (equal (gen x y i j)
                  (logior (bitn x i) (bitn y i))))
  :rule-classes ())

(defthmd prop-val
  (implies (and (integerp i) (natp j) (>= i j))
           (equal (prop x y i j)
                  (if (= (+ (bits x i j) (bits y i j))
                         (1- (expt 2 (1+ (- i j)))))
                      1
                    0))))

(defthmd prop-as-logxor
  (implies (and (natp i)
                (natp j)
                (<= j i)
                (integerp x)
                (integerp y))
           (equal (prop x y i j)
                  (if (equal (logxor (bits x i j) (bits y i j))
                             (1- (expt 2 (1+ (- i j)))))
                      1
                    0))))

(defthm gen-extend
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

(defthm gen-extend-cor
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
  :rule-classes ())

(defthm prop-extend
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

(defthm bits-sum
  (implies (and (integerp x) (integerp y))
           (equal (bits (+ x y) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (gen x y (1- j) 0))
                        (- i j) 0)))
  :rule-classes ())

(defthm bits-sum-shift
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
    :rule-classes ())

(defthmd bits-sum-swallow
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
                  (bits x i j))))

(defthmd bits-sum-cor
  (implies (and (integerp x)
                (integerp y)
                (>= i j)
                (>= j 0)
                (= (gen x y i j) 0)
                (= (gen x y (1- j) 0) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j)))))

(defthm bits-sum-3
  (implies (and (integerp x) (integerp y) (integerp z))
           (equal (bits (+ x y z) i j)
                  (bits (+ (bits x i j)
                           (bits y i j)
                           (bits z i j)
                           (gen x y (1- j) 0)
                           (gen (+ x y) z (1- j) 0))
                        (- i j) 0)))
  :rule-classes ())

(defthm bits-sum-plus-1
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
				     (gen x y (1- j) 0) ))
			  (- i j) 0)))
  :rule-classes ())

(defthmd logand-gen-0
  (implies (and (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand (bits x i j) (bits y i j)) 0))
           (equal (gen x y i j) 0)))


(defthm logand-gen-0-cor
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp j)
                (>= i j)
                (>= j 0)
                (= (logand x y) 0))
           (equal (bits (+ x y) i j)
                  (+ (bits x i j) (bits y i j))))
  :rule-classes ())

(defthmd gen-plus
  (implies (and (integerp x)
                (integerp y)
                (integerp z)
		(natp k)
		(= (logand z y) 0)
		(= (gen x y k 0) 1))
	   (equal (gen (+ x y) z k 0) 0)))

(defthmd gen-extend-3
    (implies (and (natp i)
		  (natp j)
		  (> i j)
		  (integerp x)
		  (integerp y)
                  (bvecp z (1+ j))
		  (= (logand y z) 0))
	     (equal (gen (+ x y) z i 0)
		    (logand (prop x y i (1+ j))
			    (gen (+ x y) z j 0)))))
)

;;;**********************************************************************
;;;                  Leading One Prediction
;;;**********************************************************************

(defsection-rtl |Leading One Prediction| |Addition|

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
