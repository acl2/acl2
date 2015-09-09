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

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)
(include-book "float")
(local (include-book "../lib3/top"))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))
(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defun cat-size (x)
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x)
                      ,(cadr x)
                      (cat ,@(cddr x))
                      ,(cat-size (cddr x))))))

(defund mulcat (l n x)
  (declare (xargs :guard (and (integerp l) (< 0 l) (acl2-numberp n) (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))


;;;**********************************************************************
;;;                 Ripple-Carry-Adders and Compression Trees
;;;**********************************************************************

(defthm half-adder
  (implies (and (bvecp u 1)
                (bvecp v 1))
           (equal (+ u v)
                  (cat (logand u v) 1 (logxor u v) 1)))
  :rule-classes ())

(defthm add-2
    (implies (and (natp x) (natp y))
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
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (= (+ x y z)
		(+ (logxor x (logxor y z))
		   (* 2 (logior (logand x y)
				(logior (logand x z)
					(logand y z)))))))
  :rule-classes ())

(defun rc-carry (x y k)
  (if (zp k)
      0
    (logior (logand (bitn x (1- k)) (bitn y (1- k)))
	    (logior (logand (bitn x (1- k)) (rc-carry x y (1- k)))
		    (logand (bitn y (1- k)) (rc-carry x y (1- k)))))))

(defun rc-sum (x y k)
  (if (zp k)
      0
    (cat (logxor (bitn x (1- k))
		 (logxor (bitn y (1- k)) (rc-carry x y (1- k))))
	 1
	 (rc-sum x y (1- k))
	 (1- k))))

(defthm ripple-carry
  (implies (and (natp x)
                (natp y)
                (natp n))
           (equal (+ (bits x (1- n) 0) (bits y (1- n) 0))
                  (cat (rc-carry x y n) 1 (rc-sum x y n) n)))
  :rule-classes ())

(local (defun nats (n) (if (zp n) () (cons (1- n) (nats (1- n))))))

(local (defthm bvecp-member-1
  (implies (and (natp x)
                (natp n)
                (< x n))
           (member x (nats n)))
  :rule-classes ()))

(local (defthm bvecp-member
  (implies (and (natp n)
                (bvecp x n))
           (member x (nats (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bvecp-member-1 (n (expt 2 n))))
                  :in-theory (enable bvecp)))))

(defthmd compress-bit-5-3
  (implies (and (bvecp u 1)
                (bvecp v 1)
                (bvecp w 1)
                (bvecp x 1)
                (bvecp c 1))
           (equal (+ u v w x c)
                  (let ((xor4 (logxor u (logxor v (logxor w x)))))
                    (+ (logxor xor4 c)
                       (* 2 (+ (logior (logand xor4 c) (logand (lognot xor4) x))
                               (logior (logand u v) (logior (logand u w) (logand v w)))))))))
  :hints (("Goal" :use ((:instance bvecp-member (x u) (n 1))
                        (:instance bvecp-member (x v) (n 1))
                        (:instance bvecp-member (x w) (n 1))
                        (:instance bvecp-member (x x) (n 1))
                        (:instance bvecp-member (x c) (n 1))))))

(defun xor4 (u v w x)
  (logxor u (logxor v (logxor w x))))

(defun cout1 (u v w)
  (logior (logand u v) (logior (logand u w) (logand v w))))

(defun cout2 (u v w x cin)
  (logior (logand (xor4 u v w x) cin)
          (logand (lognot (xor4 u v w x)) x)))

(defun sout (u v w x cin)
  (logxor (xor4 u v w x) cin))

(local (defun comp-4-2-induct (u v w x cin n)
   (declare (xargs :guard (and (natp n) (bvecp u n) (bvecp v n) (bvecp w n) (bvecp x n) (bvecp cin n))))
   (if (zp n)
      t
    (comp-4-2-induct (bits u (- n 2) 0)
                     (bits v (- n 2) 0)
                     (bits w (- n 2) 0)
                     (bits x (- n 2) 0)
                     (bits cin (- n 2) 0)
                     (1- n)))))

(local (defthmd logand-bitn-lognot-1
  (implies (and (integerp n)
                (integerp x)
                (integerp y))
           (equal (logand (bitn (lognot x) n) (bitn y n))
                  (logand (lognot (bitn x n)) (bitn y n))))
  :hints (("Goal" :cases ((< n 0))
                  :use ((:instance bits-lognot (i n) (j n))
                        bitn-0-1
                        (:instance bitn-0-1 (x y)))))))

(local (defthmd logand-bitn-lognot-2
  (implies (and (integerp n)
                (integerp x)
                (integerp y))
           (equal (logand (bitn y n) (bitn (lognot x) n))
                  (logand (bitn y n) (lognot (bitn x n)))))
  :hints (("Goal" :cases ((< n 0))
                  :use ((:instance bits-lognot (i n) (j n))
                        bitn-0-1
                        (:instance bitn-0-1 (x y)))))))

(local (defthmd logand-bvecp-2
  (implies (and (natp n)
                (bvecp x (1+ n))
                (integerp y))
           (equal (logand x (bits y n 0))
                  (logand x y)))
  :hints (("Goal" :use ((:instance bits-logand (i n) (j 0)))))))

(local (defthmd bits-lognot-bits
  (implies (and (integerp x)
                (natp i)
                (natp j)
                (natp k)
                (natp l)
                (<= l k)
                (<= k (- i j)))
           (equal (bits (lognot (bits x i j)) k l)
                  (bits (lognot x) (+ k j) (+ l j))))
  :hints (("Goal" :in-theory (enable bits-lognot)))))

(local (defthmd logand-bits-lognot
  (implies (and (integerp x)
                (integerp n)
                (bvecp y (1+ n)))
           (equal (logand y (bits (lognot x) n 0))
                  (logand y (lognot (bits x n 0)))))
  :hints (("Goal" :use ((:instance logand-bvecp-2 (x y) (y (lognot (bits x n 0)))))
                  :cases ((< n 0))
                  :in-theory (enable bits-lognot-bits)))))

(local (defthmd comp-4-2-1
  (implies (and (bvecp x1 n)
                (bvecp x2 n)
                (bvecp x3 n)
                (bvecp x4 n)
                (bvecp x5 n)
                (syntaxp (not (consp x1)))
                (not (zp n)))
           (equal (+ x1 x2 x3 x4 x5)
                  (+ (* (expt 2 (1- n))
                        (+ (bitn x1 (1- n))
                           (bitn x2 (1- n))
                           (bitn x3 (1- n))
                           (bitn x4 (1- n))
                           (bitn x5 (1- n))))
                     (bits x1 (- n 2) 0)
                     (bits x2 (- n 2) 0)
                     (bits x3 (- n 2) 0)
                     (bits x4 (- n 2) 0)
                     (bits x5 (- n 2) 0))))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x x1) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x x2) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x x3) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x x4) (n (1- n)) (m 0))
                        (:instance bitn-plus-bits (x x5) (n (1- n)) (m 0)))))))

(local (defthmd comp-4-2-2
  (implies (and (bvecp x1 n)
                (bvecp x2 n)
                (bvecp x3 n)
                (bvecp x4 n)
                (bvecp x5 n)
                (rationalp y)
                (syntaxp (not (consp x1)))
                (syntaxp (not (consp x2)))
                (syntaxp (not (consp x3)))
                (syntaxp (not (consp x4)))
                (syntaxp (not (consp x5)))
                (not (zp n)))
           (equal (+ (logxor x1 x2 x3 x4 x5) y)
                  (+ (* (expt 2 (1- n)) (bitn (logxor x1 x2 x3 x4 x5) (1- n)))
                     (bits (logxor x1 x2 x3 x4 x5) (- n 2) 0)
                     y)))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (logxor x1 x2 x3 x4 x5)) (n (1- n)) (m 0)))))))

(local (defthmd comp-4-2-3
  (implies (and (bvecp x n)
               ; (syntaxp (not (consp x)))
                (not (zp n)))
           (equal (cat x n 0 1)
                  (+ (* (expt 2 n) (bitn x (1- n)))
                     (cat (bits x (- n 2) 0) (1- n) 0 1))))
  :hints (("Goal" :in-theory (enable bits-cat bitn-cat)
                  :use ((:instance bitn-plus-bits (x (cat x n 0 1)) (m 0)))))))

;; Believe it or not, the proof of the following lemma depends on the alphabetical ordering
;; of the variables:

(local (defthm comp-4-2-4
  (implies (and (natp n)
                (bvecp u n)
                (bvecp v n)
                (bvecp w n)
                (bvecp x n)
                (bvecp zcin n))
           (equal (+ u v w x zcin)
                  (+ (sout u v w x zcin)
                     (cat (cout1 u v w) n 0 1)
                     (cat (cout2 u v w x zcin) n 0 1))))
  :rule-classes ()
  :hints (("Goal" :induct (comp-4-2-induct u v w x zcin n))
          ("Subgoal *1/2" :in-theory (enable comp-4-2-2 comp-4-2-3 comp-4-2-1 logand-bitn-lognot-1 logand-bitn-lognot-2
                                      compress-bit-5-3 bits-logior bits-logxor bits-logand
                                      logand-bits-lognot bitn-logior bitn-logxor bitn-logand)))))

(defthm compress-5-3
  (implies (and (natp n)
                (bvecp u n)
                (bvecp v n)
                (bvecp w n)
                (bvecp x n)
                (bvecp cin n))
           (equal (+ u v w x cin)
                  (+ (sout u v w x cin)
                     (cat (cout1 u v w) n 0 1)
                     (cat (cout2 u v w x cin) n 0 1))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance comp-4-2-4 (zcin cin))))))

(local (defthmd comp-4-2-6
  (implies (and (bvecp u n)
                (bvecp v n)
                (bvecp w n)
                (natp n)
                (syntaxp (atom n)))
           (EQUAL (LOGIOR (LOGAND U V)
                          (LOGAND U W)
                          (LOGAND V W))
                  (+ (LOGIOR (LOGAND (BITS U (+ -2 N) 0)
                                     (BITS V (+ -2 N) 0))
                             (LOGAND (BITS U (+ -2 N) 0)
                                     (BITS W (+ -2 N) 0))
                             (LOGAND (BITS V (+ -2 N) 0)
                                     (BITS W (+ -2 N) 0)))
                     (* (EXPT 2 (+ -1 N))
                        (LOGIOR (LOGAND (BITN U (+ -1 N))
                                        (BITN V (+ -1 N)))
                                (LOGAND (BITN U (+ -1 N))
                                        (BITN W (+ -1 N)))
                                (LOGAND (BITN V (+ -1 N))
                                        (BITN W (+ -1 N))))))))
  :hints (("Goal" :in-theory (enable bits-logand bitn-logand bits-logior bitn-logior)
                  :use ((:instance bitn-plus-bits (x (LOGIOR (LOGAND U V) (LOGAND U W) (LOGAND V W))) (n (1- n)) (m 0)))))))

(defthmd compress-4-2
  (implies (and (natp n)
                (bvecp u n)
                (bvecp v n)
                (bvecp w n)
                (bvecp x n)
                (bvecp c0 1))
           (let ((xor4 (logxor u (logxor v (logxor w x))))
                 (c (cat (logior (logand u v) (logior (logand u w) (logand v w))) n c0 1)))
             (equal (+ u v w x c0)
                    (+ (logxor xor4 (bits c (1- n) 0))
                       (* 2 (logior (logand xor4 (bits c (1- n) 0)) (logand (lognot xor4) x)))
                       (* (expt 2 n) (bitn c n))))))
  :hints (("Goal" :use ((:instance compress-5-3 (cin (bits (cat (cout1 u v w) n c0 1) (1- n) 0))))
                  :in-theory (enable bits-logxor bitn-logxor bits-logand bitn-logand bits-logior bitn-logior bits-cat bitn-cat))
          ("Subgoal 1.2'''" :in-theory (enable cat))
          ("Subgoal 1.1''" :in-theory (enable bits-logxor bitn-logxor bits-logand bitn-logand bits-logior bitn-logior
                                       logand-bitn-lognot-1 logand-bitn-lognot-2 logand-bits-lognot bits-cat bitn-cat)
                           :expand ((CAT (LOGIOR (LOGAND X (LOGNOT (LOGXOR U V W X)))
                                                 (LOGAND (LOGXOR U V W X)
                                                         (CAT (LOGIOR (LOGAND (BITS U (+ -2 N) 0)
                                                                              (BITS V (+ -2 N) 0))
                                                                      (LOGAND (BITS U (+ -2 N) 0)
                                                                              (BITS W (+ -2 N) 0))
                                                                      (LOGAND (BITS V (+ -2 N) 0)
                                                                              (BITS W (+ -2 N) 0)))
                                                              (+ -1 N)
                                                              C0 1)))
                                         N 0 1)))
          ("Subgoal 1.1'''" :in-theory (enable cat))
          ("Subgoal 1.1'4'" :in-theory (enable comp-4-2-6))))


;;;**********************************************************************
;;;                      Carry-Look-Ahead Adders
;;;**********************************************************************

(defun gen (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
  (if (and (natp i) (natp j) (>= i j))
      (if (= (bitn x i) (bitn y i))
	  (bitn x i)
	(gen x y (1- i) j))
    0))

(defun prop (x y i j)
  (declare (xargs :measure (nfix (1+ i))))
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
  (implies (and (natp j) (>= i j))
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
  (implies (and (natp x)
                (natp y)
		(natp i))
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
                (natp x)
                (natp y))
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
  (implies (and (natp x)
                (natp y)
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
                (natp x)
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
  (implies (and (natp x)
                (natp y)
		(natp k)
		(bvecp z (1+ k))
		(= (logand z y) 0)
		(= (gen x y k 0) 1))
	   (equal (gen (+ x y) z k 0) 0)))

(defthmd gen-extend-3
    (implies (and (natp i)
		  (natp j)
		  (> i j)
		  (natp x)
		  (natp y)
		  (bvecp z (1+ j))
		  (= (logand y z) 0))
	     (equal (gen (+ x y) z i 0)
		    (logand (prop x y i (1+ j))
			    (gen (+ x y) z j 0)))))


;;;**********************************************************************
;;;                  Leading One Prediction
;;;**********************************************************************

(defund lop (a b d k)
  (let ((c (- (bitn a (1- k)) (bitn b (1- k)))))
    (if (and (integerp k) (>= k 0))
	(if (= k 0)
	    0
	  (if (= d 0)
	      (lop a b c (1- k))
	    (if (= d (- c))
		(lop a b (- c) (1- k))
	      k)))
      0)))

(defthm lop-bnds
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (>= a 0)
                (>= b 0)
                (>= n 0)
                (not (= a b))
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (or (= (lop a b 0 n) (expo (- a b)))
               (= (lop a b 0 n) (1+ (expo (- a b))))))
  :rule-classes ())

(defthm lop-thm-1
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (= e (expo a))
		  (< (expo b) e)
		  (= lambda
		     (logior (* 2 (mod a (expt 2 e)))
			     (bits (lognot (* 2 b)) e 0))))
	     (or (= (expo (- a b)) (expo lambda))
		 (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())

(defun lamt (a b e)
  (logxor a (bits (lognot b) e 0)))

(defun lamg (a b e)
  (logand a (bits (lognot b) e 0)))

(defun lamz (a b e)
  (bits (lognot (logior a (bits (lognot b) e 0))) e 0))

(defun lam1 (a b e)
  (logand (bits (lamt a b e) e 2)
	  (logand (bits (lamg a b e) (1- e) 1)
		  (bits (lognot (lamz a b e)) (- e 2) 0))))

(defun lam2 (a b e)
  (logand (bits (lognot (lamt a b e)) e 2)
	  (logand (bits (lamz a b e) (1- e) 1)
		  (bits (lognot (lamz a b e)) (- e 2) 0))))

(defun lam3 (a b e)
  (logand (bits (lamt a b e) e 2)
	  (logand (bits (lamz a b e) (1- e) 1)
		  (bits (lognot (lamg a b e)) (- e 2) 0))))

(defun lam4 (a b e)
  (logand (bits (lognot (lamt a b e)) e 2)
	  (logand (bits (lamg a b e) (1- e) 1)
		  (bits (lognot (lamg a b e)) (- e 2) 0))))

(defun lam0 (a b e)
  (logior (lam1 a b e)
	  (logior (lam2 a b e)
		  (logior (lam3 a b e)
			  (lam4 a b e)))))

(defun lamb (a b e)
  (+ (* 2 (lam0 a b e))
     (bitn (lognot(lamt a b e)) 0)))

(defthm lop-thm-2
    (implies (and (integerp a)
		  (> a 0)
		  (integerp b)
		  (> b 0)
		  (not (= a b))
		  (= e (expo a))
		  (= e (expo b))
		  (> e 1))
	     (and (not (= (lamb a b e) 0))
		  (or (= (expo (- a b)) (expo (lamb a b e)))
		      (= (expo (- a b)) (1- (expo (lamb a b e)))))))
  :rule-classes ())


;;;**********************************************************************
;;;                    Trailing One Prediction
;;;**********************************************************************

(defthm top-thm-1
  (implies (and (natp n)
                (natp k)
                (< k n)
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
