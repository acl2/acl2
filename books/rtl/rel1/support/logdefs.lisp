;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(include-book "floor")

(defun BITN (x n)
  (if (logbitp n x) 1 0))

(local
 (defthm bitn-def-1
     (implies (and (integerp x)
		   (>= x 0))
	      (iff (evenp x)
		   (= (fl (/ x 2))  (/ x 2))))
   :rule-classes ()))

(local
 (defthm bitn-def-2
     (implies (and (rationalp x) (rationalp y))
	      (iff (= x y) (= (* 2 x) (* 2 y))))
   :rule-classes ()))

(local
 (defthm bitn-def-3
     (implies (and (integerp x)
		   (>= x 0))
	      (iff (evenp x)
		   (= (* 2 (fl (/ x 2)))
		      x)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def-1)
			 (:instance bitn-def-2 (x (/ x 2)) (y (fl (/ x 2)))))))))

(local
 (defthm bitn-def-4
     (implies (and (integerp x)
		   (>= x 0))
	      (iff (evenp x)
		   (= (rem x 2) 0)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def-3)
			 (:instance rem-fl (m x) (n 2)))))))

(local
(defthm bitn-def-5
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0))
	     (iff (= (bitn x n) 0)
		  (evenp (fl (/ x (expt 2 n))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor-fl (m x) (n (expt 2 n))))))))

(local
(defthm bitn-def-6
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0))
	     (iff (= (bitn x n) 0)
		  (= (rem (fl (/ x (expt 2 n)))
			  2)
		     0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def-4 (x (fl (/ x (expt 2 n)))))
			(:instance bitn-def-5))))))

(defthm REM012
    (implies (and (integerp x)
		  (>= x 0))
	     (or (= (rem x 2) 0)
		 (= (rem x 2) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem<n (m x) (n 2))
			(:instance rem>=0 (m x) (n 2))))))

(defthm BITN-DEF
    (implies (and (integerp x)
		  (integerp k)
		  (>= x 0)
		  (>= k 0))
	     (equal (bitn x k)
		    (rem (fl (/ x (expt 2 k)))
			 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def-6 (n k))
			 (:instance rem012 (x (fl (/ x (expt 2 k)))))))))

(progn

; Matt K. mod: The addition of natp-bitn, and the corresponding disable of (:t
; bitn), produces the state that existed before April 2016, when ACL2 started
; providing a type-set bit for the set {1}.  Without the changes, the following
; community books failed to certify after that ACL2 change (and a few still
; fail without additional changes).

;   rtl/rel1/support/fadd/add3.lisp
;   rtl/rel1/support/fadd/stick.lisp
;   rtl/rel1/support/fadd/top.lisp
;   rtl/rel1/support/merge.lisp
;   rtl/rel1/support/fadd/lop2.lisp
;   rtl/rel1/support/fadd/lop3.lisp
;   workshops/1999/multiplier/proof.lisp

; Technical Note: For the four books just above, only, the book certifies if
; for the all-type-reasoning-tags-p case in rewrite-atm, we add a COND clause
; that avoids returning any change in the case that the atom is a call of IF.

  (defthm natp-bitn
    (natp (bitn x n))
    :rule-classes :type-prescription)

  (in-theory (disable bitn (:t bitn)))
  )

(defthm BITN-ALT-0
    (implies (and (integerp x)
		  (>= x 0))
	     (equal (bitn x 0)
		    (rem x 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def (k 0))))))

(defthm BITN-ALT-POS
    (implies (and (integerp x)
		  (integerp k)
		  (>= x 0)
		  (> k 0))
	     (equal (bitn x k)
		    (bitn (fl (/ x 2)) (1- k))))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def)
			 (:instance bitn-def (x (fl (/ x 2))) (k (1- k)))
			 (:instance fl/int (x (/ x 2)) (n (expt 2 (1- k))))))))

(local
(defthm bit-rem-1
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (rem (fl (/ (+ (* (expt 2 n) (fl (/ x (expt 2 n))))
				   (rem x (expt 2 n)))
				(expt 2 k)))
			 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bitn-def)
			 (:instance rem-fl (m x) (n (expt 2 n))))))))

(local
 (defthm bit-rem-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (rem (fl (+ (* (expt 2 (- n k)) (fl (/ x (expt 2 n))))
				(/ (rem x (expt 2 n))
				   (expt 2 k))))
			 2)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable a15)
		   :use ((:instance bit-rem-1)
			 (:instance expt- (a n) (b k)))))))

 (defthm INTEGERP-EXPT-TYPE
    (implies (and (integerp n)
		  (>= n 0))
	     (integerp (expt 2 n)))
  :rule-classes (:type-prescription))

(local
(defthm bit-rem-3
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (>= n 0)
		  (> n k))
	     (equal (rem (fl (+ (* (expt 2 (- n k)) (fl (/ x (expt 2 n))))
				(/ (rem x (expt 2 n))
				   (expt 2 k))))
			 2)
		    (rem (+ (* (expt 2 (- n k)) (fl (/ x (expt 2 n))))
			    (fl	(/ (rem x (expt 2 n))
				   (expt 2 k))))
			 2)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable a10)
		   :use ((:instance integerp-expt-type (n (- n k)))
			 (:instance fl+int
				    (x (/ (rem x (expt 2 n)) (expt 2 k)))
				    (n (* (expt 2 (- n k)) (fl (/ x (expt 2 n)))))))))))

(local
(defthm bit-rem-4
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (rem (+ (* (expt 2 (- n k)) (fl (/ x (expt 2 n))))
			    (fl	(/ (rem x (expt 2 n))
				   (expt 2 k))))
			 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bit-rem-3)
			 (:instance bit-rem-2))))))

(local
(defthm bit-rem-5
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (rem (+ (* 2 (expt 2 (1- (- n k))) (fl (/ x (expt 2 n))))
			    (fl	(/ (rem x (expt 2 n))
				   (expt 2 k))))
			 2)))
   :rule-classes ()
   :hints (("Goal" :use ((:instance bit-rem-4))))))

(local
(defthm bit-rem-6
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (>= (* (EXPT 2 (+ -1 N (* -1 K)))
                    (FL (* 1/2 X (/ (EXPT 2 (+ -1 N))))))
		 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance n<=fl (n 0) (x (* 1/2 X (/ (EXPT 2 (+ -1 N))))))
			(:instance expt-pos (x (1- (- n k)))))))))

(local
(defthm bit-rem-7
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (>= (FL (* (/ (EXPT 2 K))
			(REM X (* 2 (EXPT 2 (+ -1 N))))))
		 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance n<=fl (n 0) (x (* (/ (EXPT 2 K)) (REM X (* 2 (EXPT 2 (+ -1 N)))))))
			(:instance expt-pos (x k))
			(:instance rem>=0 (m x) (n (* 2 (EXPT 2 (+ -1 N)))))
			(:instance expt-pos (x (1- n))))))))

(local
(defthm bit-rem-8
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (rem (fl (/ (rem x (expt 2 n))
				(expt 2 k)))
			 2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-rem-5)
			(:instance integerp-expt-type (n (1- (- n k))))
			(:instance bit-rem-6)
			(:instance bit-rem-7)
			(:instance rem+
				   (n 2)
				   (m (fl (/ (rem x (expt 2 n))	(expt 2 k))))
				   (a (* (expt 2 (1- (- n k))) (fl (/ x (expt 2 n)))))))))))

(defthm BIT-REM
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= k 0)
		  (> n k))
	     (equal (bitn x k)
		    (bitn (rem x (expt 2 n)) k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-rem-8)
			(:instance integerp-rem (m x) (n (expt 2 n)))
			(:instance rem>=0 (m x) (n (expt 2 n)))
			(:instance expt-pos (x n))
			(:instance bitn-def (x (rem x (expt 2 n))))))))

(defthm BIT-EXPO-A
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0)
		  (< x (expt 2 n)))
	     (equal (bitn x n) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (k n))
			(:instance rem< (m (fl (/ x (expt 2 n)))) (n 2))
			(:instance fl-unique (x (/ x (expt 2 n))) (n 0))))))

(defthm BIT-EXPO-B
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0)
		  (<= (expt 2 n) x)
		  (< x (expt 2 (1+ n))))
	     (equal (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (k n))
			(:instance rem< (m (fl (/ x (expt 2 n)))) (n 2))
			(:instance fl-unique (x (/ x (expt 2 n))) (n 1))))))

(local
(defthm bit+-1
    (implies (and (integerp x)
		  (integerp m)
		  (integerp n)
		  (>= x 0)
		  (>= m n)
		  (>= n 0))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (rem (fl (+ (/ x (expt 2 n))
				(expt 2 (- m n))))
			 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos a14 integerp-expt-type)
		  :use ((:instance bitn-def (x (+ x (expt 2 m))) (k n))
			(:instance integerp-expt-type (n m))
			(:instance expt-pos (x m))
			(:instance expt- (a m) (b n)))))))

(local
(defthm bit+-2
    (implies (and (integerp x)
		  (integerp m)
		  (integerp n)
		  (>= x 0)
		  (>= m n)
		  (>= n 0))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (rem (+ (fl (/ x (expt 2 n)))
			    (expt 2 (- m n)))
			 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt-type)
		  :use ((:instance bit+-1)
			(:instance integerp-expt-type (n (- m n)))
			(:instance fl+int (x (/ x (expt 2 n))) (n (expt 2 (- m n)))))))))

(local
 (defthm bit+-3
    (implies (and (integerp x) (> x 0))
	     (>= (* x 2) 2))
  :rule-classes ()))

(local
(defthm bit+-4
    (implies (integerp x)
	     (not (= (* x 2) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit+-3)
			(:instance bit+-3 (x (- x))))))))

(defthm REM+1-2
    (implies (and (integerp x)
		  (>= x 0))
	     (not (= (rem x 2) (rem (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n 2))
			(:instance bit+-4 (x (- (fl (/ (1+ x) 2)) (fl (/ x 2)))))
			(:instance rem-fl (m (1+ x)) (n 2))))))

(defthm BIT+-A
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit+-2 (m n))
			(:instance rem+1-2 (x (fl (/ x (expt 2 n)))))
			(:instance bitn-def (k n))))))

(defthm BIT+-B
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (>= x 0)
		  (> m n)
		  (>= n 0))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (bitn x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt integerp-expt-type)
		  :use ((:instance bit+-2)
			(:instance rem+
				   (m (fl (/ x (expt 2 n))))
				   (n 2)
				   (a (expt 2 (1- (- m n)))))
			(:instance integerp-expt-type (n (1- (- m n))))
			(:instance expo+ (m 1) (n (1- (- m n))))
			(:instance bitn-def (k n))))))

(defun SHL (x s n)
  (rem (+ (* 2 x) s) (expt 2 n)))

(defun SHR (x s n)
  (+ (fl (/ x 2)) (* (expt 2 (1- n)) s)))

(defun CAT (x y n)
  (+ (* (expt 2 n) x) y))

(defun BITS (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(defthm REM-BITS
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp y)
		  (>= y 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (= (rem x (expt 2 (1+ i))) (rem y (expt 2 (1+ i)))))
	     (= (bits x i j) (bits y i j)))
  :rule-classes ())

(local
(defthm bit-bits-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0)
		  (>= n k))
	     (= (/ x (expt 2 k))
		(+ (* (expt 2 (- n k))
		      (fl (/ x (expt 2 n))))
		   (/ (rem x (expt 2 n))
		      (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a15)
                  ;; order switched below for Version  2.7 fertilization
		  :use ((:instance expt- (a n) (b k))
			(:instance rem-fl (m x) (n (expt 2 n))))))))

(local
(defthm bit-bits-2
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0)
		  (>= n k))
	     (= (fl (+ (* (expt 2 (- n k))
			  (fl (/ x (expt 2 n))))
		       (/ (rem x (expt 2 n))
			  (expt 2 k))))
		(+ (* (expt 2 (- n k))
		      (fl (/ x (expt 2 n))))
		   (fl (/ (rem x (expt 2 n))
			  (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt-type)
	   :use ((:instance integerp-expt-type (n (- n k)))
		 (:instance fl+int
				   (x (/ (rem x (expt 2 n)) (expt 2 k)))
				   (n (* (expt 2 (- n k)) (fl (/ x (expt 2 n)))))))))))

(local
(defthm bit-bits-3
    (implies (= x y)
	     (= (fl x) (fl y)))
  :rule-classes ()))

(local
 (defthm bit-bits-4
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0)
		  (>= n k))
	     (= (fl (/ x (expt 2 k)))
		(+ (* (expt 2 (- n k))
		      (fl (/ x (expt 2 n))))
		   (fl (/ (rem x (expt 2 n))
			  (expt 2 k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a2 a9 a8)
		  :use ((:instance bit-bits-1)
			(:instance bit-bits-3
				   (x (/ x (expt 2 k)))
				   (y (+ (* (expt 2 (- n k))
					    (fl (/ x (expt 2 n))))
					 (/ (rem x (expt 2 n))
					    (expt 2 k)))))
			(:instance bit-bits-2))))))

(local
 (defthm bit-bits-5
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (= (rem (fl (/ x (expt 2 k)))
		     (expt 2 (- (1+ i) k)))
		(rem (+ (* (expt 2 (- (1+ i) k))
			   (fl (/ x (expt 2 (1+ i)))))
			(fl (/ (rem x (expt 2 (1+ i)))
			       (expt 2 k))))
		     (expt 2 (- (1+ i) k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-4 (n (1+ i))))))))

(local
 (defthm bit-bits-6
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (integerp (expt 2 (+ 1 i (* -1 k)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance integerp-expt-type (n (- (1+ i) k))))))))

(local
(defthm bit-bits-7
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (>= (fl (* (/ (expt 2 k)) (rem x (* 2 (expt 2 i)))))
                 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-pos (x k))
			(:instance expt-pos (x i))
			(:instance integerp-expt-type (n i))
			(:instance rem>=0 (m x) (n (* 2 (EXPT 2 I))))
			(:instance integerp-expt-type (n k))
			(:instance n<=fl (x (* (/ (EXPT 2 K)) (REM X (* 2 (EXPT 2 I))))) (n 0)))))))

(local
(defthm bit-bits-8
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (= (rem (fl (/ x (expt 2 k)))
		     (expt 2 (- (1+ i) k)))
		(rem (fl (/ (rem x (expt 2 (1+ i)))
			    (expt 2 k)))
		     (expt 2 (- (1+ i) k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-expt-type)
		  :use ((:instance bit-bits-5)
			(:instance bit-bits-6)
			(:instance bit-bits-7)
			(:instance rem+
				   (m (fl (/ (rem x (expt 2 (1+ i))) (expt 2 k))))
				   (n (expt 2 (- (1+ i) k)))
				   (a (fl (/ x (expt 2 (1+ i)))))))))))

(local
(defthm bit-bits-9
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (> (expt 2 (+ 1 i (* -1 k)))
		(* (/ (expt 2 k))
		   (rem x (* 2 (expt 2 i))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance bit-bits-8)
			(:instance bit-bits-6)
			(:instance bit-bits-7)
			(:instance rem<n (m x) (n (expt 2 (1+ i))))
			(:instance expt- (a (1+ i)) (b k)))))))

(local
(defthm bit-bits-10
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (> (expt 2 (+ 1 i (* -1 k)))
		(fl (* (/ (expt 2 k))
		       (rem x (* 2 (expt 2 i)))))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable a9 a15)
		  :use ((:instance bit-bits-9)
			(:instance fl-def (x (/ (rem x (expt 2 (1+ i))) (expt 2 k)))))))))

(local
(defthm bit-bits-11
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (= (rem (fl (/ x (expt 2 k)))
		     (expt 2 (- (1+ i) k)))
		(fl (/ (rem x (expt 2 (1+ i)))
		       (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-8)
			(:instance bit-bits-6)
			(:instance bit-bits-7)
			(:instance bit-bits-10)
			(:instance rem<
				   (m (fl (/ (rem x (expt 2 (1+ i))) (expt 2 k))))
				   (n (expt 2 (- (1+ i) k)))))))))

(local
 (defthm bit-bits-12
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k))
	     (= (bits (fl (/ x (expt 2 k)))
		      (- i k)
		      (- j k))
		(fl (/ (fl (/ (rem x (expt 2 (1+ i))) (expt 2 k)))
		       (expt 2 (- j k))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-11))))))

(local
(defthm bit-bits-13
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k)
		  (>= j k))
	     (= (fl (/ (fl (/ (rem x (expt 2 (1+ i))) (expt 2 k)))
		       (expt 2 (- j k))))
		(fl (/ (rem x (expt 2 (1+ i)))
		       (expt 2 j)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a15 bits integerp-expt-type)
		  :use ((:instance expo+ (m k) (n (- j k)))
			(:instance integerp-expt-type (n (- j k)))
			(:instance fl/int
				   (x (/ (rem x (expt 2 (1+ i))) (expt 2 k)))
				   (n (expt 2 (- j k)))))))))

(local
(defthm bit-bits-14
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k)
		  (>= j k))
	     (= (bits (fl (/ x (expt 2 k)))
		      (- i k)
		      (- j k))
		(fl (/ (rem x (expt 2 (1+ i)))
		       (expt 2 j)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-12)
			(:instance bit-bits-13))))))

(defthm BIT-BITS-A
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i k)
		  (>= j k))
	     (= (bits (fl (/ x (expt 2 k)))
		      (- i k)
		      (- j k))
		(bits x i j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-14)))))

(local
(defthm bit-bits-15
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bitn (bits x i j) k)
		(rem (fl (/ (fl (/ (rem x (expt 2 (1+ i)))
				   (expt 2 j)))
			    (expt 2 k)))
		     2)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-def (x (bits x i j)))
			(:instance bit-bits-7 (k j)))))))

(local
(defthm bit-bits-16
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bitn (bits x i j) k)
		(rem (fl (/ (rem x (expt 2 (1+ i)))
			    (expt 2 (+ j k))))
		     2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a15)
		  :use ((:instance bit-bits-15)
			(:instance fl/int (x (/ (rem x (expt 2 (1+ i))) (expt 2 j))) (n (expt 2 k)))
			(:instance expo+ (m j) (n k)))))))

(defthm BIT-BITS-B
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bitn (bits x i j) k)
		(bitn x (+ j k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-16)
			(:instance rem>=0 (m x) (n (expt 2 (1+ i))))
			(:instance bitn-def (x (rem x (expt 2 (1+ i)))) (k (+ j k)))
			(:instance bit-rem (n (1+ i)) (k (+ j k)))))))

(local
(defthm bit-bits-17
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bits x i j)
		(rem (fl (/ x (expt 2 j))) (expt 2 (- (1+ i) j)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-rem)
		  :use ((:instance bit-bits-a (k j))
			(:instance integerp-expt-type (n (- (1+ i) j)))
			(:instance integerp-rem (m (FL (/ x (EXPT 2 J)))) (n (EXPT 2 (- (1+ I) j)))))))))

(local
(defthm bit-bits-18
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bits (bits x i j) k l)
		(fl (/ (rem (rem (fl (/ x (expt 2 j))) (expt 2 (- (1+ i) j)))
			    (expt 2 (1+ k)))
		       (expt 2 l)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-17))))))

(local
(defthm rem-rem-1
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp b)
		  (> b 0)
		  (integerp a)
		  (>= a b))
	     (>= (* (FL (* X (/ (EXPT 2 A))))
                    (EXPT 2 (+ A (* -1 B))))
                 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-pos)
		  :use ((:instance expt-pos (x (- a b)))
			(:instance expt-pos (x a))
			(:instance n<=fl (n 0) (x (* X (/ (EXPT 2 A))))))))))

(defthm REM-REM
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp b)
		  (> b 0)
		  (integerp a)
		  (>= a b))
	     (= (rem x (expt 2 b))
		(rem (rem x (expt 2 a)) (expt 2 b))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-fl (m x) (n (expt 2 a)))
			(:instance expo+ (m b) (n (- a b)))
			(:instance rem-rem-1)
			(:instance rem>=0 (m x) (n (expt 2 a)))
			(:instance integerp-expt-type (n (- a b)))
			(:instance rem+
				   (m (rem x (expt 2 a)))
				   (n (expt 2 b))
				   (a (* (expt 2 (- a b)) (fl (/ x (expt 2 a))))))))))

(local
(defthm bit-bits-19
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (>= i (+ j k)))
	     (= (bits (bits x i j) k l)
		(fl (/ (rem (fl (/ x (expt 2 j)))
			    (expt 2 (1+ k)))
		       (expt 2 l)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-18)
			(:instance rem-rem
				   (x (fl (/ x (expt 2 j))))
				   (a (- (1+ i) j))
				   (b (1+ k))))))))

(local
(defthm bit-bits-20
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (integerp l)
		  (>= l 0)
		  (>= i (+ j k)))
	     (= (bits (bits x i j) k l)
		(bits (fl (/ x (expt 2 j))) k l)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-19))))))

(defthm BIT-BITS-C
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp i)
		  (>= i 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (>= k 0)
		  (integerp l)
		  (>= l 0)
		  (>= i (+ j k)))
	     (= (bits (bits x i j) k l)
		(bits x (+ k j) (+ l j))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-bits-20)
			(:instance bit-bits-a (k j) (i (+ j k)) (j (+ j l)))))))

(defun COMP1 (x n)
  (1- (- (expt 2 n) x)))

(defun DEC1 (x n)
  (rem (1- (+ (expt 2 n) x)) (expt 2 n)))

(defthm LOGAND-0
    (equal (logand 0 y) 0))

(defthm LOGAND-0-2
    (equal (logand x 0) 0))

(defthm LOGAND-DEF
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (logand x y)
		(+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
		   (logand (rem x 2) (rem y 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand)
		  :use ((:instance rem012)
			(:instance rem012 (x y))
			(:instance binary-logand (i x) (j y))
			(:instance floor-fl (m x) (n 2))
			(:instance floor-fl (m y) (n 2))
			(:instance bitn-def-4)
			(:instance bitn-def-4 (x y))))))

(defthm LOGAND-NAT
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (logand i j))
		  (>= (logand i j) 0)))
  :rule-classes ())

(defthm LOGAND-REM
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (rem (logand x y) 2)
		(logand (rem x 2) (rem y 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand fl)
		  :use ((:instance logand-def)
			(:instance rem012)
			(:instance rem012 (x y))
			(:instance rem+
				   (m (logand (rem x 2) (rem y 2)))
				   (n 2)
				   (a (logand (fl (/ x 2)) (fl (/ y 2)))))
			(:instance logand-nat (i (fl (/ x 2))) (j (fl (/ y 2))))
			(:instance rem< (m (logand (rem x 2) (rem y 2))) (n 2))))))

(defthm LOGAND-FL
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (fl (/ (logand x y) 2))
		(logand (fl (/ x 2)) (fl (/ y 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand fl)
		  :use ((:instance logand-def)
			(:instance logand-rem)
			(:instance rem-fl (m (logand x y)) (n 2))
			(:instance logand-nat (i x) (j y))))))

(local
 (defthm logand-1
    (implies (integerp x)
	     (equal (logand -1 x) x))))

(local
(defthm logand-1-2
    (implies (integerp x)
	     (equal (logand x -1) x))))

(local
(defthm den-int
    (implies (integerp x)
	     (equal (denominator x) 1))
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance lowest-terms
				   (n (denominator x))
				   (r x)
				   (q 1))
			(:instance rational-implies1)
			(:instance rational-implies2))))))

(local
(defthm num-int
    (implies (integerp x)
	     (equal (numerator x) x))
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance den-int)
			(:instance rational-implies1)
			(:instance rational-implies2))))))

(local
(defthm floor*2
    (implies (integerp x)
	     (equal (floor (* 2 x) 2) x))))

(local
(defthm den-2x+1/2-1
    (implies (integerp x)
	     (equal (denominator (/ (1+ (* 2 x)) 2))
		    (* 2 (- (numerator (/ (1+ (* 2 x)) 2))
			    (* x (denominator (/ (1+ (* 2 x)) 2)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance rational-implies1 (x (/ (1+ (* 2 x)) 2)))
			(:instance rational-implies2 (x (/ (1+ (* 2 x)) 2))))))))

(local
(defthm den-2x+1/2-2
    (implies (integerp x)
	     (equal (* 2 (numerator (/ (1+ (* 2 x)) 2)))
		    (* (denominator (/ (1+ (* 2 x)) 2))
		       (1+ (* 2 x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance rational-implies1 (x (/ (1+ (* 2 x)) 2)))
			(:instance rational-implies2 (x (/ (1+ (* 2 x)) 2)))
			(:instance den-2x+1/2-1))))))

(local
(defthm worst-hack-yet
    (implies (and (rationalp n)
		  (rationalp d)
		  (rationalp s)
		  (rationalp q)
		  (= (* 2 n) (* d s))
		  (= d (* 2 q)))
	     (= n (* s q)))
  :rule-classes ()))

(local
(defthm den-2x+1/2-3
    (implies (integerp x)
	     (equal (numerator (/ (1+ (* 2 x)) 2))
		    (* (1+ (* 2 x))
		       (- (numerator (/ (1+ (* 2 x)) 2))
			  (* x (denominator (/ (1+ (* 2 x)) 2)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance den-2x+1/2-1)
			(:instance den-2x+1/2-2)
			(:instance worst-hack-yet
				   (n (numerator (/ (1+ (* 2 x)) 2)))
				   (d (denominator (/ (1+ (* 2 x)) 2)))
				   (s (1+ (* 2 x)))
				   (q (- (numerator (/ (1+ (* 2 x)) 2))
					 (* x (denominator (/ (1+ (* 2 x)) 2)))))))))))

(local
(defthm den-2x+1/2-4
    (implies (integerp x)
	     (equal (- (numerator (/ (1+ (* 2 x)) 2))
		       (* x (denominator (/ (1+ (* 2 x)) 2))))
		    1))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance lowest-terms
				   (n (- (numerator (/ (1+ (* 2 x)) 2))
					 (* x (denominator (/ (1+ (* 2 x)) 2)))))
				   (r (1+ (* 2 x)))
				   (q 2)
				   (x (/ (1+ (* 2 x)) 2)))
			(:instance den-2x+1/2-1)
			(:instance den-2x+1/2-3)
			(:instance rational-implies1 (x (/ (1+ (* 2 x)) 2)))
			(:instance rational-implies2 (x (/ (1+ (* 2 x)) 2))))))))

(local
(defthm den-2x+1/2
    (implies (integerp x)
	     (equal (denominator (+ 1/2 x)) 2))
  :hints (("Goal" :use ((:instance den-2x+1/2-1)
			(:instance den-2x+1/2-4))))))

(local
(defthm num-2x+1/2
    (implies (integerp x)
	     (equal (numerator (+ 1/2 x)) (1+ (* 2 x))))
  :hints (("Goal" :in-theory (disable rational-implies2)
		  :use ((:instance rational-implies2 (x (/ (1+ (* 2 x)) 2)))
			(:instance den-2x+1/2))))))

(defun INDUCT-NAT (x)
  (if (and (integerp x)
	   (> x 0))
      (induct-nat (1- x))
    ()))

(local
(defthm floor*2+1-1
    (implies (and (integerp x) (>= x 0))
	     (equal (nonnegative-integer-quotient (1+ (* 2 x)) 2)
		    x))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat x)))))

(local
(defthm floor*2+1-2
    (implies (and (integerp x) (> x 0))
	     (equal (nonnegative-integer-quotient (1- (* 2 x)) 2)
		    (1- x)))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat x)))))

(local
(defthm floor*2+1
    (implies (integerp x)
	     (equal (floor (1+ (* 2 x)) 2) x))
  :rule-classes ()
  :hints (("Goal" :use ((:instance floor*2+1-2)
			(:instance floor*2+1-2 (x (- x))))))))

(local
(defthm floor-logand
    (implies (and (integerp i)
		  (integerp j))
	     (= (floor (logand i j) 2)
		(logand (floor i 2) (floor j 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand floor evenp floor*2)
		  :use ((:instance binary-logand)
			(:instance floor*2 (x (LOGAND (FLOOR I 2) (FLOOR J 2))))
			(:instance floor*2+1 (x (LOGAND (FLOOR I 2) (FLOOR J 2)))))))))

(local
(defthm x-or-x/2-1
    (implies (integerp n)
	     (integerp (1+ n)))
  :rule-classes ()
:hints (("Goal" :induct (induct-nat x)))))

(local
(defthm x-or-x/2-2
    (implies (rationalp x)
	     (equal (+ 1 -1/2 x) (+ 1/2 x)))
  :rule-classes ()))

(local
(defthm x-or-x/2-3
    (implies (and (rationalp x)
		  (integerp (+ -1/2 x)))
	     (integerp (+ 1/2 x)))
  :hints (("Goal" :use ((:instance x-or-x/2-1 (n (+ -1/2 x)))
			(:instance x-or-x/2-2))))))

(local
(defthm x-or-x/2-4
    (implies (and (integerp x) (>= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :induct (induct-nat x)))))

(local
(defthm x-or-x/2-5
    (IMPLIES (integerp x)
	     (integerp (- x)))
  :rule-classes ()))

(local
(defthm x-or-x/2-6
    (IMPLIES (integerp x)
	     (= (- (* -1/2 x)) (* 1/2 x)))
  :rule-classes ()))

(local
(defthm x-or-x/2-7
    (implies (and (integerp x)
		  (integerp (* -1/2 x)))
	     (integerp (* 1/2 x)))
  :hints (("Goal" :in-theory (disable a2)
		  :use ((:instance x-or-x/2-5 (x (* -1/2 x)))
			(:instance x-or-x/2-6))))))

(local
(defthm x-or-x/2-8
    (implies (and (integerp x)
		  (integerp y))
	     (integerp (+ x y)))
  :rule-classes ()))

(local
(defthm x-or-x/2-9
    (implies (integerp x)
	     (= (+ x (+ 1/2 (* -1/2 x)))
		(+ 1/2 (* 1/2 x))))
  :rule-classes ()))

(local
(defthm x-or-x/2-10
    (implies (and (integerp x)
		  (integerp (+ 1/2 (* -1/2 x))))
	     (integerp (+ 1/2 (* 1/2 x))))
  :hints (("Goal" :in-theory (disable a2)
		  :use ((:instance x-or-x/2-8 (y (+ 1/2 (* -1/2 x))))
			(:instance x-or-x/2-9))))))

(local
(defthm x-or-x/2-11
    (implies (and (integerp x) (<= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance x-or-x/2-4 (x (- x)))
			(:instance x-or-x/2-5 (x (* -1/2 x))))))))

(defthm X-OR-X/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance x-or-x/2-4)
			(:instance x-or-x/2-11)))))

(local
(defthm floor-lognot-1
    (implies (integerp n)
	     (= (floor (lognot (* 2 n)) 2)
		(lognot (floor (* 2 n) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable floor)
		  :use ((:instance floor*2+1 (x (lognot n)))
			(:instance floor*2 (x n)))))))

(local
(defthm floor-lognot-2
    (implies (integerp n)
	     (= (floor (lognot (1- (* 2 n))) 2)
		(lognot (floor (1- (* 2 n)) 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable floor)
		  :use ((:instance floor*2+1 (x (1- n)))
			(:instance floor*2 (x (- n))))))))

(local
(defthm floor-lognot
    (implies (integerp i)
	     (= (floor (lognot i) 2)
		(lognot (floor i 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable floor lognot)
		  :use ((:instance floor-lognot-1 (n (/ i 2)))
			(:instance floor-lognot-2 (n (/ (1+ i) 2)))
			(:instance x-or-x/2 (x i)))))))

(local
(defthm floor-logior
    (implies (and (integerp i)
		  (integerp j))
	     (= (floor (logior i j) 2)
		(logior (floor i 2) (floor j 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand floor lognot)
		  :use ((:instance floor-lognot)
			(:instance floor-lognot (i j))
			(:instance floor-logand (i (lognot i)) (j (lognot j)))
			(:instance floor-lognot (i (logand (lognot i) (lognot j)))))))))

(local
(defthm fl-logior-1
    (implies (integerp i)
	     (iff (>= i 0) (< (lognot i) 0)))
  :rule-classes ()))

(local
(defthm fl-logior-2
    (implies (and (integerp i) (< i 0)
		  (integerp j) (< j 0))
	     (and (integerp (logand i j))
		  (< (logand i j) 0)))
  :rule-classes ()))

(defthm LOGIOR-NAT
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (logior i j))
		  (>= (logior i j) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable lognot logand)
		  :use ((:instance fl-logior-1)
			(:instance fl-logior-1 (i j))
			(:instance fl-logior-1 (i (logand (lognot i) (lognot j))))
			(:instance fl-logior-2 (i (lognot i)) (j (lognot j)))))))

(defthm LOGIOR-FL
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (fl (/ (logior i j) 2))
		(logior (fl (/ i 2)) (fl (/ j 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logior floor)
		  :use ((:instance floor-logior)
			(:instance floor-fl (m (logior i j)) (n 2))
			(:instance floor-fl (m i) (n 2))
			(:instance floor-fl (m j) (n 2))
			(:instance logior-nat)))))

(defthm REM-2*I
    (implies (integerp i)
	     (equal (rem (* 2 i) 2) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem (x (* 2 i)) (y 2))
			(:instance rem012 (x (* 2 i)))))))

(local
(defthm rem-logior-2
    (implies (integerp i)
	     (equal (rem (1+ (* 2 i)) 2) (- 1 (* 2 (- (truncate (1+ (* 2 i)) 2) i)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem (x (1+ (* 2 i))) (y 2)))))))

(defthm REM-2*I+1
    (implies (integerp i)
	     (not (equal (rem (1+ (* 2 i)) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit+-4 (x (- (truncate (1+ (* 2 i)) 2) i)))
			(:instance rem-logior-2)))))

(local
(defthm rem-logior-4
    (implies (integerp n)
	     (not (= (rem (lognot (* 2 n)) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-2*i+1 (i (1- (- n)))))))))

(local
(defthm rem-logior-5
    (implies (integerp n)
	     (= (rem (lognot (1+ (* 2 n))) 2) 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem-2*i (i (1- (- n)))))))))

(local
(defthm rem-logior-6
    (implies (integerp n) (integerp (1- n)))
  :rule-classes ()))

(local
(defthm rem-logior-7
    (implies (rationalp x)
	     (= (1- (+ 1/2 x))
		(+ -1/2 x)))
  :rule-classes ()))

(local
(defthm rem-logior-8
    (implies (and (rationalp x)
		  (integerp (+ 1/2 x)))
	     (integerp (+ -1/2 x)))
  :hints (("Goal" :use ((:instance rem-logior-6 (n (+ 1/2 x)))
			(:instance rem-logior-7))))))

(local
(defthm rem-logior-9
    (implies (integerp i)
	     (iff (= (rem (lognot i) 2) 0)
		  (not (= (rem i 2) 0))))
  :hints (("Goal" :in-theory (disable lognot)
		  :use ((:instance x-or-x/2 (x i))
			(:instance rem-2*i (i (/ i 2)))
			(:instance rem-logior-4 (n (/ i 2)))
			(:instance rem-2*i+1 (i (1- (/ (1+ i) 2))))
			(:instance rem-logior-5 (n (1- (/ (1+ i) 2)))))))))

(local
(defthm evenp-logand-1
    (implies (and (integerp i)
		  (integerp j)
		  (or (evenp i) (evenp j)))
	     (= (logand i j)
		(* 2 (logand (floor i 2) (floor j 2)))))
  :rule-classes ()))

(local
(defthm evenp-logand-2
    (implies (integerp x)
	     (iff (evenp x)
		  (= (rem x 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance x-or-x/2)
			(:instance rem-2*i (i (/ x 2)))
			(:instance rem-2*i+1 (i (1- (/ (1+ x) 2)))))))))

(local
(defthm evenp-logand-3
    (implies (and (integerp i)
		  (integerp j)
		  (or (= (rem i 2) 0) (= (rem j 2) 0)))
	     (= (rem (logand i j) 2) 0))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand floor evenp)
		  :use ((:instance evenp-logand-1)
			(:instance evenp-logand-2 (x i))
			(:instance evenp-logand-2 (x j))
			(:instance rem-2*i (i (logand (floor i 2) (floor j 2)))))))))

(local
(defthm evenp-logand-4
    (implies (and (integerp i)
		  (integerp j)
		  (not (or (evenp i) (evenp j)))
		  (or (= i -1) (= j -1)))
	     (or (= (logand i j) i)
		 (= (logand i j) j)))
  :rule-classes ()))

(local
(defthm evenp-logand-5
    (implies (and (integerp i)
		  (integerp j)
		  (not (or (= (rem i 2) 0) (= (rem j 2) 0)))
		  (or (= i -1) (= j -1)))
	     (not (= (rem (logand i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand evenp)
		  :use ((:instance evenp-logand-4)
			(:instance evenp-logand-2 (x i))
			(:instance evenp-logand-2 (x j)))))))

(local
(defthm evenp-logand-6
    (implies (and (integerp i)
		  (integerp j)
		  (not (or (evenp i) (evenp j)))
		  (not (or (= i -1) (= j -1))))
	     (= (logand i j)
		(1+ (* 2 (logand (floor i 2) (floor j 2))))))
  :rule-classes ()))

(local
(defthm evenp-logand-7
    (implies (and (integerp i)
		  (integerp j)
		  (not (or (= (rem i 2) 0) (= (rem j 2) 0)))
		  (not (or (= i -1) (= j -1))))
	     (not (= (rem (logand i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand evenp floor)
		  :use ((:instance evenp-logand-6)
			(:instance evenp-logand-2 (x i))
			(:instance evenp-logand-2 (x j))
			(:instance rem-2*i+1 (i (logand (floor i 2) (floor j 2)))))))))

(local
(defthm evenp-logand-8
    (implies (and (integerp i)
		  (integerp j)
		  (not (or (= (rem i 2) 0) (= (rem j 2) 0))))
	     (not (= (rem (logand i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand evenp floor)
		  :use ((:instance evenp-logand-5)
			(:instance evenp-logand-7))))))

(local
(defthm evenp-logand
    (implies (and (integerp i)
		  (integerp j))
	     (iff (or (= (rem i 2) 0) (= (rem j 2) 0))
		  (= (rem (logand i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand evenp floor)
		  :use ((:instance evenp-logand-3)
			(:instance evenp-logand-8))))))

(local
(defthm rem-logior-10
    (implies (and (integerp i)
		  (integerp j))
	     (iff (and (= (rem i 2) 0) (= (rem j 2) 0))
		  (= (rem (logior i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logand lognot)
		  :use ((:instance rem-logior-9 (i (logand (lognot i) (lognot j))))
			(:instance evenp-logand (i (lognot i)) (j (lognot j)))
			(:instance rem-logior-9)
			(:instance rem-logior-9 (i j)))))))

(defthm LOGIOR-REM
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (rem (logior i j) 2)
		(logior (rem i 2) (rem j 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logior)
		  :use ((:instance rem-logior-10)
			(:instance rem012 (x i))
			(:instance rem012 (x j))
			(:instance logior-nat)
			(:instance rem012 (x (logior i j)))))))

(defthm LOGIOR-DEF
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (logior i j)
		(+ (* 2 (logior (fl (/ i 2)) (fl (/ j 2))))
		   (logior (rem i 2) (rem j 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logior)
		  :use ((:instance logior-nat)
			(:instance rem-fl (m (logior i j)) (n 2))
			(:instance logior-rem)
			(:instance logior-fl)))))

