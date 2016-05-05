;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/proofs"))

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

(in-theory (disable fl cg))

(defun comp1 (x n)
  (1- (- (expt 2 n) x)))


;;;**********************************************************************
;;;                             BITN
;;;**********************************************************************

(defun bitn (x n)
  (if (logbitp n x) 1 0))

(progn

; See the comment about April 2016 in books/rtl/rel1/support/logdefs.lisp.

  (defthm natp-bitn
    (natp (bitn x n))
    :rule-classes :type-prescription)

  (in-theory (disable bitn (:t bitn)))
  )

(defthm bitn-def
    (implies (and (integerp x)
		  (integerp k)
		  (>= x 0)
		  (>= k 0))
	     (equal (bitn x k)
		    (rem (fl (/ x (expt 2 k)))
			 2)))
   :rule-classes ())

(defthm bitn-0
    (implies (and (integerp k) (>= k 0))
	     (= (bitn 0 k) 0))
  :rule-classes ())

(defthm bitn-0-1
    (or (= (bitn x n) 0) (= (bitn x n) 1))
  :rule-classes ())

(defthm bitn-alt-0
    (implies (and (integerp x) (>= x 0))
	     (equal (bitn x 0)
		    (rem x 2)))
  :rule-classes ())

(defthm bitn-alt-pos
    (implies (and (integerp x)
		  (integerp k)
		  (>= x 0)
		  (> k 0))
	     (equal (bitn x k)
		    (bitn (fl (/ x 2)) (1- k))))
  :rule-classes ())

(defthm bit-expo-a
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0)
		  (< x (expt 2 n)))
	     (equal (bitn x n) 0))
  :rule-classes ())

(defthm bit-expo-b
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0)
		  (<= (expt 2 n) x)
		  (< x (expt 2 (1+ n))))
	     (equal (bitn x n) 1))
  :rule-classes ())

(defthm bit-expo-c
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= x 0)
		  (>= n 0)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1))
  :rule-classes ())

(defthm bit-expo-d
    (implies (and (integerp x)
		  (integerp n)
		  (integerp k)
		  (>= k 0)
		  (< k n)
		  (< x (expt 2 n))
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1))
  :rule-classes ())

(defthm bitn-2**n
    (implies (and (integerp n) (>= n 0))
	     (= (bitn (expt 2 n) n) 1))
  :rule-classes ())

(defthm bit+-a
    (implies (and (integerp x)
		  (integerp n)
		  (>= x 0)
		  (>= n 0))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ())

(defthm bit+-b
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (>= x 0)
		  (> m n)
		  (>= n 0))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (bitn x n)))
  :rule-classes ())

(defthm bit+*k
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (>= x 0)
		  (> m n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n)))
  :rule-classes ())

(defthm bitn-rem
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp j)
		  (>= j 0)
		  (integerp k)
		  (> k j))
	     (equal (bitn (rem x (expt 2 k)) j)
		    (bitn x j))))

(defthm bitn-n+k
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (integerp k)
		  (>= k 0))
	     (= (bitn (* x (expt 2 k)) (+ n k))
		(bitn x n)))
  :rule-classes ())

(defthm rem-n+1
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (> n 0))
	     (= (rem a (expt 2 (1+ n)))
		(+ (* (bitn a n) (expt 2 n))
		   (rem a (expt 2 n)))))
  :rule-classes ())

(defthm rem-n-n+1
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp n)
		  (> n 0))
	     (iff (= (rem a (expt 2 (1+ n))) 0)
		  (and (= (rem a (expt 2 n)) 0)
		       (= (bitn a n) 0))))
  :rule-classes ())

(defthm bitn-fl
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp k)
		  (>= k 0)
		  (integerp r)
		  (>= r 0))
	     (= (bitn (fl (/ x (expt 2 r))) k)
		(bitn x (+ k r))))
  :rule-classes ())

(defthm bit+*k-2
    (implies (and (integerp x)
		  (integerp n)
		  (integerp m)
		  (< x (expt 2 m))
		  (>= x 0)
		  (<= m n)
		  (>= m 0)
		  (integerp k)
		  (>= k 0))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn k (- n m))))
  :rule-classes ())


;;;**********************************************************************
;;;                         BITS
;;;**********************************************************************

(defun bits (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(in-theory (disable bits))

(defthm rem-bits
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

(defthm bits-0
    (implies (and (integerp i)
		  (integerp j)
		  (>= i 0))
	     (equal (bits 0 i j) 0)))

(defthm bits-nat
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (bits x i j))
		  (>= (bits x i j) 0)))
  :rule-classes ())

(defthm bits<
    (implies (and (integerp x) (>= x 0)
		  (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (< (bits x i j) (expt 2 (- (1+ i) j))))
  :rule-classes ())

(defthm bits-rewrite
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (>= n 0)
		  (< x (expt 2 (1+ n))))
	     (equal (bits x n 0)
		    x)))

(defthm bits-0-rem
    (implies (and (integerp x)
		  (integerp n)
		  (>= n 0))
	     (equal (bits x n 0)
		    (rem x (expt 2 (1+ n))))))

(in-theory (disable bits-0-rem))

(defthm bit-bits-a
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
  :rule-classes ())

(defthm bit-bits-b
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
  :rule-classes ())

(defthm bit-bits-c
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
  :rule-classes ())

(defthm bits-rem-0
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (>= m 0)
		  (integerp n)
		  (>= n 0))
	     (iff (= (rem x (expt 2 (+ m n 1))) 0)
		  (and (= (bits x (+ m n) n) 0)
		       (= (rem x (expt 2 n)) 0))))
  :rule-classes ())

(defthm bits-bitn
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (iff (= (bits x n 0) 0)
		  (and (= (bitn x n) 0)
		       (= (bits x (1- n) 0) 0))))
  :rule-classes ())

(defthm bits-bits
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp r)
		  (>= r 0)
		  (integerp n)
		  (> n r)
		  (integerp m)
		  (> m n))
	     (= (bits x (1- m) r)
		(+ (bits x (1- n) r)
		   (* (expt 2 (- n r)) (bits x (1- m) n)))))
  :rule-classes ())

(defthm bits+bitn
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (>= m 0)
		  (integerp n)
		  (> n m))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :rule-classes ())

(defthm bitn+bits
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp m)
		  (> m 0)
		  (integerp n)
		  (> n m))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ())

(defthm bits+2**k-2
    (implies (and (integerp m)
		  (>= m 0)
		  (integerp n)
		  (>= n m)
		  (integerp k)
		  (>= k 0)
		  (<= k m)
		  (integerp y)
		  (>= y 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 k)))
	     (= (bits (+ x (* y (expt 2 k))) n m)
		(bits y (- n k) (- m k))))
  :rule-classes ())


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(in-theory (disable logand logior logxor))

(defthm logand-def
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (logand x y)
		(+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
		   (logand (rem x 2) (rem y 2)))))
  :rule-classes ())

(defthm logand-nat
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (logand i j))
		  (>= (logand i j) 0)))
  :rule-classes ())

(defthm logand-rem
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (rem (logand x y) 2)
		(logand (rem x 2) (rem y 2))))
  :rule-classes ())

(defthm logand-fl
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (fl (/ (logand x y) 2))
		(logand (fl (/ x 2)) (fl (/ y 2)))))
  :rule-classes ())

(defthm logior-def
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (logior i j)
		(+ (* 2 (logior (fl (/ i 2)) (fl (/ j 2))))
		   (logior (rem i 2) (rem j 2)))))
  :rule-classes ())

(defthm logior-nat
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (logior i j))
		  (>= (logior i j) 0)))
  :rule-classes ())

(defthm logior-rem
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (rem (logior i j) 2)
		(logior (rem i 2) (rem j 2))))
  :rule-classes ())

(defthm logior-fl
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (fl (/ (logior i j) 2))
		(logior (fl (/ i 2)) (fl (/ j 2)))))
  :rule-classes ())

(defthm logxor-def
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (logxor x y)
		(+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
		   (logxor (rem x 2) (rem y 2)))))
  :rule-classes ())

(defthm logxor-nat
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (and (integerp (logxor i j))
		  (>= (logxor i j) 0)))
  :rule-classes ())

(defthm logxor-rem
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (= (rem (logxor i j) 2)
		(logxor (rem i 2) (rem j 2))))
  :rule-classes ())

(defthm logxor-fl
    (implies (and (integerp i)
		  (integerp j)
		  (>= i 0)
		  (>= j 0))
	     (= (fl (/ (logxor i j) 2))
		(logxor (fl (/ i 2)) (fl (/ j 2)))))
  :rule-classes())

(defthm logxor-rewrite
    (implies (and (integerp n) (>= n 1)
		  (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n)))
	     (= (logxor x y)
		(logior (logand x (comp1 y n))
			(logand y (comp1 x n)))))
  :rule-classes ())

(defthm bit-basic-a
    (implies (and (integerp x) (>= x 0))
	     (= (logand x 0)
		0))
  :rule-classes ())

(defthm bit-basic-b
    (implies (and (integerp x) (>= x 0))
	     (= (logior x 0)
		x))
  :rule-classes ())

(defthm logxor-0
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logxor-0-2
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-x-x
    (implies (and (integerp x) (>= x 0))
	     (equal (logxor x x) 0)))

(defthm logand-2**n-1
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x (1- (expt 2 n)))
		x))
  :rule-classes ())

(defthm bit-basic-c
    (implies (and (integerp x)
		  (integerp y))
	     (= (logand x y) (logand y x)))
  :rule-classes ())

(defthm bit-basic-d
    (implies (and (integerp x)
		  (integerp y))
	     (= (logior x y) (logior y x)))
  :rule-classes ())

(defthm logxor-commutative
    (implies (and (integerp x)
		  (integerp y))
	     (= (logxor x y) (logxor y x)))
  :rule-classes ())

(defthm bit-basic-e
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand (logand x y) z)
		(logand x (logand y z))))
  :rule-classes ())

(defthm bit-basic-f
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logior (logior x y) z)
		(logior x (logior y z))))
  :rule-classes ())

(defthm logxor-assoc
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logxor (logxor x y) z)
		(logxor x (logxor y z))))
  :rule-classes ())

(defthm bit-basic-g
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logior x (logand y z))
		(logand (logior x y) (logior x z))))
  :rule-classes ())

(defthm bit-basic-h
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand x (logior y z))
		(logior (logand x y) (logand x z))))
  :rule-classes ())

(defthm bit-basic-h-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp z) (>= z 0))
	     (= (logand  (logior y z) x)
		(logior (logand y x) (logand z x))))
  :rule-classes ())

(defthm logand-x-x
    (implies (and (integerp x) (>= x 0))
	     (equal (logand x x) x)))

(defthm or-dist-a
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (< y (expt 2 n)))
	     (< (logior x y) (expt 2 n)))
  :rule-classes ())

(defthm or-dist-b
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< y (expt 2 n)))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ())

(defthm or-dist-c
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ())

(defthm or-dist-d
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
  	     (= (rem (logior x y) (expt 2 n))
		(logior (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :rule-classes ())

(defthm and-dist-a
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (<= (logand x y) x))
  :rule-classes ())

(defthm and-dist-b
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ())

(defthm and-dist-c
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) y)))
  :rule-classes ())

(defthm rem-logand
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (> n 0))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :rule-classes ())

(defthm rem-logxor
    (implies (and (integerp n) (>= n 1)
		  (integerp x) (>= x 0)
		  (integerp y) (>= y 0))
	     (= (rem (logxor x y) (expt 2 n))
		(logxor (rem x (expt 2 n))
			(rem y (expt 2 n)))))
  :rule-classes ())

(defthm and-dist-d
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (rem y (expt 2 n)))))
  :rule-classes ())

(defthm logxor<2**n
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n))
		  (< y (expt 2 n)))
	     (< (logxor x y) (expt 2 n)))
  :rule-classes ())

(defthm bit-dist-a
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logand x y) n)
		(logand (bitn x n) (bitn y n))))
  :rule-classes ())

(defthm bit-dist-b
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logior x y) n)
		(logior (bitn x n) (bitn y n))))
  :rule-classes ())

(defthm bitn-logxor
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0))
	     (= (bitn (logxor x y) n)
		(logxor (bitn x n) (bitn y n))))
  :rule-classes ())

(defthm and-bits-a
    (implies (and (integerp x) (>= x 0)
		  (integerp k) (>= k 0))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ())

(defthm and-bits-b
    (implies (and (integerp x) (>= x 0)
		  (integerp k) (>= k 0))
	     (= (logior x (expt 2 k))
		(+ x
		   (* (expt 2 k)
		      (- 1 (bitn x k))))))
  :rule-classes ())

(defthm and-bits-c
    (implies (and (integerp x) (>= x 0)
		  (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ())

(defthm and-bits-e
    (implies (and (integerp n) (>= n 0)
		  (integerp k) (>= k 0)
		  (integerp l) (>= l 0) (< l k)
		  (< k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(- (expt 2 n) (expt 2 k))))
  :rule-classes ())

(defthm bitn-0-logxor-+
    (implies (and (integerp a)
		  (>= a 0)
		  (integerp b)
		  (>= b 0))
	     (= (bitn (+ a b) 0)
		(bitn (logxor a b) 0)))
  :rule-classes ())


;;;**********************************************************************
;;;                            COMP1
;;;**********************************************************************

(defthm integerp-comp1
    (implies (and (integerp n)
		  (integerp x)
		  (>= n 0))
	     (integerp (comp1 x n)))
  :rule-classes (:type-prescription))

(defthm comp1-comp1
    (implies (and (integerp n)
		  (integerp x))
	     (= (comp1 (comp1 x n) n)
		x))
  :rule-classes ())

(defthm fl-comp1
    (implies (and (integerp n) (>= n k)
		  (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(comp1 (fl (/ x (expt 2 k))) (- n k))))
  :rule-classes ())

(defthm rem-comp1
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n)))
	     (not (= (rem (comp1 x n) 2)
		     (rem x 2))))
  :rule-classes ())

(defthm comp1-bnds
    (implies (and (integerp n) (> n 0)
		  (integerp x) (>= x 0) (< x (expt 2 n)))
	     (and (< (comp1 x n) (expt 2 n))
		  (>=  (comp1 x n) 0)))
  :rule-classes ())

(defthm bitn-comp1
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x)
		  (>= x 0)
		  (< x (expt 2 n))
		  (integerp k)
		  (>= k 0)
		  (< k n))
	     (not (= (bitn (comp1 x n) k)
		     (bitn x k))))
  :rule-classes ())

(defthm comp1-rem
    (implies (and (integerp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (< x (expt 2 m)))
	     (= (rem (comp1 x m) (expt 2 n))
		(comp1 (rem x (expt 2 n)) n)))
  :rule-classes ())
