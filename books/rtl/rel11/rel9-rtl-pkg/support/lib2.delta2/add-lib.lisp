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

(in-package "RTL")

(include-book "base")
(local (include-book "../lib2.delta1/arith"))

;; Add to bits.lisp, after bits-bvecp:

(defthm bits-bounds
    (implies (and (integerp i)
		  (integerp j))
	     (and (natp (bits x i j))
		  (< (bits x i j) (expt 2 (1+ (- i j))))))
  :rule-classes()
  :hints (("Goal" :in-theory (e/d (bvecp) (bits-bvecp bits-bvecp-simple))
		  :use ((:instance bits-bvecp (k (1+ (- i j))))))))

;; Add these to bits.lisp, after bits-bits-sum:

(defthmd bits-bits-diff
  (implies (and (integerp x)
                (integerp y)
                (natp i))
	   (equal (bits (- x (bits y i 0)) i 0)
		  (bits (- x y) i 0)))
  :hints (("Goal" :use ((:instance mod-diff (a x) (b y) (n (expt 2 (1+ i)))))
		  :in-theory (enable bits-mod))))

(local-defthm bits-bits-times-1
    (implies (and (integerp x)
		  (integerp y)
		  (natp i))
	     (= (bits (* (bits x i 0) y) i 0)
		(bits (* x y) i 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-mod-times (a x) (b y) (n (expt 2 (1+ i)))))
		  :in-theory (enable bits-mod))))

(defthmd bits-bits-times
    (implies (and (integerp x)
		  (integerp y)
		  (integerp i))
	     (equal (bits (* (bits x i 0) y) i 0)
		    (bits (* x y) i 0)))
  :hints (("Goal" :use (bits-bits-times-1))))

(defthm bits-diff-equal
    (implies (and (natp n)
		  (integerp x)
		  (integerp y)
		  (< (abs (- x y)) (expt 2 n)))
	     (iff (= x y)
		  (= (bits (- x y) (1- n) 0) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-mod)
		  :use ((:instance mod-force-equal (a (- x y)) (b 0) (n (expt 2 n)))))))


;; Add these to bits.lisp,after bits-tail-2:

(defun sgndintval (w x)
  (if (= (bitn x (1- w)) 1)
      (- x (expt 2 w))
    x))

(defthm sgndintval-bits
    (implies (and (integerp x)
		  (natp w)
		  (< x (expt 2 (1- w)))
		  (>= x (- (expt 2 (1- w)))))
	     (= (sgndintval w (bits x (1- w) 0))
		x))
  :hints (("Goal" :use ((:instance bits-tail (i (1- w)))
			(:instance bits-tail-2 (i (1- w)))
			(:instance expt-weak-monotone (n (1- w)) (m w))
			(:instance bvecp-bitn-0 (n (1- w)))
			(:instance bvecp-bitn-0 (n (1- w))))
		  :in-theory (enable bvecp)))
  :rule-classes ())


(defun signextend (n m x)
  (bits (SgndIntVal m x) (1- n) 0))

(local-defthm sgndintval-signextend-1
    (implies (and (natp n)
		  (integerp z)
		  (< z (expt 2 (1- n)))
		  (<= (- (expt 2 (1- n))) z))
	     (equal (sgndintval n (bits z (1- n) 0))
		    z))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bvecp-bitn-0 (x z) (n (1- n)))
			(:instance neg-bitn-1 (x z) (n (1- n)))
			(:instance bits-tail (x z) (i (1- n)))
			(:instance bits-tail-2 (x z) (i (1- n)))
			(:instance expt-strong-monotone (n (1- n)) (m n)))
		  :in-theory (enable bvecp))))

(defthmd sgndintval-signextend
    (implies (and (natp n)
		  (natp m)
		  (<= m n)
		  (bvecp x m))
	     (equal (sgndintval n (signextend n m x))
		    (sgndintval m x)))
  :hints (("Goal" :use ((:instance sgndintval-signextend-1 (z (sgndintval m x)))
			(:instance expt-weak-monotone (n (1- m)) (m (1- n)))
			(:instance a15 (i 2) (j1 (1- m)) (j2 1))
			(:instance bitn-plus-bits (n (1- m)) (m 0))
			(:instance bits-bounds (i (- m 2)) (j 0)))
		  :in-theory (enable bvecp))))

;; Add bits-lognot to log.lisp, after bitn-lognot:

(local-defthm mod-lognot
    (implies (and (integerp n)
		  (> n 0)
		  (integerp x))
	     (equal (mod (lognot x) n)
		    (- (1- n) (mod x n))))
  :hints (("Goal" :in-theory (enable lognot)
		  :use ((:instance mod-mult (m (1- (- x))) (a 1) (n n))
			(:instance mod-diff (a (1- n)) (b x) (n n))
			(:instance mod-does-nothing
				   (m (- (1- n) (mod x n)))
				   (n n))
			(:instance mod-bnd-2 (m x) (n n))
			(:instance natp-mod-2 (m x) (n n))))))

(local-defthmd bits-lognot-1
    (implies (and (natp i)
		  (integerp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (fl (/ (- (1- (expt 2 (1+ i)))
			      (mod x (expt 2 (1+ i))))
			   (expt 2 j)))))
  :hints (("Goal" :in-theory (enable bits))))

(local-defthm bits-lognot-2
    (implies (and (integerp i)
		  (integerp j))
	     (equal (* (/ (EXPT 2 J)) (EXPT 2 (+ 1 I)))
		    (expt 2 (- (1+ i) j))))
  :hints (("Goal" :use ((:instance a15 (i 2) (j1 (1+ i)) (j2 (- j)))))))

(local-defthmd bits-lognot-3
    (implies (and (natp i)
		  (integerp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (+ (expt 2 (- (1+ i) j))
		       (fl (/ (1- (- (mod x (expt 2 (1+ i))))) (expt 2 j))))))
  :hints (("Goal" :in-theory (enable bits-lognot-1)
		  :use ((:instance fl+int-rewrite
				   (x (/ (1- (- (mod x (expt 2 (1+ i))))) (expt 2 j)))
				   (n (expt 1 (- (1+ i) j))))))))

(defthmd bits-lognot
    (implies (and (natp i)
		  (natp j)
		  (<= j i)
		  (integerp x))
	     (equal (bits (lognot x) i j)
		    (- (1- (expt 2 (- (1+ i) j))) (bits x i j))))
  :hints (("Goal" :in-theory (enable bits bits-lognot-3)
		  :use ((:instance fl-m-n (m (- (mod x (expt 2 (1+ i))))) (n (expt 2 j)))))))
