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

;;;**************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************
(in-package "RTL")

;This book includes theorems mixing the logical operators (logand, etc.) with bits and bitn.

(include-book "ground-zero")

(local (include-book "log-proofs"))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(include-book "lnot")
(include-book "logand")
(include-book "logior")
(include-book "logxor")

;move!
;rename! mod-lognot-by-2
(defthm mod-logior-9
  (implies (integerp i)
           (iff (= (mod (lognot i) 2) 0)
                (not (= (mod i 2) 0)))))

;move!
(defthm mod-logior-10
  (implies (and (integerp i)
                (integerp j))
           (iff (and (= (mod i 2) 0) (= (mod j 2) 0))
                (= (mod (logior i j) 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use mod-logior-by-2
           :in-theory (set-difference-theories
                       (enable mod-by-2)
                       '(logior)))))

;BOZO export!
;gen?
(defthm logior-logand
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y)
                (integerp z)
                (<= 0 z))
           (equal (logior x (logand y z))
                  (logand (logior x y) (logior x z))))
  :rule-classes ())

;BOZO export!
(defthm logior-logand-alt
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y)
                (integerp z)
                (<= 0 z))
           (equal (logior (logand y z) x)
                  (logand (logior x y) (logior x z))))
  :rule-classes ())

(defthm logand-logior
  (implies (and (integerp x) (<= 0 x)
                (integerp y) (<= 0 y)
                (integerp z) (<= 0 z))
           (equal (logand x (logior y z))
                  (logior (logand x y) (logand x z))))
  :rule-classes ())

(defthm logand-logior-alt
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp z) (>= z 0))
           (equal (logand (logior y z) x)
                  (logior (logand y x) (logand z x))))
  :rule-classes ())

(defthm mod-logand-aux
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (= (mod (logand x y) (expt 2 n))
              (logand (mod x (expt 2 n)) y)))
  :rule-classes ())

;generalize (mod y (expt 2 n)) to anything < 2^n?
(defthm and-dist-d
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (mod y (expt 2 n)))))
  :rule-classes ())

;compare to mod-logand-aux
;we can wrap the mod around x or y or both (same for bits of logand?)
(defthm mod-logand
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (equal (mod (logand x y) (expt 2 n))
                  (logand (mod x (expt 2 n)) (mod y (expt 2 n))))))

;prove that we can wrap the bits around either arg in the conclusion or both...
;will have to shift if we don't wrap bits??
(defthm bits-logand
   (implies (and     ;(<= i j)
             (case-split (natp x)) ;drop?
             (case-split (natp y)) ;drop?
             (case-split (natp i))
             (case-split (natp j))
             )
            (equal (bits (logand x y) i j)
                   (logand (bits x i j) (bits y i j)))))

(defthm bitn-logand
  (implies (and (integerp x) ; (>= x 0)
                (integerp y) ; (>= y 0)
                (integerp n) (>= n 0)
                )
           (equal (bitn (logand x y) n)
                  (logand (bitn x n) (bitn y n)))))

(defthm bits-logior
    (implies (and ;(>= i j)
                  (case-split (natp x))
                  (case-split (natp y))
                  (case-split (natp i))
                  (case-split (natp j))
                  )
	     (equal (bits (logior x y) i j)
		    (logior (bits x i j) (bits y i j)))))

;someday prove from bits-logior (will have to generalize bits-logior?)?
(defthm bitn-logior
    (implies (and (integerp x)
		  (integerp y)
		  (integerp n)
                  (>= n 0))
	     (equal (bitn (logior x y) n)
                    (logior (bitn x n) (bitn y n)))))

;give better name, perhaps "logand-with-power2" ?
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

(defthm logand-slice
  (implies (and (integerp x) (>= x 0)
                (integerp n) (>= n 0)
                (integerp k) (>= k 0)
                (< k n))
           (= (logand x (- (expt 2 n) (expt 2 k)))
              (* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ())

;move to logxor.lisp?
(defthmd logxor-rewrite
   (implies (and (< x (expt 2 n))
                 (< y (expt 2 n))
                 (integerp n) (>= n 1) ;gen?
                 (integerp x) (>= x 0)
                 (integerp y) (>= y 0))
            (= (logxor x y)
               (logior (logand x (lnot y n))
                       (logand y (lnot x n))))))

;n is a free var
(defthmd logxor-rewrite-2
    ;; ! Do we really want to get rid of logxor?
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n)
		  (not (= n 0)))
	     (equal (logxor x y)
		    (logior (logand x (lnot y n))
			    (logand y (lnot x n)))))
    :rule-classes ((:rewrite :match-free :all)))

(defthm bitn-logxor
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                (case-split (integerp n))
                (case-split (>= n 0))
                )
           (equal (bitn (logxor x y) n)
                  (logxor (bitn x n) (bitn y n)))))



(defthm bits-logxor
  (implies (and (case-split (natp x))
                (case-split (natp y))
                (case-split (natp i))
                (case-split (natp j))
;(>= i j)
                )
           (equal (bits (logxor x y) i j)
                  (logxor (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bvecp natp expt-split)
                              '())
           :use ((:instance hack1 (x (+ i x y)))
                 (:instance bits-logxor-aux (n (+ i x y)))))))

