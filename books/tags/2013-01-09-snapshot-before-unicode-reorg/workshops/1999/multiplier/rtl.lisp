;;;***************************************************************
;;;Proof of Correctness of a Floating Point Multiplier

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1999
;;;***************************************************************

;;Definitions of the ACL2 functions that are used in the
;;formalization of the RTL semantics


(in-package "ACL2")

(defmacro ?? (x y z)
  `(if (equal ,x 0) ,z ,y))

(defun log< (x y)
  (if (< x y) 1 0))

(defun log<= (x y)
  (if (<= x y) 1 0))

(defun log> (x y)
  (if (> x y) 1 0))

(defun log>= (x y)
  (if (>= x y) 1 0))

(defun log= (x y)
  (if (equal x y) 1 0))

(defun log<> (x y)
  (if (equal x y) 1 0))

(defun logand1 (x n)
  (log= x (1- (expt 2 n))))

(defun logior1 (x)
  (if (equal x 0) 0 1))

(defun comp1 (x n)
  (1- (- (expt 2 n) x)))

(defun bitn (x n)
  (if (logbitp n x) 1 0))

(defun fl (x) (floor x 1))

(defun bits (x i j)
  (fl (/ (rem x (expt 2 (1+ i))) (expt 2 j))))

(defun cat (x y n)
  (+ (* (expt 2 n) x) y))

(defun mulcat (n x l)
  (if (and (integerp n) (> n 0))
      (cat (mulcat (1- n) x l)
	   x
	   l)
    0))