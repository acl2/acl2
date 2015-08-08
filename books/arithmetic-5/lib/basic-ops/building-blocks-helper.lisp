; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; building-blocks-helper.lisp
;;;
;;; This book contains some messy proofs which I want to hide.
;;; There is probably nothing to be gained by looking at it.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (include-book "../../support/top"))

(local
 (defun rationalp-guard-fn (args)
   (if (endp (cdr args))
       `((rationalp ,(car args)))
     (cons `(rationalp ,(car args))
	   (rationalp-guard-fn (cdr args))))))



(local
 (defmacro rationalp-guard (&rest args)
   (if (endp (cdr args))
       `(rationalp ,(car args))
     (cons 'and
	   (rationalp-guard-fn args)))))

(local
 (defun real/rationalp-guard-fn (args)
   (if (endp (cdr args))
       `((real/rationalp ,(car args)))
     (cons `(real/rationalp ,(car args))
	   (real/rationalp-guard-fn (cdr args))))))



(local
 (defmacro real/rationalp-guard (&rest args)
   (if (endp (cdr args))
       `(real/rationalp ,(car args))
     (cons 'and
	   (real/rationalp-guard-fn args)))))


(local
 (defthm niq-bounds
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :hints (("Subgoal *1/1''" :use (:instance NORMALIZE-<-/-TO-*-3-3
					     (X 1)
					     (Z J)
					     (Y I))))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

(local
 (defthm floor-bounds-1
   (implies (real/rationalp-guard x y)
	    (and (< (+ (/ x y) -1)
		    (floor x y))
		 (<= (floor x y)
		     (/ x y))))
   :rule-classes ((:generalize)
		  (:linear :trigger-terms ((floor x y))))))

(local
 (defthm floor-bounds-2
   (implies (and (real/rationalp-guard x y)
		 (integerp (/ x y)))
	    (equal (floor x y)
		   (/ x y)))
   :rule-classes ((:generalize)
		  (:linear :trigger-terms ((floor x y))))))

(local
 (defthm floor-bounds-3
   (implies (and (real/rationalp-guard x y)
		 (not (integerp (/ x y))))
	    (< (floor x y)
	       (/ x y)))
   :rule-classes ((:generalize)
		  (:linear :trigger-terms ((floor x y))))))

(local
 (in-theory (disable floor)))

(defthm one
  (IMPLIES (AND (INTEGERP x)
		(integerp y)
		(<= 0 y))
	   (<= 0
	       (LOGAND x y)))
  :rule-classes :linear)

(defthm two
  (IMPLIES (AND (INTEGERP x)
		(integerp y)
		(<= 0 y))
	   (<= (LOGAND x y)
	       y))
  :rule-classes :linear)

(defthm rewrite-floor-x*y-z-left
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z)
		(not (equal z 0)))
	   (equal (floor (* x y) z)
		  (floor y (/ z x)))))

(defun power-of-2-measure (x)
  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((or (not (real/rationalp x))
             (<= x 0)) 0)
	((< x 1) (cons (cons 1 1) (floor (/ x) 1)))
	(t (floor x 1))))

(defun power-of-2-helper (x)
  (declare (xargs :guard t
                  :measure (power-of-2-measure x)
		  :hints (("Subgoal 2.2'" :use (:instance
						(:theorem
						 (IMPLIES (AND (REAL/RATIONALP X)
							       (< 2 X))
							  (< (FLOOR X 2) (FLOOR X 1))))
						(x (/ x)))
			                  :in-theory (enable NORMALIZE-<-/-TO-*-1)))))
  (cond ((or (not (real/rationalp x))
             (<= x 0))
         0)
        ((< x 1) (+ -1 (power-of-2-helper (* 2 x))))
        ((<= 2 x) (+ 1 (power-of-2-helper (* 1/2 x))))
        ((equal x 1) 0)
        (t 0) ;got a number in the doubly-open interval (1,2)
        ))