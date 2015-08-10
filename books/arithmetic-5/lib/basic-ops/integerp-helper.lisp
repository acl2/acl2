; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp-helper.lisp
;;;
;;;
;;; This book contains some messy proofs which I want to hide.
;;; There is probably nothing to be gained by looking at it.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(local
 (include-book "../../support/top"))

(include-book "building-blocks")

(include-book "default-hint")

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (local
  (defun INDUCT-NAT (x)
    (if (and (integerp x)
             (> x 0))
        (induct-nat (1- x))
      ())))

 (local
  (defthm x-or-x/2-4
    (implies (and (integerp x) (>= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :induct (induct-nat x))
	    ("Subgoal *1/1''" :use (:instance (:theorem
					       (implies (integerp a)
							(integerp (+ 1 a))))
					      (a (+ -1/2 (* 1/2 X))))))))

 (local
  (defthm x-or-x/2-5
    (IMPLIES (integerp x)
	     (integerp (- x)))
    :rule-classes ()))

 (local
  (defthm foo
    (implies (and (integerp x)
		  (integerp y))
	     (integerp (+ x y)))
    :rule-classes ()))

 (local
  (defthm bar
    (equal (+ X (- (* 1/2 X)))
	   (* 1/2 x))))

 (local
  (defthm x-or-x/2-11
    (implies (and (integerp x) (<= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :in-theory (disable FUNCTIONAL-SELF-INVERSION-OF-MINUS)
             :use ((:instance x-or-x/2-4 (x (- x)))
		   (:instance foo (x (+ 1/2 (- (* 1/2 X)))) (y x)))))))

 (local
  (defthm X-OR-X/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :in-theory (disable FUNCTIONAL-SELF-INVERSION-OF-MINUS)
             :use ((:instance x-or-x/2-4)
                   (:instance x-or-x/2-11))))))

;;; Expressions like (integerp (+ 1/2 x)) show up when one is reasoning
;;; about odd and even.

;;; Note1: We do not have to worry about expressions such as
;;; (integerp (+ -1/2 x)) or (integerp (+ 3/2 x)) because of
;;; integerp-+-reduce-leading-constant.

;;; Note 2: We could write a similar rule --- probably a meta rule
;;; --- for expressions such as (integerp (+ 1/3 x)) and
;;; (integerp (+ 3/10 x)).  For (integerp (+ c/d x)), (* n x) is not
;;; an integer for all 0 < n < d.  But this would probably be a messy
;;; proof to do --- it would depend on c/d being in lowest terms ---
;;; but I have not thought about it yet.

 (defthm even-and-odd-alternate
   (implies (acl2-numberp x)
            (equal (integerp (+ 1/2 x))
                   (and (integerp (* 2 x))
                        (not (integerp x)))))
   :hints (("Subgoal 3'"
            :use ((:instance
                   (:theorem (implies (and (integerp x)
                                           (integerp y))
                                      (integerp (* x y))))
                   (x (+ 1/2 x))
                   (y 2))))
           ("Subgoal 2'"
            :use ((:instance X-OR-X/2
                             (x (* 2 x)))))))

  (local
   (defun ind (x)
     (cond ((not (integerp x))
	    t)
	   ((< x -1)
	    (ind (+ 2 x)))
	   ((< 1 x)
	    (ind (+ -2 x)))
	   ((equal x -1)
	    t)
	   ((equal x 0)
	    t)
	   ((equal x 1)
	    t)
	   (t
	    t))))

  (local
   (defthm reduce-integerp
     (implies (and (integerp x)
		   (acl2-numberp y))
	      (iff (integerp (+ x y))
		   (integerp y)))))

  (defthm sum-is-even-helper
    (implies (and (integerp x)
		  (integerp y))
	     (equal (integerp (+ (* 1/2 x) (* 1/2 y)))
		    (if (integerp (* 1/2 x))
			(integerp (* 1/2 y))
		      (not (integerp (* 1/2 y))))))
    :hints (("Goal" :induct (ind x))
	    ("Subgoal *1/3.1" :use (:instance X-OR-X/2
					      (x y))
	                      :in-theory (disable even-and-odd-alternate))))

 )