
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; simple-equalities-and-inequalities-helper.lisp
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

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
 (defthm niq-bounds
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :hints (("Subgoal *1/1''" :in-theory (enable NORMALIZE-<-/-TO-*-3-3)))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

(local
(defthm floor-bounds-1
  (implies (rationalp-guard x y)
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))

(local
(defthm floor-bounds-2
  (implies (and (rationalp-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))

(local
(defthm floor-bounds-3
  (implies (and (rationalp-guard x y)
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize) 
		 (:linear :trigger-terms ((floor x y))))))


(local
 (in-theory (disable floor)))

(defthm integerp-<-constant
  (implies (and (syntaxp (rational-constant-p c))
		(rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< x c)
                  (<= x (floor c 1))))
  :otf-flg t)

(defthm constant-<-integerp
  (implies (and (syntaxp (rational-constant-p c))
                (rationalp c)
		(not (integerp c))
		(integerp x))
           (equal (< c x)
                  (<= (+ 1 (floor c 1)) x)))
  :otf-flg t)

