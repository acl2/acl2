; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; floor-mod.lisp
;;;
;;; This is a start at a book for reasoning about floor and mod.
;;; Most of what is here came from the IHS books and modified.
;;; I believe that I could do better with some meta-rules, but
;;; I need to do a little more tuning of ACL2's handling of
;;; meta-rules first.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;-----------------------------------------------------------------
;;
;; Definitions
;;
;;-----------------------------------------------------------------

(IN-PACKAGE "ACL2")


(local
 (include-book "floor-mod-helper"))

;(defmacro e/d (enable disable)
;  `(union-theories ',enable (disable ,@disable)))

(local
 (in-theory (disable (:executable-counterpart force))))

(defun fm-y-guard (y)
  (cond ((atom y)
	 `((real/rationalp ,y)
	   (not (equal ,y 0))))
	((endp (cdr y))
	 `((real/rationalp ,(car y))
	   (not (equal ,(car y) 0))))
	(t
	 (list* `(real/rationalp ,(car y))
		`(not (equal ,(car y) 0))
		(fm-y-guard (cdr y))))))

(defun fm-x-guard (x)
  (cond ((atom x)
	 `((real/rationalp ,x)))
	((endp (cdr x))
	 `((real/rationalp ,(car x))))
	(t
	 (cons `(real/rationalp ,(car x))
	       (fm-x-guard (cdr x))))))

(defmacro fm-guard (x y)
  (cons 'and
	(append (fm-x-guard x)
		(fm-y-guard y))))

;;-----------------------------------------------------------------
;;
;; Basic definitions and lemmatta
;;
;;-----------------------------------------------------------------

;;(defthm floor-integerp
;;  (integerp (floor x y)))

(defthm integerp-mod
  (implies (and (integerp x)
		(integerp y))
	   (integerp (mod x y)))
  :rule-classes :type-prescription)

(defthm rationalp-mod
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (mod x y)))
  :rule-classes :type-prescription)

#+:non-standard-analysis
(defthm realp-mod
  (implies (and (realp x)
		(realp y))
	   (realp (mod x y)))
  :rule-classes :type-prescription)

(defthm floor-completion
  (implies (or (not (acl2-numberp x))
	       (not (acl2-numberp y)))
	   (equal (floor x y)
		  0)))

(defthm floor-0
  (and (equal (floor x 0)
	      0)
       (equal (floor 0 y)
	      0)))

(defthm mod-completion
  (and (implies (not (acl2-numberp x))
		(equal (mod x y)
		       0))
       (implies (not (acl2-numberp y))
		(equal (mod x y)
		       (fix x)))))

(defthm mod-0
  (and (equal (mod 0 y)
	      0)
       (equal (mod x 0)
	      (fix x))))

(defthm floor-mod-elim
  ;; [Jared] modified on 2014-07-29 to not forcibly assume acl2-numberp, to
  ;; avoid name clash with arithmetic-5.
  (implies (acl2-numberp x)
	   (equal (+ (mod x y) (* y (floor x y))) x))
  :hints (("Goal" :in-theory (disable floor)))
  :rule-classes ((:rewrite)
		 (:elim)))

;;-----------------------------------------------------------------
;;
;; alternate, recursive, definitions.
;;
;;-----------------------------------------------------------------


(defun floor* (x y)
  (declare (xargs :measure (abs (floor x y))))
    (cond ((not (real/rationalp x))
	   t)
	  ((not (real/rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (1- (floor* (+ x y) y)))
		 ((< y x)
		  t)
		 (t
		  (1+ (floor* (- x y) y)))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (1- (floor* (+ x y) y)))
		 ((< x y)
		  t)
		 (t
		  (1+ (floor* (- x y) y)))))))

(defun mod* (x y)
  (declare (xargs :measure (abs (floor x y))))
    (cond ((not (real/rationalp x))
	   t)
	  ((not (real/rationalp y))
	   t)
	  ((equal y 0)
	   t)
	  ((< y 0)
	   (cond ((< 0 x)
		  (mod* (+ x y) y))
		 ((< y x)
		  t)
		 (t
		  (mod* (- x y) y))))
	  (t  ;; (< 0 y)
	   (cond ((< x 0)
		  (mod* (+ x y) y))
		 ((< x y)
		  t)
		 (t
		  (mod* (- x y) y))))))

(defthm ifloor-ind
  t
  :rule-classes ((:induction :pattern (floor x y)
			     :scheme (floor* x y))))

(defthm imod-ind
  t
  :rule-classes ((:induction :pattern (mod x y)
			     :scheme (mod* x y))))

;;-----------------------------------------------------------------
;;
;; Simple bounds.
;;
;;-----------------------------------------------------------------

(defthm floor-bounds-1
  (implies (fm-guard x y)
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(defthm floor-bounds-2
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(defthm floor-bounds-3
  (implies (and (fm-guard x y)
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(in-theory (disable floor))

(defthm mod-bounds-1
  (implies (and (fm-guard x y)
		(< 0 y))
	   (and (<= 0 (mod x y))
		(< (mod x y) y)))
  :rule-classes ((:generalize)
		 (:linear)
                 (:forward-chaining)))

(defthm mod-bounds-2
  (implies (and (fm-guard x y)
		(< y 0))
	   (and (<= (mod x y) 0)
		(< y (mod x y))))
  :rule-classes ((:generalize)
		 (:linear)
                 (:forward-chaining)))

(defthm mod-bounds-3
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal 0 (mod x y)))
  :rule-classes ((:generalize)
		 (:linear)
                 (:forward-chaining)))

;;-----------------------------------------------------------------
;;
;; Type-prescription and linear rules.
;;
;;-----------------------------------------------------------------

(in-theory (disable floor mod))

(defthm floor-nonnegative
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= 0 x)
		  (<= x 0)))
	   (<= 0 (floor x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)))

(defthm floor-nonpositive
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= x 0)
		  (<= 0 x)))
	   (<= (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)))

(defthm floor-positive
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= y x)
		  (<= x y)))
	   (< 0 (floor x y)))
;;  :hints (("Subgoal 4.1.2'" :in-theory
;;                            (enable prefer-positive-exponents-match-base)))
;;  :otf-flg t
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (< 0 (floor x y))
				  (if (< 0 y)
				      (<= y x)
				    (<= x y)))))))

(defthm floor-negative
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (< x 0)
		  (< 0 x)))
	   (< (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (< (floor x y) 0)
				  (if (< 0 y)
				      (< x 0)
				    (< 0 x)))))))

(defthm floor-=-x/y
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y) (/ x y)))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (floor x y) (/ x y))
				  (integerp (/ x y)))))))

(defthm floor-zero
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (<= 0 x)
			 (< x y))
		  (and (<= x 0)
		       (< y x))))
	   (equal (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (floor x y) 0)
				  (if (< 0 y)
				      (and (<= 0 x)
					   (< x y))
				    (and (<= x 0)
					 (< y x))))))))

(defthm floor-one
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (<= y x)
			 (< x (* 2 y)))
		  (and (<= x y)
		       (< (* 2 y) x))))
	    (equal (floor x y) 1))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (floor x y) 1)
				  (if (< 0 y)
				      (and (<= y x)
					   (< x (* 2 y)))
				    (and (<= x y)
					 (< (* 2 y) x))))))))

(defthm floor-minus-one
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (< x 0)
			 (<= (- x) y))
		  (and (< 0 x)
		       (<= y (- x)))))
	    (equal (floor x y) -1))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (floor x y) -1)
				  (if (< 0 y)
				      (and (< x 0)
					   (<= (- x) y))
				    (and (< 0 x)
					 (<= y (- x)))))))))

(defthm mod-nonnegative
  (implies (and (fm-guard x y)
		(< 0 y))
	   (<= 0 (mod x y)))
  :rule-classes ((:rewrite)
		 (:type-prescription)))

(defthm mod-nonpositive
  (implies (and (fm-guard x y)
		(< y 0))
	   (<= (mod x y) 0))
  :rule-classes ((:rewrite)
		 (:type-prescription)))


(defthm mod-positive
  (implies (and (fm-guard x y)
		(< 0 y)
		(not (integerp (/ x y))))
	   (< 0 (mod x y)))
  :rule-classes ((:rewrite)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		   (implies (fm-guard x y)
			    (equal (< 0 (mod x y))
				   (and (< 0 y)
					(not (integerp (/ x y)))))))))

(defthm mod-negative
  (implies (and (fm-guard x y)
		(< y 0)
		(not (integerp (/ x y))))
	   (< (mod x y) 0))
  :rule-classes ((:rewrite)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		   (implies (fm-guard x y)
			    (equal (< (mod x y) 0)
				   (and (< y 0)
					(not (integerp (/ x y)))))))))

(defthm mod-zero
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal (mod x y) 0))
  :rule-classes ((:rewrite)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		   (implies (fm-guard x y)
			    (equal (equal (mod x y) 0)
				   (integerp (/ x y)))))))

(defthm mod-x-y-=-x
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (<= 0 x)
			 (< x y))
		  (and (<= x 0)
		       (< y x))))
	   (equal (mod x y) x))
  :rule-classes ((:rewrite :backchain-limit-lst 1)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (mod x y) x)
				  (if (< 0 y)
				      (and (<= 0 x)
					   (< x y))
				    (and (<= x 0)
					 (< y x))))))))

(defthm mod-x-y-=-x-+-y
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (< x 0)
			 (<= (- x) y))
		  (and (< 0 x)
		       (<= y (- x)))))
	    (equal (mod x y) (+ x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (mod x y) (+ x y))
				  (if (< 0 y)
				      (and (< x 0)
					   (<= (- x) y))
				    (and (< 0 x)
					 (<= y (- x)))))))))

(defthm mod-x-y-=-x---y   ;;; xxx
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (and (<= y x)
			 (< x (* 2 y)))
		  (and (<= x y)
		       (< (* 2 y) x))))
           (equal (mod x y) (- x y)))
  :hints (("Goal" :in-theory (enable mod)))  ;;; New hint.
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (mod x y) (- x y))
				  (if (< 0 y)
				      (and (<= y x)
					   (< x (* 2 y)))
				    (and (<= x y)
					 (< (* 2 y) x))))))))

;;-----------------------------------------------------------------
;;
;; ???
;;
;;-----------------------------------------------------------------

(defthm justify-floor-recursion
  (and (implies (and (real/rationalp x)
		     (< 0 x)
		     (real/rationalp y)
		     (< 1 y))
		(< (floor x y) x))
       (implies (and (real/rationalp x)
		     (< x -1)
		     (real/rationalp y)
		     (<= 2 y))
		(< x (floor x y)))))

;;-----------------------------------------------------------------
;;
;; Simple reductions
;;
;;-----------------------------------------------------------------

(defthm rewrite-floor-x*y-z-right
  (implies (fm-guard x (y z))
	   (equal (floor (* x y) z)
		  (floor x (/ z y))))
  :hints (("Goal" :by rewrite-floor-x*y-z-rightxxx)))

(in-theory (disable rewrite-floor-x*y-z-right))

(defthm rewrite-mod-x*y-z-right
  (implies (fm-guard x (y z))
	   (equal (mod (* x y) z)
		  (* y (mod x (/ z y)))))
  :hints (("Goal" :by rewrite-mod-x*y-z-rightxxx)))

(in-theory (disable rewrite-mod-x*y-z-right))

(defthm floor-minus
  (implies (fm-guard x y)
	    (equal (floor (- x) y)
		   (if (integerp (* x (/ y)))
		       (- (floor x y))
		     (+ (- (floor x y)) -1)))))

(defthm floor-minus-2
  (implies (fm-guard x y)
	    (equal (floor x (- y))
		   (if (integerp (* x (/ y)))
		       (- (floor x y))
		     (+ (- (floor x y)) -1)))))

(defthm mod-minus
  (implies (fm-guard x y)
	   (equal (mod (- x) y)
		  (if (integerp (/ x y))
		      0
		    (- y (mod x y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-minus-2
  (implies (fm-guard x y)
	   (equal (mod x (- y))
		  (if (integerp (/ x y))
		      0
		    (- (mod x y) y))))
  :hints (("Goal" :in-theory (enable mod))))

; These next two theorems could easily loop.

(defthm floor-+
  (implies (fm-guard (x y) z)
	   (equal (floor (+ x y) z)
		  (+ (floor (+ (mod x z) (mod y z)) z)
		     (+ (floor x z) (floor y z)))))
  :hints (("Goal" :by  floor-plusxxx)))

(in-theory (disable floor-+))

(defthm mod-+
  (implies (fm-guard (x y) z)
	   (equal (mod (+ x y) z)
		  (mod (+ (mod x z) (mod y z)) z)))
  :hints (("Goal" :by  mod-plusxxx)))

(in-theory (disable mod-+))

(defthm rewrite-floor-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

(defthm rewrite-mod-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (mod (mod x y) z)
		  (mod x z))))
;;  :hints (("Goal" :in-theory (enable mod-+))))


(defthm mod-+-cancel-0
  (implies (and (fm-guard (x y) z))
	   (equal (equal (mod (+ x y) z) x)
		  (and (equal (mod y z) 0)
		       (equal (mod x z) x)))))
;;  :hints (("Subgoal 7" :in-theory (enable mod-+))
;;	  ("Subgoal 6" :in-theory (enable mod-+))
;;	  ("Subgoal 5" :expand (mod (+ x y) z))))







(defthm floor-cancel-*
  (implies (and (fm-guard x y)
		(integerp x))
	   (and (equal (floor (* x y) y)
		       x)
		(equal (floor (* y x) y)
		       x))))

(defthm floor-cancel-*-2
  (implies (and (fm-guard x (y z))
		(integerp z))
	   (equal (floor (* x z) (* y z))
		  (floor x y))))

(defthm mod-minus
  (implies (fm-guard x y)
	   (equal (mod (- x) y)
		  (if (integerp (/ x y))
		      0
		    (- y (mod x y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm simplify-mod-*
  (implies (fm-guard x (y z))
	    (equal (mod (* x y) (* y z))
		   (* y (mod x z))))
  :hints (("Goal" :in-theory (enable mod))))

;;-----------------------------------------------------------------
;;
;; Cancellation
;;
;;-----------------------------------------------------------------

(defthm cancel-floor-+
  (implies (and (equal i (/ x z))
		(integerp i)
		(fm-guard (x y) z))
	   (and (equal (floor (+ x y) z)
		       (+ i (floor y z)))
		(equal (floor (+ y x) z)
		       (+ i (floor y z))))))

(defthm cancel-floor-+-3
  (implies (and (equal i (/ w z))
		(integerp i)
		(fm-guard (w x y) z))
	   (equal (floor (+ x y w) z)
		  (+ i (floor (+ x y) z)))))

(defthm cancel-mod-+
  (implies (and (equal i (/ x z))
		(integerp i)
		(fm-guard (x y) z))
	   (and (equal (mod (+ x y) z)
		       (mod y z))
		(equal (mod (+ y x) z)
		       (mod y z))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm cancel-mod-+-3
  (implies (and (equal i (/ w z))
		(integerp i)
		(fm-guard (w x y) z))
	   (equal (mod (+ x y w) z)
		  (mod (+ x y) z)))
  :hints (("Goal" :by cancel-mod-+-3xxx)))

(defthm rewrite-floor-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

(defthm rewrite-mod-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (mod (mod x y) z)
		  (mod x z))))

(defthm simplify-mod-+-mod
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard (w x) (y z)))
	   (and (equal (mod (+ w (mod x y)) z)
		       (mod (+ w x) z))
		(equal (mod (+ (mod x y) w) z)
		       (mod (+ w x) z))
		(equal (mod (+ w (- (mod x y))) z)
		       (mod (+ w (- x)) z))
		(equal (mod (+ (mod x y) (- w)) z)
		       (mod (+ x (- w)) z)))))

(defthm mod-+-cancel-0
  (implies (and (fm-guard (x y) z))
	   (equal (equal (mod (+ x y) z) x)
		  (and (equal (mod y z) 0)
		       (equal (mod x z) x))))
  :hints (("Subgoal 5" :expand (mod (+ x y) z))))

(defthm floor-floor-integer
  (implies (and (real/rationalp x)
		(integerp i)
		(integerp j)
		(< 0 i)
		(< 0 j))
	   (equal (floor (floor x i) j)
		  (floor x (* i j)))))

;;-----------------------------------------------------------------
;;
;; Simple reductions
;;
;;-----------------------------------------------------------------

(defthm mod-two
  (implies (integerp x)
	   (or (equal (mod x 2) 0)
	       (equal (mod x 2) 1)))
  :rule-classes ((:forward-chaining
		  :corollary
		  (implies (integerp x)
			   (and (<= 0 (mod x 2))
				(< (mod x 2) 2)))
		  :trigger-terms ((mod x 2)))
		 (:generalize)))

;;-----------------------------------------------------------------
;;
;; Simple reductions
;;
;;-----------------------------------------------------------------


(in-theory (disable floor-+))

(in-theory (disable mod-+))
