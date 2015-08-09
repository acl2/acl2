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

(local (include-book "../meta/top"))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

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

(local
 (defthm niq-boundsxxx
   (implies (and (integerp i)
		 (<= 0 i)
		 (integerp j)
		 (< 0 j))
	    (and (<= (nonnegative-integer-quotient i j)
		     (/ i j))
		 (< (+ (/ i j) -1)
		    (nonnegative-integer-quotient i j))))
   :hints (("Subgoal *1/1''" :in-theory
                             (enable prefer-positive-exponents-gather-exponents)))
   :rule-classes ((:linear
		   :trigger-terms ((nonnegative-integer-quotient i j))))))

;;-----------------------------------------------------------------
;;
;; Basic definitions and lemmatta
;;
;;-----------------------------------------------------------------

;;(defthm floor-integerpxxx
;;  (integerp (floor x y)))

(defthm integerp-modxxx
  (implies (and (integerp x)
		(integerp y))
	   (integerp (mod x y)))
  :rule-classes :type-prescription)

(defthm rationalp-modxxx
  (implies (and (rationalp x)
		(rationalp y))
	   (rationalp (mod x y)))
  :rule-classes :type-prescription)

#+:non-standard-analysis
(defthm realp-modxxx
  (implies (and (realp x)
		(realp y))
	   (realp (mod x y)))
  :rule-classes :type-prescription)

(defthm floor-completionxxx
  (implies (or (not (acl2-numberp x))
	       (not (acl2-numberp y)))
	   (equal (floor x y)
		  0)))

(defthm floor-0xxx
  (and (equal (floor x 0)
	      0)
       (equal (floor 0 y)
	      0)))

(defthm mod-completionxxx
  (and (implies (not (acl2-numberp x))
		(equal (mod x y)
		       0))
       (implies (not (acl2-numberp y))
		(equal (mod x y)
		       (fix x)))))

(defthm mod-0xxx
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

(defthm ifloor-indxxx
  t
  :rule-classes ((:induction :pattern (floor x y)
			     :scheme (floor* x y))))

(defthm imod-indxxx
  t
  :rule-classes ((:induction :pattern (mod x y)
			     :scheme (mod* x y))))

;;-----------------------------------------------------------------
;;
;; Simple bounds.
;;
;;-----------------------------------------------------------------

(defthm floor-bounds-1xxx
  (implies (fm-guard x y)
	   (and (< (+ (/ x y) -1)
		   (floor x y))
		(<= (floor x y)
		    (/ x y))))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(defthm floor-bounds-2xxx
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y)
		  (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(defthm floor-bounds-3xxx
  (implies (and (fm-guard x y)
		(not (integerp (/ x y))))
	   (< (floor x y)
	      (/ x y)))
  :rule-classes ((:generalize)
		 (:linear :trigger-terms ((floor x y)))
                 (:forward-chaining :trigger-terms ((floor x y)))))

(in-theory (disable floor))

(defthm mod-bounds-1xxx
  (implies (and (fm-guard x y)
		(< 0 y))
	   (and (<= 0 (mod x y))
		(< (mod x y) y)))
  :rule-classes ((:generalize)
		 (:linear)
                 (:forward-chaining)))

(defthm mod-bounds-2xxx
  (implies (and (fm-guard x y)
		(< y 0))
	   (and (<= (mod x y) 0)
		(< y (mod x y))))
  :rule-classes ((:generalize)
		 (:linear)
                 (:forward-chaining)))

(defthm mod-bounds-3xxx
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

(defthm floor-nonnegativexxx
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= 0 x)
		  (<= x 0)))
	   (<= 0 (floor x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)))

(defthm floor-nonpositivexxx
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= x 0)
		  (<= 0 x)))
	   (<= (floor x y) 0))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)))

(defthm floor-positivexxx
  (implies (and (fm-guard x y)
		(if (< 0 y)
		    (<= y x)
		  (<= x y)))
	   (< 0 (floor x y)))
  :hints (("Subgoal 4.1.2'" :in-theory
                            (enable prefer-positive-exponents-gather-exponents)))
  :otf-flg t
  :rule-classes ((:rewrite :backchain-limit-lst 0)
		 (:type-prescription)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (< 0 (floor x y))
				  (if (< 0 y)
				      (<= y x)
				    (<= x y)))))))

(defthm floor-negativexxx
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

(defthm floor-=-x/yxxx
  (implies (and (fm-guard x y)
		(integerp (/ x y)))
	   (equal (floor x y) (/ x y)))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (fm-guard x y)
			   (equal (equal (floor x y) (/ x y))
				  (integerp (/ x y)))))))

(defthm floor-zeroxxx
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

(defthm floor-onexxx
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

(defthm floor-minus-onexxx
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

(defthm mod-nonnegativexxx
  (implies (and (fm-guard x y)
		(< 0 y))
	   (<= 0 (mod x y)))
  :rule-classes ((:rewrite)
		 (:type-prescription)))

(defthm mod-nonpositivexxx
  (implies (and (fm-guard x y)
		(< y 0))
	   (<= (mod x y) 0))
  :rule-classes ((:rewrite)
		 (:type-prescription)))


(defthm mod-positivexxx
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

(defthm mod-negativexxx
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

(defthm mod-zeroxxx
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

(defthm mod-x-y-=-xxxx
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

(defthm mod-x-y-=-x-+-yxxx
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

(defthm mod-x-y-=-x---y   ;;; xxxxxx
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

(defthm justify-floor-recursionxxx
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

(defthm rewrite-floor-x*y-z-rightxxx
  (implies (fm-guard x (y z))
	   (equal (floor (* x y) z)
		  (floor x (/ z y)))))

(in-theory (disable rewrite-floor-x*y-z-rightxxx))

(defthm rewrite-mod-x*y-z-rightxxx
  (implies (fm-guard x (y z))
	   (equal (mod (* x y) z)
		  (* y (mod x (/ z y)))))
  :hints (("Goal" :in-theory (enable mod))))

(in-theory (disable rewrite-mod-x*y-z-rightxxx))

(defthm floor-minusxxx
  (implies (fm-guard x y)
	    (equal (floor (- x) y)
		   (if (integerp (* x (/ y)))
		       (- (floor x y))
		     (+ (- (floor x y)) -1)))))

(defthm floor-minus-2xxx
  (implies (fm-guard x y)
	    (equal (floor x (- y))
		   (if (integerp (* x (/ y)))
		       (- (floor x y))
		     (+ (- (floor x y)) -1)))))

(defthm mod-minusxxx
  (implies (fm-guard x y)
	   (equal (mod (- x) y)
		  (if (integerp (/ x y))
		      0
		    (- y (mod x y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm mod-minus-2xxx
  (implies (fm-guard x y)
	   (equal (mod x (- y))
		  (if (integerp (/ x y))
		      0
		    (- (mod x y) y))))
  :hints (("Goal" :in-theory (enable mod))))

; These next two theorems could easily loop.

(defthm floor-plusxxx
  (implies (fm-guard (x y) z)
	   (equal (floor (+ x y) z)
		  (+ (floor (+ (mod x z) (mod y z)) z)
		     (+ (floor x z) (floor y z)))))
  :hints (("Goal" :use ((:instance floor-+)))))

(in-theory (disable floor-plusxxx))

(defthm mod-plusxxx
  (implies (fm-guard (x y) z)
	   (equal (mod (+ x y) z)
		  (mod (+ (mod x z) (mod y z)) z)))
  :hints (("Goal" :in-theory (enable mod))))

(in-theory (disable mod-plusxxx))

(defthm rewrite-floor-modxxx
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

(defthm rewrite-mod-modxxx
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (mod (mod x y) z)
		  (mod x z))))
;;  :hints (("Goal" :in-theory (enable mod-+))))


(defthm mod-+-cancel-0xxx
  (implies (and (fm-guard (x y) z))
	   (equal (equal (mod (+ x y) z) x)
		  (and (equal (mod y z) 0)
		       (equal (mod x z) x)))))
;;  :hints (("Subgoal 7" :in-theory (enable mod-+))
;;	  ("Subgoal 6" :in-theory (enable mod-+))
;;	  ("Subgoal 5" :expand (mod (+ x y) z))))







(defthm floor-cancel-*xxx
  (implies (and (fm-guard x y)
		(integerp x))
	   (and (equal (floor (* x y) y)
		       x)
		(equal (floor (* y x) y)
		       x))))

(defthm floor-cancel-*-2xxx
  (implies (and (fm-guard x (y z))
		(integerp z))
	   (equal (floor (* x z) (* y z))
		  (floor x y))))

(defthm mod-minusxxx
  (implies (fm-guard x y)
	   (equal (mod (- x) y)
		  (if (integerp (/ x y))
		      0
		    (- y (mod x y)))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm simplify-mod-*xxx
  (implies (fm-guard x (y z))
	    (equal (mod (* x y) (* y z))
		   (* y (mod x z))))
  :hints (("Goal" :in-theory (enable mod))))

;;-----------------------------------------------------------------
;;
;; Cancellation
;;
;;-----------------------------------------------------------------

(defthm cancel-floor-+xxx
  (implies (and (equal i (/ x z))
		(integerp i)
		(fm-guard (x y) z))
	   (and (equal (floor (+ x y) z)
		       (+ i (floor y z)))
		(equal (floor (+ y x) z)
		       (+ i (floor y z))))))

(defthm cancel-floor-+-3xxx
  (implies (and (equal i (/ w z))
		(integerp i)
		(fm-guard (w x y) z))
	   (equal (floor (+ x y w) z)
		  (+ i (floor (+ x y) z)))))

(defthm cancel-mod-+xxx
  (implies (and (equal i (/ x z))
		(integerp i)
		(fm-guard (x y) z))
	   (and (equal (mod (+ x y) z)
		       (mod y z))
		(equal (mod (+ y x) z)
		       (mod y z))))
  :hints (("Goal" :in-theory (enable mod))))

(defthm cancel-mod-+-3xxx
  (implies (and (equal i (/ w z))
		(integerp i)
		(fm-guard (w x y) z))
	   (equal (mod (+ x y w) z)
		  (mod (+ x y) z))))

(defthm rewrite-floor-modxxx
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (floor (mod x y) z)
		  (- (floor x z) (* i (floor x y))))))

(defthm rewrite-mod-modxxx
  (implies (and (equal i (/ y z))
		(integerp i)
		(fm-guard x (y z)))
	   (equal (mod (mod x y) z)
		  (mod x z))))

(defthm simplify-mod-+-modxxx
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

(defthm mod-+-cancel-0xxx
  (implies (and (fm-guard (x y) z))
	   (equal (equal (mod (+ x y) z) x)
		  (and (equal (mod y z) 0)
		       (equal (mod x z) x))))
  :hints (("Subgoal 5" :expand (mod (+ x y) z))))

(defthm floor-floor-integerxxx
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

(defthm mod-twoxxx
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
