; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; expt-helper.lisp
;;
;; This book contains some messy proofs which I want to hide.
;; There is probably nothing to be gained by looking at it.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local
 (include-book "../../support/top"))

(local
 (include-book "default-hint"))

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(local
 (in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
		     FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

(local
(in-arithmetic-theory '((:REWRITE arith-associativity-of-*)
                        (:REWRITE arith-commutativity-of-*)
                        (:REWRITE arith-commutativity-2-of-*)
                        (:REWRITE arith-unicity-of-1)
                        (:REWRITE arith-times-zero)
                        (:REWRITE arith-inverse-of-*-1)
                        (:REWRITE arith-inverse-of-*-2)
                        (:REWRITE arith-inverse-of-*-3)
                        (:REWRITE arith-functional-self-inversion-of-/ )
                        (:REWRITE arith-distributivity-of-/-over-*)
                       ;(:REWRITE arith-functional-commutativity-of-minus-*-right)
                       ;(:REWRITE arith-functional-commutativity-of-minus-*-left)
                        (:REWRITE arith-reciprocal-minusa)
                        (:REWRITE arith-distributivity-1)
                        (:REWRITE arith-distributivity-2)
                        (:REWRITE arith-fold-consts-in-*)
                        (:REWRITE arith-expt-0)
                        (:REWRITE arith-expt-1)
                        (:REWRITE arith-expt-minus-1)
                        (:REWRITE arith-functional-commutativity-of-expt-/)
                        (:REWRITE arith-expt-minus-exponent)
                        (:REWRITE arith-expt-negative-constant-exponent)
                        (:REWRITE arith-exponents-multiply)
                        (:REWRITE arith-distributivity-of-expt-over-*)
                        (:REWRITE arith-fix-revealed)
                        (:REWRITE arith-Rational-implies2)
                        (:REWRITE arith-exponents-add-1)
                        (:REWRITE arith-exponents-add-for-nonpos-exponentsa)
                        (:REWRITE arith-exponents-add-for-nonneg-exponentsa)
                        (:REWRITE arith-exponents-add-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun ind (x)
   (if (integerp x)
       (cond ((equal x 0) t)
	     ((equal x -1) t)
	     ((equal x 1) t)
	     ((< 0 x) (ind (- x 2)))
	     ((< x 0) (ind (+ x 2))))
       t)))

(local
 (encapsulate
  ()

  (local
   (defthm hack1a
     (implies (integerp x)
	      (integerp (+ -1 x)))))

  (local
   (defthm hack1b
     (implies (integerp x)
	      (integerp (+ x 1)))))

  (defthm odd-and-even
    (implies (and (integerp x)
		  (not (integerp (* 1/2 x))))
	     (integerp (+ -1/2 (* 1/2 x))))  ; (* 1/2 (- x 1))))
    :hints (("Goal" :induct (ind x))
	    ("Subgoal *1/5'''" :use ((:instance hack1a
						(x (+ 1/2 R)))))
	    ("Subgoal *1/4'''":use ((:instance hack1b
					       (x (+ -3/2 R))))))
    :rule-classes :type-prescription)

  ))


(encapsulate
 ()

 (local
  (defthm expt-x-2
    (implies (and (real/rationalp x)
		  (not (equal x 0)))
	     (< 0 (expt x 2)))))

 (local
  (defthm <-0-expt-x-2
    (implies (and (< r 0)
		  (real/rationalp r)
		  (integerp i))
	     (< 0 (expt (expt r i) 2)))
    :hints (("Goal" :use ((:instance expt-x-2
				     (x (expt r i))))))))

 (defthm expt-type-prescription-negative-base-even-exponent-a
   (implies (and (< r 0)
		 (real/rationalp r)
		 (integerp i)
		 (integerp (* 1/2 i)))
	    (< 0 (expt r i)))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance <-0-expt-x-2
				    (i (* 1/2 i)))))))

 (local
  (defthm reduce
    (implies (and (integerp i)
		  (real/rationalp r)
		  (not (equal r 0)))
	     (equal (expt r i)
		    (* r (expt r (- i 1)))))))

 (defthm expt-type-prescription-negative-base-odd-exponent-a
   (implies (and (< r 0)
		 (real/rationalp r)
		 (integerp i)
		 (not (integerp (* 1/2 i))))
	    (< (expt r i) 0))
   :rule-classes (:type-prescription :generalize)
   :hints (("Goal" :use ((:instance
			  expt-type-prescription-negative-base-even-exponent-a
				    (r r)
				    (i (- i 1)))
			 (:instance reduce))
	    :in-theory (disable reduce))))

 )




(local
 (in-theory (enable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
		     FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT)))

(defthm expt-negative-base-even-exponent-a
  (implies (and (integerp i)
		(integerp (* 1/2 i)))
	   (equal (expt (- r) i)
		  (expt r i)))
  :hints (("Goal" :induct (ind i))))

(encapsulate
 ()

 (local
  (defthm expt-negative-base-odd-exponent-hack
      (implies (and (integerp i)
                    (not (integerp (* 1/2 i))))
               (equal (expt (* -1 r) i)
                      (* -1 (expt  r i))))
    :hints (("Goal" :induct (ind i)))
    :rule-classes nil))

 (local
  (defthm hack654
      (equal (* -1 x)
             (- x))))

 (defthm expt-negative-base-odd-exponent-a
     (implies (and (integerp i)
                   (not (integerp (* 1/2 i))))
              (equal (expt (- r) i)
                     (- (expt  r i))))
   :hints (("Goal" :use expt-negative-base-odd-exponent-hack)))

 )

(encapsulate ()

 (local
  (defthm onea
    (equal (- (/ x))
	   (/ (- x)))))

  (local
   (in-theory (disable RECIPROCAL-MINUS-A)))

 (local
  (defthm one
    (implies (real/rationalp x)
	     (equal (equal (abs (/ x)) 1)
		    (equal (abs x) 1)))
    :otf-flg t))

  (local
   (defthm oner
     (implies (real/rationalp x)
	      (equal (equal (- x) 1)
		     (equal x -1)))))

  (local
   (defthm onex
     (implies (and (real/rationalp x)
		   (real/rationalp y)
		   (equal (abs (* x y)) 1)
		   (equal (abs x) 1))
	      (equal (abs y) 1))
     :otf-flg t))

  (local
   (defthm oney
     (implies (and (real/rationalp x)
		   (real/rationalp y))
	      (equal (abs (* x y))
		     (* (abs x) (abs y))))))

 (local
  (defthm www
    (implies (real/rationalp x)
	     (real/rationalp (abs x)))))

 (local
  (defthm ee
    (<= 0 (abs x))))

 (local
  (defthm nnn
    (implies (and (real/rationalp x)
		  (not (equal x 0))
		  (< (abs x) 1))
	     (< 1 (abs (/ x))))
    :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-1)))))

 (local
  (defthm nnn-2
    (implies (and (real/rationalp x)
		  (not (equal x 0))
		  (< 1 (abs x)))
	     (< (abs (/ x)) 1))
    :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-2)))))

 (local
  (defthm nnn-3
    (implies (and (real/rationalp x)
		  (not (equal x 0)))
	     (not (equal (abs (/ x)) 0)))))
#|
 (local
  (defthm nnn-4
    (implies (rationalp x)
	     (equal (<= (abs x) 0)
		    (equal x 0)))))
|#
 (local
  (defthm nnn-4
    (implies (real/rationalp x)
	     (equal (< 0 (abs x))
		    (not (equal x 0))))))

 (local
  (defthm foo
    (implies (and (real/rationalp x)
		  (not (equal x 0)))
	     (< 0 (abs (/ x))))))

 (local
  (in-theory (e/d (zip) (abs))))

 (local
  (defthm xxx1
    (implies (and (integerp n)
		  (real/rationalp x)
		  (equal n 0))
	     (equal (abs (expt x n)) 1))))

 (local
  (defthm xxx2
    (implies (and (integerp n)
		  (real/rationalp x)
		  (equal (abs x) 1))
	     (equal (abs (expt x n)) 1))
    :hints (("Goal" :do-not '(generalize)))))

 (local
  (defthm qqq
    (implies (and (real/rationalp x)
		  (real/rationalp y))
	     (equal (< 0 (* x y))
		    (cond ((equal x 0)
			   nil)
			  ((< x 0)
			   (< y 0))
			  (t
			   (< 0 y)))))))

 (local
  (defthm ggg
    (implies (real/rationalp x)
	     (real/rationalp (/ x)))))

 (local
  (defthm hhh
    (implies (real/rationalp x)
	     (real/rationalp (expt x n)))))

 ;;; Do I really have non-linear arithmetic enabled?

 (local
  (defthm ddd
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (< 0 x)
		  (< x 1)
		  (< 0 y)
		  (< y 1))
	     (< (* x y) 1))
    :hints (("Goal" :use (:instance <-*-X-Y-Y)
	            :in-theory (disable <-*-X-Y-Y)))))

 (local
  (defthm ddd-2
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< 0 x)
		  (< x 1)
		  (< 0 (* y z))
		  (< (* y z) 1))
	     (< (* y x z) 1))))

 (local
  (defthm jjj
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (< 1 x)
		  (< 1 y))
	     (< 1 (* x y)))
    :hints (("Goal" :use (:instance <-Y-*-X-Y)
	            :in-theory (disable <-Y-*-X-Y)))))

 (local
  (defthm jjj-2
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< 1 x)
		  (< 1 (* y z)))
	     (< 1 (* y x z)))))

 (local
  (defthm yyy1
     (implies (and (integerp n)
		   (real/rationalp x)
		   (< 0 n)
		   (< 0 (abs x))
		   (< (abs x) 1))
	      (and (< 0 (abs (expt x n)))
		   (< (abs (expt x n)) 1)))
    :hints (("Goal" :do-not '(generalize)))))

 (local
  (defthm yyy2
     (implies (and (integerp n)
		   (real/rationalp x)
		   (< 0 n)
		   (< 1 (abs x)))
	      (< 1 (abs (expt x n))))
    :hints (("Goal" :do-not '(generalize)))))

 (local
  (defthm yyy3
     (implies (and (integerp n)
		   (real/rationalp x)
		   (< n 0)
		   (< 0 (abs x))
		   (< (abs x) 1))
	      (< 1 (abs (expt x n))))
    :hints (("Goal" :do-not '(generalize)))))

 (local
  (defthm yyy4
     (implies (and (integerp n)
		   (real/rationalp x)
		   (< n 0)
		   (< 1 (abs x)))
	      (and (< 0 (abs (expt x n)))
		   (< (abs (expt x n)) 1)))
    :hints (("Goal" :do-not '(generalize)))))

 (local
  (defthm oneb
    (implies (and (integerp n)
		  (real/rationalp x))
	     (equal (equal (abs (expt x n)) 1)
		    (or (equal n 0)
			(equal (abs x) 1))))
    :hints (("Goal" :use (xxx1 xxx2 yyy1 yyy2 yyy3 yyy4)
	            :in-theory (disable xxx1 xxx2 yyy1 yyy2 yyy3 yyy4)
		    :do-not-induct t))
    :otf-flg t))

 (defthm |(equal (expt x n) -1)|
   (implies (and (integerp n)
		 (real/rationalp x))
	    (equal (equal (expt x n) -1)
		   (and (equal x -1)
			(oddp n))))
   :hints (("Goal" :use oneb
	           :in-theory (e/d (abs) (oneb)))))

 (defthm |(equal (expt x n) 1) --- helper|
   (implies  (and (integerp n)
		  (real/rationalp x))
	     (equal (equal (expt x n) 1)
		    (or (zip n)
			(equal x 1)
			(and (equal x -1)
			     (evenp n)))))
   :hints (("Goal" :use oneb
	           :in-theory (e/d (abs) (oneb)))))
 )

(encapsulate ()

 (local
  (defthm two
    (implies (acl2-numberp n)
	     (equal (* -1 n)
		    (- n)))))

 (defthm |(expt x (* c n))|
   (implies (and (syntaxp (quotep c))
		(syntaxp (and (< c 5)
			      (< -5 c)))
                (integerp c)
                (not (equal c 0))
		(real/rationalp x)
		(integerp n))
           (equal (expt x (* c n))
                  (cond ((< c 0)
                         (* (/ (expt x n)) (expt x (* (+ c 1) n))))
                        (t  ; (< 0 c)
                         (* (expt x n) (expt x (* (- c 1) n)))))))
   :hints (("Goal" :in-theory (e/d (EXPTS-ADD-INVERSE)
				   (expt EXPONENTS-ADD-2 EXPONENTS-ADD-1 equal-/))
	    :use (:instance ARITH-EXPT-MINUS-EXPONENT
			    (r x)
			    (i n)))))
)

(encapsulate ()

 (local
  (defthm three
    (implies (and (real/rationalp x)
		  (< 0 x)
		  (< x 1))
	     (not (integerp x)))))

 (local
  (defthm threea
    (implies (and (integerp x)
		  (< 1 x))
	     (and (< 0 (/ x))
		  (< (/ x) 1)))
    :hints (("Goal" :in-theory (enable NORMALIZE-<-/-TO-*-2)))))

 (local
  (defthm threeb
    (IMPLIES (AND (INTEGERP X) (< 1 X))
	     (NOT (INTEGERP (/ X))))))

 (defthm |(integerp (expt x n))|
   (implies (and (integerp n)
		 (integerp x)
		 (< 1 x))
	    (equal (integerp (expt x n))
		   (<= 0 n))))
 )

(encapsulate ()

 (local
  (defun ind-hint (i)
    (cond ((zip i)
	   t)
	  ((< 0 i)
	   (ind-hint (+ -1 i)))
	  (t
	   (ind-hint (+ 1 i))))))

 (local
  (defthm four
    (implies (and (real/rationalp x)
		  (< 1 x)
		  (integerp m)
		  (integerp i))
	     (equal (< (expt x m) (expt x (+ m i)))
		    (< 0 i)))
    :hints (("Goal" :induct (ind-hint i)))))

 (defthm |(< (expt x n) (expt x m))|
   (implies (and (real/rationalp x)
		 (< 1 x)
		 (integerp m)
		 (integerp n))
	    (equal (< (expt x m) (expt x n))
		   (< m n)))
   :hints (("Goal" :use (:instance four
				   (i (- n m))))))
 )

(encapsulate ()

 (local
  (defun ind-hint (i)
    (cond ((zip i)
	   t)
	  ((< 0 i)
	   (ind-hint (+ -1 i)))
	  (t
	   (ind-hint (+ 1 i))))))

 (local
  (defthm five
    (implies (and (real/rationalp x)
		  (not (equal x -1))
		  (not (equal x 0))
		  (not (equal x 1))
		  (integerp m)
		  (integerp i))
	     (equal (equal (expt x m) (expt x (+ m i)))
		    (equal i 0)))
    :hints (("Goal" :induct (ind-hint i)))))

 (defthm |(equal (expt x m) (expt x n))|
   (implies (and (real/rationalp x)
		 (not (equal x -1))
		 (not (equal x 0))
		 (not (equal x 1))
		 (integerp m)
		 (integerp n))
	    (equal (equal (expt x m) (expt x n))
		   (equal m n)))
   :hints (("Goal" :use (:instance five
				   (i (- n m))))))
)

(encapsulate ()

 (local
  (defun ind-hintx (i)
    (cond ((zp i)
	   t)
	  (t
	   (ind-hintx (+ -1 i))))))

 (local
  (defthm sixa
    (IMPLIES (AND (REAL/RATIONALP X)
		  (< 1 X)
		  (real/rationalp b)
		  (< 0 b))
	     (< b
		(* x b)))))

 (local
  (defthm sixb
    (IMPLIES (AND (REAL/RATIONALP X)
		  (<= 1 X)
		  (real/rationalp b)
		  (< 0 b))
	     (<= b
		(* x b)))))

 (local
  (defthm six
    (implies (and (real/rationalp x)
		(< 1 x)
                (integerp m)
		(<= 0 m)
		(integerp i)
                (< 0 i)
		(real/rationalp y)
		(< (+ y 1) x))
	   (< (+ y (expt x m)) (expt x (+ m i))))
    :hints (("Goal" :induct (ind-hintx i)
	            :do-not '(generalize))
	    ("Subgoal *1/2.2'''" :use (:instance sixb
						 (b (- x 1))
						 (x (EXPT X M))))
	    ("Subgoal *1/2.1" :use (:instance sixa
					      (b (* (/ X) (EXPT X I) (EXPT X M)))
					      (x x))
	                      :in-theory (disable <-*-X-Y-Y)))))

 (defthm expt-exceeds-another-by-more-than-y
   (implies (and (real/rationalp x)
		 (< 1 x)
		 (integerp m)
		 (integerp n)
		 (<= 0 m)
		 (<= 0 n)
		 (< m n)
		 (real/rationalp y)
		 (< (+ y 1) x))
	    (< (+ y (expt x m)) (expt x n)))
   :hints (("Goal" :use (:instance six
				   (y y)
				   (x x)
				   (m m)
				   (i (- n m))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(encapsulate
 ()

 (local
  (defthm helper-www
    (implies (and (integerp n)
		  (< 0 n)
		  (real/rationalp x)
		  (< 1 x))
	     (<= x (expt x n)))))

 (local
  (in-theory (disable helper-www)))

 (local
  (defthm helper-qqq
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< 0 z))
	     (equal (<= x (* y z))
		    (<= (/ x z) y)))
    :hints (("Goal" :in-theory (enable prefer-*-to-/)))))

 (defthm expt-linear-helper-a
   (implies (and (< d n)
		 (integerp d)
		 (real/rationalp c)
		 (< 1 c)
		 (integerp n))
	    (<= (expt c (+ 1 d)) (expt c n)))
   :hints (("Subgoal *1/8" :use (:instance helper-www
					   (x c)
					   (n (- n d))))))

 (defthm expt-linear-helper-b
   (implies (and (< n d)
		 (integerp d)
		 (real/rationalp c)
		 (< 1 c)
		 (integerp n))
	    (<= (expt c n) (expt c (+ -1 d))))
   :hints (("Goal" :use (:instance expt-linear-helper-a
				   (d (+ -1 n))
				   (n (+ -1 d)))
	    :in-theory (enable prefer-*-to-/))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (local
  (defthm even-is-even
    (implies (and (evenp x)
		  (evenp y))
	     (not (equal x (+ 1 y))))
    :rule-classes nil))

 (local
  (defthm expt-even
    (implies (and (integerp n)
		  (< 0 n))
	     (evenp (expt 2 n)))))

 (local
  (defthm expt-2-n-is-even-helper
    (implies (and (integerp n)
		  (< 0 n)
		  (integerp m)
		  (< 0 m))
	     (not (equal (expt 2 n)
			 (+ 1 (expt 2 m)))))
    :hints (("Goal" :use (:instance even-is-even
				    (x (expt 2 n))
				    (y (expt 2 m)))
	     :in-theory (disable evenp)))))

 (defthm expt-2-n-is-even
   (implies (and (integerp n)
		 (integerp m))
	    (equal (equal (expt 2 n)
			  (+ 1 (expt 2 m)))
		   (and (equal n 1)
			(equal m 0))))
   :hints (("Subgoal *1/3" :cases ((< m 0)
				   (< 0 m)))))
 )
