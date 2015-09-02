; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; simplify-helper.lisp
;;
;;
;; Nothing in this book is directly available to the user.
;; It is an irritating little book whose only purpose is to
;; allow one to prove a couple of theorems about multiplying
;; (or dividing) both sides of an inequality by a rational
;; number.  Previously one had to know that the other terms
;; of the inequality were rational also.  See cancel-terms or
;; basic-arithmetic for examples of its use.
;;
;; Why, oh why, are complex numbers linearly ordered?
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm hack0
   (implies (and (real/rationalp x)
		 (real/rationalp y)
		 (real/rationalp z))
	    (equal (* z (complex x y))
		   (complex (* x z) (* y z))))
   :hints (("Goal" :use ((:instance complex-definition)
			 (:instance complex-definition
				    (x (* x z))
				    (y (* y z)))))
	   ("Goal'4'" :use ((:instance distributivity
				       (x z)
				       (y x)
				       (z (* #c(0 1) y))))))))

(local
 (defthm hack1
   (implies (and (real/rationalp x)
		 (real/rationalp y))
	    (equal (real/rationalp (complex x y))
		   (equal y 0)))))

(local
 (in-theory (enable rewrite-linear-equalities-to-iff)))



(local
 (defthm step-one
   (implies (and (real/rationalp a)
		 (not (equal a 0)))
	    (equal (< x y)
		   (cond ((< a 0)
			    (< (* a y) (* a x)))
			 ((< 0 a)
			    (< (* a x) (* a y))))))
   :hints (("Goal" :use completion-of-<)

	   ("Subgoal 6.4.1'" :use ((:instance completion-of-<
					     (x (complex (* a r) (* a s)))
					     (y 0))))
	   ("Subgoal 6.3'''" :use ((:instance completion-of-<
					     (x 0)
					     (y (complex (* a r) (* a s))))))
           ("Subgoal 6.2'4'" :use ((:instance completion-of-<
					       (x 0)
					       (y (complex 0 (* a r))))))
           ("Subgoal 6.1.1'" :use ((:instance completion-of-<
                                              (x (complex 0 (* a r)))
                                              (y 0))))
           ("Subgoal 5.4.1'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 5.3'''" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y 0))))
           ("Subgoal 5.2'4'" :use ((:instance completion-of-<
                                              (x (complex 0 (* a r)))
					      (y 0))))
           ("Subgoal 5.1.1'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex 0 (* a r))))))
           ("Subgoal 4.4.1'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 4.3'''" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y 0))))
           ("Subgoal 4.2'4'" :use ((:instance completion-of-<
                                              (x (complex 0 (* a r)))
					      (y 0))))
           ("Subgoal 4.1.1'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex 0 (* a r))))))
           ("Subgoal 3.4.1'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y 0))))
           ("Subgoal 3.3'''" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 3.2'4'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex 0 (* a r))))))
           ("Subgoal 3.1.1'" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (complex 0 (* a r))))))
           ("Subgoal 2.4'5'" :use ((:instance completion-of-<
                                              (x (complex (* a i) (* a j)))
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 2.3'5'" :use ((:instance completion-of-<
                                              (x (complex (* a i) (* a j)))
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 2.2'6'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y (complex (* a r) (* a i))))))
           ("Subgoal 2.1'6'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y (complex (* a r) (* a i))))))
           ("Subgoal 1.4'5'" :use ((:instance completion-of-<
                                              (x (complex (* a i) (* a j)))
                                              (y (complex (* a r) (* a s))))))
           ("Subgoal 1.3'5'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y (complex (* a i) (* a j))))))
           ("Subgoal 1.2'6'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a s)))
                                              (y (complex (* a r) (* a i))))))
           ("Subgoal 1.1'6'" :use ((:instance completion-of-<
                                              (x (complex (* a r) (* a i)))
                                              (y (complex (* a r) (* a s)))))))))

(local
 (in-theory (disable hack0 hack1 step-one)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here are the lemmas which we export.

(defthm helper-0
  (implies (not (equal (fix a) 0))
	   (equal (equal (* a x)
			 (* y a))
		  (equal (fix x)
			 (fix y)))))

(defthm helper-1
  (implies (not (equal (fix a) 0))
	   (equal (equal (* x a)
			 (* y z a))
		  (equal (fix x)
			 (* y z)))))

(defthm helper-2
  (implies (not (equal (fix a) 0))
	   (equal (equal (* w x a)
			 (* y z a))
		  (equal (* w x)
			 (* y z)))))

(defthm helper-3
  (implies (not (equal (fix a) 0))
	   (equal (equal (+ (* w a)
			    (* x a))
			 (+ (* y a)
			    (* z a)))
		  (equal (+ x w)
			 (+ z y))))
  :hints (("Goal" :use (:instance helper-0
				  (x (+ w x))
				  (y (+ y z))))))

(defthm helper-4
  (implies (not (equal (fix a) 0))
	   (equal (equal (+ (* x a)
			    (* y a))
			 (* z a))
		  (equal (+ x y)
			 (fix z))))
  :hints (("Goal" :use (:instance helper-0
				  (x (+ x y))
				  (y z)))))

(defthm helper-5
  (implies (not (equal (fix a) 0))
	   (equal (equal (+ (* w a)
			    (* x a))
			 (* y z a))
		  (equal (+ w x)
			 (* y z))))
  :hints (("Goal" :use (:instance helper-0
				  (x (+ w x))
				  (y (* y z))))))

(defthm helper-6
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (* a x)
		     (* b x))
		  (if (< 0 x)
		      (< a b)
		      (< b a))))
  :hints (("Goal" :use (:instance step-one
				  (x (* a x))
				  (y (* b x))
				  (a (/ x))))))

(defthm helper-6a
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (* x a)
		     (* x b))
		  (if (< 0 x)
		      (< a b)
		      (< b a)))))

(defthm helper-7
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (+ (* a x)
			(* b x))
		     (* c x))
		  (if (< 0 x)
		      (< (+ a b) c)
		      (< c (+ a b)))))
  :hints (("Goal" :use (:instance step-one
				  (x (+ (* a x)
					(* b x)))
				  (y (* c x))
				  (a (/ x))))))

(defthm helper-8
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (* c x)
		     (+ (* a x)
			(* b x)))
		  (if (< 0 x)
		      (< c (+ a b))
		      (< (+ a b) c))))
  :hints (("Goal" :use (:instance step-one
				  (x (* c x))
				  (y (+ (* a x)
					(* b x)))
				  (a (/ x))))))

(defthm helper-9
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (* a x)
		     (* b c x))
		  (if (< 0 x)
		      (< a (* b c))
		      (< (* b c) a))))
  :hints (("Goal" :use (:instance step-one
				  (x (* a x))
				  (y (* b c x))
				  (a (/ x))))))

(defthm helper-10
  (implies (and (real/rationalp x)
		(not (equal x 0)))
	   (equal (< (* a b x)
		     (* c x))
		  (if (< 0 x)
		      (< (* a b) c)
		      (< c (* a b)))))
  :hints (("Goal" :use (:instance step-one
				  (x (* a b x))
				  (y (* c x))
				  ( a (/ x))))))

(defthm helper-11
    (implies (and (<= 0 x)
                  (<= y 0)
                  (acl2-numberp x)
                  (real/rationalp y))
             (<= (* x y) 0))
  :hints (("Goal" :use (:instance step-one
				  (x (* x y))
				  (y 0)
				  ( a (/ y))))))

(defthm helper-12
    (implies (and (< x 0)
                  (< y 0)
                  (acl2-numberp x)
                  (real/rationalp y))
             (< 0 (* x y)))
  :hints (("Goal" :use (:instance step-one
				  (x 0)
				  (y (* x y))
				  ( a (/ y))))))

(defthm helper-13
    (implies (and (<= 0 x)
                  (<= 0 y)
                  (acl2-numberp x)
                  (real/rationalp y))
             (<= 0 (* x y)))
  :hints (("Goal" :use (:instance step-one
				  (x 0)
				  (y (* x y))
				  ( a (/ y))))))

(defthm helper-14
    (implies (and (< x 0)
                  (< 0 y)
                  (acl2-numberp x)
                  (real/rationalp y))
             (< (* x y) 0))
  :hints (("Goal" :use (:instance step-one
				  (x (* x y))
				  (y 0)
				  ( a (/ y))))))

(defthm helper-15
    (implies (and (<= x 0)
                  (<= y 0)
                  (acl2-numberp x)
                  (real/rationalp y))
             (<= 0 (* x y)))
  :hints (("Goal" :use (:instance step-one
				  (x 0)
				  (y (* x y))
				  ( a (/ y))))))

(defthm helper-16
    (implies (and (< 0 x)
                  (< y 0)
                  (acl2-numberp x)
                  (real/rationalp y))
             (< (* x y) 0))
  :hints (("Goal" :use (:instance step-one
				  (x (* x y))
				  (y 0)
				  ( a (/ y))))))

(defthm helper-17
    (implies (and (<= x 0)
                  (<= 0 y)
                  (acl2-numberp x)
                  (real/rationalp y))
             (<= (* x y) 0))
  :hints (("Goal" :use (:instance step-one
				  (x (* x y))
				  (y 0)
				  ( a (/ y))))))

(defthm helper-18
    (implies (and (< 0 x)
                  (< 0 y)
                  (acl2-numberp x)
                  (real/rationalp y))
             (< 0 (* x y)))
  :hints (("Goal" :use (:instance step-one
				  (x 0)
				  (y (* x y))
				  ( a (/ y))))))

(defthm big-helper-1
  (IMPLIES (AND (EQUAL X (* Y Z))
              (REAL/RATIONALP z)
              (ACL2-NUMBERP y))
         (EQUAL (< X 0)
                (AND (NOT (EQUAL Y 0))
                     (NOT (EQUAL Z 0))
                     (COND ((< 0 Y) (< Z 0))
                           ((< Y 0) (< 0 Z))
                           (T NIL))))))

(encapsulate
 ()

(local
 (in-theory (enable hack0 hack1)))

 (local
  (defthm hack2
    (implies (and (acl2-numberp x)
		  (real/rationalp y))
	     (and (equal (realpart (* x y))
			 (* y (realpart x)))
		  (equal (imagpart (* x y))
			 (* y (imagpart x)))))))

 (local
  (defthm hack3
    (implies (and (acl2-numberp x)
		  (real/rationalp y)
		  (not (equal y 0)))
	     (equal (real/rationalp (* x y))
		    (equal (imagpart x) 0)))
    :hints (("Goal" :cases ((real/rationalp x)
			    (complex/complex-rationalp x))))))

 (local
  (defthm foo-1
    (implies (and (acl2-numberp x)
		  (< 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0)))
	    ("Subgoal 1" :cases ((equal x 0)
				 (equal y 0))))
    :otf-flg t))

 (local
  (defthm foo-2
    (implies (and (acl2-numberp x)
		  (< 0 x)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x y) (* x z)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-3
    (implies (and (acl2-numberp x)
		  (< x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (< y z))
	     (< (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x z))
				     (y (* x y)))
			  (:instance completion-of-<
				     (x x)
				     (y 0))))
	    ("Subgoal 1" :cases ((equal x 0)
				 (equal y 0))))))

 (local
  (defthm foo-4
    (implies (and (acl2-numberp x)
		  (< x 0)
		  (real/rationalp y)
		  (real/rationalp z)
		  (<= y z))
	     (<= (* x z) (* x y)))
    :hints (("Goal" :use ((:instance completion-of-<
				     (x (* x y))
				     (y (* x z)))
			  (:instance completion-of-<
				     (x 0)
				     (y x))))
	    ("Subgoal 4" :cases ((equal x 0)
				 (equal y 0))))))

 (defthm big-helper-2
  (implies (and (real/rationalp lhs)
		(real/rationalp rhs)
		(acl2-numberp c)
		(not (equal c 0)))
	   (equal (< lhs rhs)
		  (if (< 0 c)
		      (< (* c lhs) (* c rhs))
		    (< (* c rhs) (* c lhs))))))

 )

(in-theory (disable big-helper-2))

#|
(defthm helper-9
  (implies (and (rationalp x)
		(not (equal x 0)))
	   (equal (< (* a b x)
		     (* c d x))
		  (if (< 0 x)
		      (< (* a b) (* c d))
		      (< (* c d) (* a b)))))
  :hints (("Goal" :use (:instance step-one
				  (x (* a b x))
				  (y (* c d x))
				  (a (/ x))))))
|#