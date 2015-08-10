; See the top-level arithmetic-2 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; cancel-terms-helper.lisp
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
 (include-book "../pass1/top"))

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
	   ("Subgoal 6.4'''" :use ((:instance completion-of-<
                                              (x (COMPLEX (* A R) (* A S)))
                                              (y 0))))
	   ("Subgoal 6.3'''" :use ((:instance completion-of-<
					     (x 0)
					     (y (COMPLEX (* A R) (* A S))))))
	   ("Subgoal 6.2'4'" :use ((:instance completion-of-<
					      (x (COMPLEX 0 (* A R)))
					      (y 0))))
	   ("Subgoal 6.1'4'" :use ((:instance completion-of-<
					       (x (COMPLEX 0 (* A R)))
					       (y 0))))
	   ("Subgoal 5.4'''" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (COMPLEX (* A R) (* A S))))))
	   ("Subgoal 5.3'''" :use ((:instance completion-of-<
					     (x 0)
					     (y (COMPLEX (* A R) (* A S))))))
	   ("Subgoal 5.2'4'" :use ((:instance completion-of-<
					      (x 0)
					      (y (COMPLEX 0 (* A R))))))
	   ("Subgoal 5.1'4'" :use ((:instance completion-of-<
					       (x 0)
					       (y (COMPLEX 0 (* A R))))))
	   ("Subgoal 4.4'''" :use ((:instance completion-of-<
                                              (x 0)
                                              (y (COMPLEX (* A R) (* A S))))))
	   ("Subgoal 4.3'''" :use ((:instance completion-of-<
					     (x 0)
					     (y (COMPLEX (* A R) (* A S))))))
	   ("Subgoal 4.2'4'" :use ((:instance completion-of-<
					      (x 0)
					      (y (COMPLEX 0 (* A R))))))
	   ("Subgoal 4.1'4'" :use ((:instance completion-of-<
					      (x 0)
					      (y (COMPLEX 0 (* A R))))))
	   ("Subgoal 3.4'''" :use ((:instance completion-of-<
                                              (x (COMPLEX (* A R) (* A S)))
                                              (y 0))))
	   ("Subgoal 3.3'''" :use ((:instance completion-of-<
					     (x (COMPLEX (* A R) (* A S)))
					     (y 0))))
	   ("Subgoal 3.2'4'" :use ((:instance completion-of-<
					      (x (COMPLEX 0 (* A R)))
					      (y 0))))
	   ("Subgoal 3.1'4'" :use ((:instance completion-of-<
					       (x (COMPLEX 0 (* A R)))
					       (y 0))))

           ("Subgoal 2.4'5'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A S)))
                                              (y (COMPLEX (* A I) (* A J))))))
           ("Subgoal 2.3'5'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A S)))
                                              (y (COMPLEX (* A I) (* A J))))))
           ("Subgoal 2.2'6'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A S)))
                                              (y (COMPLEX (* A R) (* A I))))))
           ("Subgoal 2.1'6'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A S)))
                                              (y (COMPLEX (* A R) (* A I))))))

           ("Subgoal 1.4'5'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A I) (* A J)))
                                              (y (COMPLEX (* A R) (* A S))))))
           ("Subgoal 1.3'5'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A I) (* A J)))
                                              (y (COMPLEX (* A R) (* A S))))))
           ("Subgoal 1.2'6'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A I)))
                                              (y (COMPLEX (* A R) (* A S))))))
           ("Subgoal 1.1'6'" :use ((:instance completion-of-<
					      (x (COMPLEX (* A R) (* A I)))
                                              (y (COMPLEX (* A R) (* A S)))))))))




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
  (implies (real/rationalp x)
           (equal (< 0 (* x y))
                  (cond ((< x 0)
                         (< y 0))
                        ((< 0 x)
                         (< 0 y))
                        (t
                         nil))))
  :hints (("Goal" :use ((:instance step-one
                                   (a (/ x))
                                   (x 0)
                                   (y (* x y)))))))

(defthm helper-12
  (implies (real/rationalp y)
           (equal (< 0 (* x y))
                  (cond ((< x 0)
                         (< y 0))
                        ((< 0 x)
                         (< 0 y))
                        (t
                         nil))))
  :hints (("Goal" :use ((:instance step-one
                                   (a (/ y))
                                   (x 0)
                                   (y (* x y)))))))

(defthm helper-13
  (implies (real/rationalp x)
           (equal (< (* x y) 0)
                  (cond ((< x 0)
                         (< 0 y))
                        ((< 0 x)
                         (< y 0))
                        (t
                         nil))))
  :hints (("Goal" :use ((:instance step-one
                                   (a (/ x))
                                   (x (* x y))
                                   (y 0))))))

(defthm helper-14
  (implies (real/rationalp y)
           (equal (< (* x y) 0)
                  (cond ((< x 0)
                         (< 0 y))
                        ((< 0 x)
                         (< y 0))
                        (t
                         nil))))
  :hints (("Goal" :use ((:instance step-one
                                   (a (/ y))
                                   (x (* x y))
                                   (y 0))))))

#|
(defthm helper-9
  (implies (and (real/rationalp x)
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
