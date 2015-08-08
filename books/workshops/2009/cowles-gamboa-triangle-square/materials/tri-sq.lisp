#| To certify:

(certify-book "tri-sq")
|#

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Make temporary use of an ACL2 Arithmetic Book to help certify this book,

(local (include-book "arithmetic-3/top" :dir :system))

(defun
 triangle (n)
 "Return the sum of the
  first n positive integers."
 (if (and (integerp n)
	   (> n 1))
     (+ n (triangle (- n 1)))
     1))

(defthm
 triangle-equality
 (implies (posp n)
	   (equal (triangle n)
		  (/ (* n (+ n 1))
		     2))))

;;========================
;; Reformulate the Problem.

;; These first three lemmas show how to transform the original problem into
;; one that has been studied for a long time and has a well understood solution

(defthm
 Lemma-1
 (implies (and (posp n)
		(posp k)
		(equal (* n (+ n 1))
		       (* 2 k k)))
	   (let ((x (+ (* 2 n) 1))
		 (y (* 2 k)))
	     (and (equal (- (* x x)
			    (* 2 y y))
			 1)
		  (>= x 3)
		  (oddp x)
		  (>= y 2)
		  (evenp y)))))

;;==========Lemma 2==========

(encapsulate  ;; Create local theory to aid
()           ;; in proof of Lemma 2

(local
 (defthm
   Lemma-2-a
   (implies (and (integerp x)
		  (evenp x))
	     (evenp (* x x)))))

(local
 (defthm
   Lemma-2-b
   (implies (and (integerp x)
		  (integerp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (oddp x))
   :hints (("Goal"
	     :use Lemma-2-a))))

(local
 (defthm
   Lemma-2-c
   (implies (and (integerp x)
		  (oddp x))
	     (equal (* x x) (+ (* 4 (floor x 2)(floor x 2))
			       (* 4 (floor x 2))
			       1)))))

(local
 (defthm
   Lemma-2-d
   (implies (and (integerp x)
		  (oddp x))
	     (oddp (* x x)))))

 (local
  (in-theory (disable Lemma-2-c)))

 (local
  (defthm
    Lemma-2-e
    (implies (and (evenp x)
		   (evenp y))
	      (evenp (* 1/2 x y)))
    :hints (("Goal"
	      :use (:instance
		    (:theorem
		     (implies (and (integerp i)
				   (integerp j))
			      (integerp (* i j))))
		    (i (* 1/2 x))
		    (j (* 1/2 y)))))))

 (local
  (defthm
    Lemma-2-f
    (implies (and (integerp x)
		   (oddp x))
	      (evenp (* 1/2 (+ -1 x)(+ 1 x))))
    :hints (("Goal"
	      ;;:in-theory (disable Lemma-2-e)
	      :use (:instance
		    Lemma-2-e
		    (x (- x 1))
		    (y (+ 1 x)))))))

 (local
  (defthm
    Lemma-2-g
    (implies (and (integerp x)
		   (integerp y)
		   (equal (- (* x x)
			     (* 2 y y))
			  1))
	      (evenp (* y y)))
    :hints (("Goal"
	      :use Lemma-2-f))))

 (local
  (defthm
    Lemma-2-h
    (implies (and (integerp x)
		   (integerp y)
		   (equal (- (* x x)
			     (* 2 y y))
			  1))
	      (evenp y))
    :hints (("Goal"
	      :use ((:instance
		     Lemma-2-d
		     (x y))
		    Lemma-2-g)))))

 (local
  (defthm
    Lemma-2-i
    (implies (and (integerp x)
		   (posp y)
		   (equal (- (* x x)
			     (* 2 y y))
			  1))
	      (>= y 2))
    :hints (("Goal"
	      :use Lemma-2-h))))

 (local
  (defthm
    Lemma-2-j
    (implies (and (integerp y)
		   (>= y 2))
	      (>= (+ 1 (* 2 y y))
		  9))
    :hints (("Goal"
	      :use (:theorem
		    (implies (and (integerp y)
				  (>= y 2))
			     (>= (* y y)
				 4)))))))

 (local
  (defthm
    Lemma-2-k
    (implies (and (integerp x)
		   (posp y)
		   (equal (- (* x x)
			     (* 2 y y))
			  1))
	      (>= (* x x)
		  9))
    :hints (("Goal"
	      :use Lemma-2-j))))

 (local
  (defthm
    Lemma-2-l
    (implies (and (posp a)
		   (< x y))
	      (< (* a x)(* a y)))))

 (local
  (defthm
    Lemma-2-m
    (implies (and (posp x)
		   (< x 3))
	      (< (* x x) 9))
    :hints (("Goal"
	      :use ((:instance
		     Lemma-2-l
		     (a x)
		     (y 3))
		    (:instance
		     Lemma-2-l
		     (a 3)
		     (y 3))
		    (:instance
		     (:theorem
		      (implies (and (< x y)
				    (< y z))
			       (< x z)))
		     (x (* x x))
		     (y (* 3 x))
		     (z 9)))))))

 (local
  (defthm
    Lemma-2-n
    (implies (and (posp x)
		   (posp y)
		   (equal (- (* x x)
			     (* 2 y y))
			  1))
	      (>= x 3))
    :hints (("Goal"
	      :use (Lemma-2-k
		    Lemma-2-m)))))

 (defthm
   Lemma-2
   (implies (and (posp x)
		  (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (and (oddp x)
		  (>= x 3)
		  (evenp y)
		  (>= y 2)))
   :hints (("Goal"
	     :use Lemma-2-h)))
 ) ;;end encapsulate

;;=====Lemma 3=================

(defthm
 Lemma-3
 (implies (and (posp x)
		(posp y)
		(equal (- (* x x)
			  (* 2 y y))
		       1))
	   (let ((n (/ (- x 1) 2))
		 (k (/ y 2)))
	     (and (posp n)
		  (posp k)
		  (equal (* n (+ n 1))
			 (* 2 k k)))))
 :hints (("Goal"
	   :in-theory (disable Lemma-2)
	   :use Lemma-2)))

;;=================================================
;; For squarefree positive integers D, the equation

;;            x^2 - D * y^2 = 1

;; is usually called Pell's equation. However, John Pell (1610--1685),
;; an English Mathematician, made no contribution to the study of this equation

;; The obvious solution, n = 1, k = 1, to our original problem corresponds
;; to the solution, x = 3, y = 2, of the Pell equation
;;             x^2 - 2 * y^2 = 1.

;;========================
;; Generate Many Solutions

;; This lemma shows how to construct new solutions to our particular Pell equation
;; from known solutions. Once more the proof depends only on elementary algebra.

;;======Lemma 4===================

(defthm
 Lemma-4
 (implies (and (posp a)
		(posp b)
		(posp c)
		(posp d)
		(equal (- (* a a)
			  (* 2 b b))
		       1)
		(equal (- (* c c)
			  (* 2 d d))
		       1))
	   (let ((x (+ (* a c)
		       (* 2 b d)))
		 (y (+ (* a d)
		       (* b c))))
	     (and (posp x)
		  (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1)))))

;; In the above lemma, the two given solutions, a, b and c, d, need not be
;; distinct. That is, using a = c and b = d in the construction of x, y
;; yields a new solution.  Thus, starting with one known solution, a = 3, b = 2,
;; many other solutions can be generated:

;;====Definition 1=========

(defun
 pair-pow (n)
 (if (and (integerp n)
	   (> n 1))
     (let* ((pair (pair-pow (- n 1)))
	     (first (first pair))
	     (second (second pair)))
	(list (+ (* 3 first)
		 (* 4 second))
	      (+ (* 3 second)
		 (* 2 first))))
     (list 3 2)))

;;=====Examples====

(defthm
 Examples
 (and (equal (pair-pow 1)
	      '(3 2))
      (equal (pair-pow 2)
	      '(17 12))
      (equal (pair-pow 3)
	      '(99 70))
      (equal (pair-pow 4)
	      '(577 408))
      (equal (pair-pow 5)
	      '(3363 2378))
      (equal (pair-pow 6)
	      '(19601 13860))
      (equal (pair-pow 7)
	      '(114243 80782))
      (equal (pair-pow 8)
	      '(665857 470832))
      (equal (pair-pow 9)
	      '(3880899 2744210))))

;;=====Theorem 1======

;; This theorem is proved by mathematical induction on j,
;; using Lemma 4.

(defthm
 Theorem-1
 (let* ((pair (pair-pow j))
	 (xj (first pair))
	 (yj (second pair)))
   (equal (- (* xj xj)
	      (* 2 yj yj))
	   1)))

;;;;;;;;;;;;;;;;;;;;;
;; No Other Solutions

;; In fact, the solutions given by Definition 1 are all the
;; positive integer solutions:

;;=====Lemma 5======

;; This lemma constructs another new solution, ( a,b ), to our Pell equation
;; from a known solution, ( x,y ).  This time the new solution is ``smaller''
;; than the old solution in the sense that b < y. The proof only requires
;; elementary algebra.

(encapsulate  ;; Create local theory to aid
()           ;; in proof of Lemma 5

(local
 (defthm
   Lemma-5-a
   (implies (and (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* 16 y y)(* 9 x x)))))

(local
 (defthm
   Lemma-5-b
   (implies (and (rationalp r)
		  (> r 0)
		  (>= s u))
	     (>= (* r s)(* r u)))))

(local
 (defthm
   Lemma-5-c
   (implies (and (posp i)
		  (posp j)
		  (>= i j))
	     (>= (* i i)(* j j)))
   :hints (("Goal"
	     :use ((:instance
		    Lemma-5-b
		    (r i)
		    (s i)
		    (u j))
		   (:instance
		    Lemma-5-b
		    (r j)
		    (s i)
		    (u j))
		   (:instance
		    (:theorem
		     (implies (and (>= x y)
				   (>= y z))
			      (>= x z)))
		    (x (* i i))
		    (y (* i j))
		    (z (* j j))))))))

(local
 (defthm
   Lemma-5-d
   (implies (and (posp x)
		  (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* 4 y)(* 3 x)))
   :hints (("Goal"
	     :use (Lemma-5-a
		   (:instance
		    Lemma-5-c
		    (i (* 4 y))
		    (j (* 3 x))))))))

(local
 (defthm
   Lemma-5-e
   (implies (and (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* 4 y y)(* 4 x x)))))

(local
 (defthm
   Lemma-5-f
   (implies (and (posp x)
		  (posp y)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* 2 y)(* 2 x)))
   :hints (("Goal"
	     :use (Lemma-5-e
		   (:instance
		    Lemma-5-c
		    (i (* 2 y))
		    (j (* 2 x))))))))

(local
 (defthm
   Lemma-5-g
   (implies (and (rationalp r)
		  (> r 0)
		  (< s u))
	     (< (* r s)(* r u)))))

(local
 (defthm
   Lemma-5-h
   (implies (and (posp x)
		  (> y x))
	     (> (/ y x) 1))
   :hints (("Goal"
	     :use (:instance
		   Lemma-5-g
		   (r (/ x))
		   (s x)
		   (u y))))))

(local
 (defthm
   Lemma-5-i
   (implies (and (posp x)
		  (posp y)
		  (> y x))
	     (> (/ x)(/ y)))
   :hints (("Goal"
	     :use (Lemma-5-h
		   (:instance
		    Lemma-5-g
		    (r (/ y))
		    (s 1)
		    (u (/ y x))))))))

(local
 (defthm
   Lemma-5-j
   (implies (and (posp i)
		  (posp j)
		  (< i j))
	     (< (* i i)(* j j)))
   :hints (("Goal"
	     :use ((:instance
		    Lemma-5-g
		    (r i)
		    (s i)
		    (u j))
		   (:instance
		    Lemma-5-g
		    (r j)
		    (s i)
		    (u j))
		   (:instance
		    (:theorem
		     (implies (and (< x y)
				   (< y z))
			      (< x z)))
		    (x (* i i))
		    (y (* i j))
		    (z (* j j))))))))

(local
 (defthm
   Lemma-5-k
   (implies (and (posp x)
		  (posp y)
		  (> y x))
	     (> (/ (* x x))(/ (* y y))))
   :hints (("Goal"
	     :use (:instance
		   Lemma-5-j
		   (i x)
		   (j y))))))

(local
 (defthm
   Lemma-5-l
   (implies (and (integerp y)
		  (> y 2))
	     (< (+ 2 (/ (* y y)))
		9/4))
   :hints (("Goal"
	     :use (:instance
		   Lemma-5-k
		   (x 2))))))

(local
 (defthm
   Lemma-5-m
   (implies (and (integerp y)
		  (> y 2)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* (/ x y)(/ x y))
		9/4))
   :hints (("Goal"
	     :use Lemma-5-l))))

(local
 (defthm
   Lemma-5-n
   (implies (and (rationalp r)
		  (rationalp s)
		  (> s 0)
		  (>= r s))
	     (>= (* r r)(* s s)))
   :hints (("Goal"
	     :use ((:instance
		    Lemma-5-b
		    (r s)
		    (s r)
		    (u s))
		   (:instance
		    Lemma-5-b
		    (s r)
		    (u s))
		   (:instance
		    (:theorem
		     (implies (and (<= x y)
				   (<= y z))
			      (<= x z)))
		    (x (* s s))
		    (y (* r s))
		    (z (* r r))))))))

(local
 (defthm
   Lemma-5-o
   (implies (and (posp x)
		  (integerp y)
		  (> y 2)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (/ x y) 3/2))
   :hints (("Goal"
	     :use (Lemma-5-m
		   (:instance
		    Lemma-5-n
		    (r (/ x y))
		    (s 3/2)))))))

(local
 (defthm
   Lemma-5-p
   (implies (and (posp x)
		  (integerp y)
		  (> y 2)
		  (equal (- (* x x)
			    (* 2 y y))
			 1))
	     (< (* 2 x)(* 3 y)))
   :hints (("Goal"
	     :use ((:instance
		    Lemma-5-g
		    (r 2)
		    (s (/ x y))
		    (u 3/2))
		   (:instance
		    Lemma-5-g
		    (r y)
		    (s (* 2 x (/ y)))
		    (u 3)))))))

(defthm
  Lemma-5
  (implies (and (posp x)
		 (posp y)
		 (> y 2)
		 (equal (- (* x x)
			   (* 2 y y))
			1))
	    (let ((a (- (* 3 x)
			(* 4 y)))
		  (b (+ (* -2 x)
			(* 3 y))))
	      (and (posp a)
		   (posp b)
		   (< b y)
		   (equal (- (* a a)
			     (* 2 b b))
			  1)))))
) ;;end encapsulate

;;======Theorem 2===============

;; The proof of this next theorem is most interesting, both mathematically and
;; as a formalization challenge in ACL2.

(defun
 pfix (x)
 (if (posp x)
     x
     1))

(defun
 sqrt-loop (n r)
 (declare (xargs :measure (let ((n (pfix n))
				 (r (pfix r)))
			     (if (> r n)
				 0
			         (- n r)))))
 (let ((n (pfix n))
	(r (pfix r)))
   (if (> (* (+ r 1)(+ r 1))
	   n)
	r
       (sqrt-loop n (+ r 1)))))

(defthm
 sqrt-loop-<=
 (implies (and (posp r)
		(<= (* r r)
		    n))
	   (<= (* (sqrt-loop n r)
		  (sqrt-loop n r))
	       n))
 :rule-classes nil)

(defthm
 sqrt-loop->
 (implies (posp n)
	   (< n
	      (* (+ 1 (sqrt-loop n r))
		 (+ 1 (sqrt-loop n r)))))
 :rule-classes nil)

(encapsulate  ;; Create local theory to aid in proof
()           ;;  of (sqrt-loop (* n n) r) = n.

(local
 (defthm
   Theorem-2-a
   (implies (and (rationalp a)
		  (> a 0)
		  (> b c))
	     (> (* a b)(* a c)))))

(local
 (defthm
   Theorem-2-b
   (implies (and (integerp s)
		  (posp n)
		  (> s n))
	     (> (* s s)(* n n)))
   :hints (("Goal"
	     :use ((:instance
		    Theorem-2-a
		    (a s)
		    (b s)
		    (c n))
		   (:instance
		    Theorem-2-a
		    (a n)
		    (b s)
		    (c n))
		   (:instance
		    (:theorem
		     (implies (and (> x y)
				   (> y z))
			      (> x z)))
		    (x (* s s))
		    (y (* n s))
		    (z (* n n))))))))

(local
 (defthm
   Theorem-2-c
   (implies (and (posp s)
		  (posp n)
		  (<= (* s s)(* n n)))
	     (<= s n))
   :hints (("Goal"
	     :use Theorem-2-b))))

(local
 (defthm
   Theorem-2-d
   (implies (and (rationalp a)
		  (> a 0)
		  (>= b c))
	     (>= (* a b)(* a c)))))

(local
 (defthm
   Theorem-2-e
   (implies (and (posp u)
		  (integerp n)
		  (>= n u))
	     (>= (* n n)(* u u)))
   :hints (("Goal"
	     :use ((:instance
		    Theorem-2-d
		    (a n)
		    (b n)
		    (c u))
		   (:instance
		    Theorem-2-d
		    (a u)
		    (b n)
		    (c u))
		   (:instance
		    (:theorem
		     (implies (and (>= x y)
				   (>= y z))
			      (>= x z)))
		    (x (* n n))
		    (y (* n u))
		    (z (* u u))))))))

(local
 (defthm
   Theorem-2-f
   (implies (and (posp u)
		  (posp n)
		  (< (* n n)(* u u)))
	     (< n u))
   :hints (("Goal"
	     :use Theorem-2-e))))

(local
 (defthm
   Theorem-2-g
   (implies (and (posp n)
		  (posp r)
		  (<= r n))
	     (and (<= (sqrt-loop (* n n) r) n)
		  (< n (+ (sqrt-loop (* n n) r) 1))))
   :hints (("Goal"
	     :use ((:instance
		    sqrt-loop-<=
		    (n (* n n)))
		   (:instance
		    sqrt-loop->
		    (n (* n n))))))))

(defthm
  sqrt-loop-sq
  (implies (and (posp n)
		 (posp r)
		 (<= r n))
	    (equal (sqrt-loop (* n n) r)
		   n))
  :hints (("Goal"
	    :use Theorem-2-g)))
) ;; end encapsulate

(defun
 sqrt-posp (n)
 (sqrt-loop n 1))

(defthm
sqrt-posp-<=
(implies (posp n)
	  (<= (* (sqrt-posp n)
		 (sqrt-posp n))
	      n))
:rule-classes (:linear
		:rewrite)
:hints (("Goal"
	  :use (:instance
		sqrt-loop-<=
		(r 1)))))

(defthm
 sqrt-posp->
 (implies (posp n)
	   (< n
	      (* (+ 1 (sqrt-posp n))
		 (+ 1 (sqrt-posp n)))))
 :rule-classes (:linear
		 :rewrite)
 :hints (("Goal"
	   :use (:instance
		 sqrt-loop->
		 (r 1)))))

(defthm
 sqrt-posp-sq
 (implies (posp n)
	   (equal (sqrt-posp (* n n))
		  n))
 :hints (("Goal"
	   :use (:instance
		 sqrt-loop-sq
		 (r 1)))))

(in-theory (disable (:DEFINITION sqrt-posp)))

(defthm
 sqrt-posp-expt-2
 (implies (posp n)
	   (equal (sqrt-posp (expt n 2))
		  n))
 :hints (("Goal"
	   :use sqrt-posp-sq)))

(defun-sk
 Exists-pair-pow-equal (x y)
 (exists j (and (posp j)
		 (equal (pair-pow j)
			(list x y)))))

(defun
 Find-smallest-y-loop (y r)
 (declare (xargs :measure (let ((y (pfix y))
				 (r (pfix r)))
			     (cond ((> r y) 0)
				   ((and (equal (* (sqrt-posp (+ (* 2 r r) 1))
						   (sqrt-posp (+ (* 2 r r) 1)))
						(+ (* 2 r r) 1))
					 (not (Exists-pair-pow-equal
					       (sqrt-posp (+ (* 2 r r) 1))
					       r)))
				    0)
				   (t (- (+ y 1) r))))))
 (let ((y (pfix y))
	(r (pfix r)))
   (cond ((> r y)
	   r)
	  ((and (equal (* (sqrt-posp (+ (* 2 r r) 1))
			  (sqrt-posp (+ (* 2 r r) 1)))
		       (+ (* 2 r r) 1))
		(not (Exists-pair-pow-equal (sqrt-posp (+ (* 2 r r) 1))
					    r)))
	   r)
	  (t (Find-smallest-y-loop y (+ r 1))))))

(defthm
 Find-smallest-y-loop-equal
 (implies (and (integerp y)
		(<= (Find-smallest-y-loop y r) y))
	   (let* ((b (Find-smallest-y-loop y r))
		  (a (sqrt-posp (+ (* 2 b b) 1))))
	     (equal (* a a)
		    (+ (* 2 b b) 1))))
 :rule-classes nil)

(defthm
 Find-smallest-y-loop-not-exists
 (implies (and (integerp y)
		(<= (Find-smallest-y-loop y r) y))
	   (let* ((b (Find-smallest-y-loop y r))
		  (a (sqrt-posp (+ (* 2 b b) 1))))
	     (not (Exists-pair-pow-equal a b))))
 :rule-classes nil)

(defthm
 Find-smallest-y-loop-finds-smallest
 (implies (and (posp r)
		(integerp b)
		(<= r b)
		(< b (Find-smallest-y-loop y r)))
	   (let ((a (sqrt-posp (+ (* 2 b b) 1))))
	     (or (not (equal (* a a)
			     (+ (* 2 b b) 1)))
		 (Exists-pair-pow-equal a b))))
 :rule-classes nil)

(defthm
 Find-smallest-y-loop-<=
 (implies (and (posp x)
		(integerp y)
		(posp r)
		(<= r y)
		(equal (* x x)
		       (+ (* 2 y y) 1))
		(not (Exists-pair-pow-equal x y)))
	   (<= (Find-smallest-y-loop y r) y))
 :rule-classes nil)

(defun
 Find-smallest-y (y)
 (Find-smallest-y-loop y 1))

(defthm
 Find-smallest-y-equal
 (implies (and (integerp y)
		(<= (Find-smallest-y y) y))
	   (let* ((b (Find-smallest-y y))
		  (a (sqrt-posp (+ (* 2 b b) 1))))
	     (equal (* a a)
		    (+ (* 2 b b) 1))))
 :hints (("Goal"
	   :use (:instance
		 Find-smallest-y-loop-equal
		 (r 1)))))

(defthm
 Find-smallest-y-not-exists
 (implies (and (integerp y)
		(<= (Find-smallest-y y) y))
	   (let* ((b (Find-smallest-y y))
		  (a (sqrt-posp (+ (* 2 b b) 1))))
	     (not (Exists-pair-pow-equal a b))))
 :hints (("Goal"
	   :use (:instance
		 Find-smallest-y-loop-not-exists
		 (r 1)))))

(defthm
 Find-smallest-y-finds-smallest
 (implies (and (posp b)
		(< b (Find-smallest-y y))
		(let ((a (sqrt-posp (+ (* 2 b b) 1))))
		  (equal (* a a)
			 (+ (* 2 b b) 1))))
	   (Exists-pair-pow-equal (sqrt-posp (+ (* 2 b b) 1))
				  b))
 :hints (("Goal"
	   :use (:instance
		 Find-smallest-y-loop-finds-smallest
		 (r 1)))))

(defthm
 Find-smallest-y-<=
 (implies (and (equal (* x x)
		       (+ (* 2 y y) 1))
		(posp x)
		(posp y)
		(not (Exists-pair-pow-equal x y)))
	   (<= (Find-smallest-y y) y))
 :rule-classes (:rewrite
		 :linear)
 :hints (("Goal"
	   :use (:instance
		 Find-smallest-y-loop-<=
		 (r 1)))))

(in-theory (disable (:definition Find-smallest-y)))

(defthm
 Equal-sqrt-posp-*-sqrt-posp
 (implies (and (equal (* x x) n)
		(posp n)
		(posp x))
	   (equal (* (sqrt-posp n)
		     (sqrt-posp n))
		  n)))

(defthm
 y=1-not-equal
 (implies (and (posp x)
		(equal y 1))
	   (not (equal (* x x)
		       (+ (* 2 y y) 1))))
 :rule-classes nil
 :hints (("Goal"
	   :use (:instance
		 Equal-sqrt-posp-*-sqrt-posp
		 (n 3)))))

(defthm
 x-*-x=9-implies-x=3
 (implies (and (posp x)
		(equal (* x x) 9))
	   (equal x 3))
 :rule-classes nil
 :hints (("Goal"
	   :use ((:instance
		  sqrt-posp-sq
		  (n x))))))

(defthm
 Not-exists-y->-2
 (implies (and (posp x)
		(posp y)
		(equal (* x x)
		       (+ (* 2 y y) 1))
		(not (Exists-pair-pow-equal x y)))
	   (> y 2))
 :rule-classes nil
 :hints (("Goal"
	   :in-theory (disable Exists-pair-pow-equal)
	   :use (y=1-not-equal
		 x-*-x=9-implies-x=3
		 (:instance
		  Exists-pair-pow-equal-suff
		  (j 1)
		  (x 3)
		  (Y 2))))))

(defthm
 Find-smallest-y->-2
 (implies (and (equal (* x x)
		       (+ (* 2 y y) 1))
		(posp x)
		(posp y)
		(not (Exists-pair-pow-equal x y)))
	   (> (Find-smallest-y y) 2))
 :rule-classes (:linear
		 :rewrite)
 :hints (("Goal"
	   :use ((:instance
		  Not-exists-y->-2
		  (y (Find-smallest-y y))
		  (x (sqrt-posp (+ (* 2
				      (Find-smallest-y y)
				      (Find-smallest-y y))
				   1))))
		 Find-smallest-y-equal
		 Find-smallest-y-not-exists))))

(defthm
 Find-smallest-y-Lemma-5
 (implies (and (equal (* x x)
		       (+ (* 2 y y) 1))
		(posp x)
		(posp y)
		(not (Exists-pair-pow-equal x y)))
	   (let ((a (- (* 3 (sqrt-posp (+ (* 2
					     (Find-smallest-y y)
					     (Find-smallest-y y))
					  1)))
		       (* 4 (Find-smallest-y y))))
		 (b (+ (* -2 (sqrt-posp (+ (* 2
					      (Find-smallest-y y)
					      (Find-smallest-y y))
					   1)))
		       (* 3 (Find-smallest-y y)))))
	     (and (posp a)
		  (posp b)
		  (< b (Find-smallest-y y))
		  (equal (- (* a a)
			    (* 2 b b))
			 1))))
 :hints (("Goal"
	   :use ((:instance
		  Lemma-5
		  (y (Find-smallest-y y))
		  (x (sqrt-posp (+ (* 2
				      (Find-smallest-y y)
				      (Find-smallest-y y))
				   1))))
		 Find-smallest-y-equal))))

(encapsulate  ;; Create local theory to aid
()           ;; in proof of contradiction.

(local
 (defthm
   Theorem-2-aa
   (implies (and (posp a)
		  (posp b)
		  (equal (- (* a a)
			    (* 2 b b))
			 1))
	     (equal (sqrt-posp (+ (* 2 b b) 1))
		    a))
   :rule-classes nil))

(local
 (defthm
   Theorem-2-ab
   (implies (and (equal (* x x)
			 (+ (* 2 y y) 1))
		  (posp x)
		  (posp y)
		  (not (Exists-pair-pow-equal x y)))
	     (let ((a (- (* 3 (sqrt-posp (+ (* 2
					       (Find-smallest-y y)
					       (Find-smallest-y y))
					    1)))
			 (* 4 (Find-smallest-y y))))
		   (b (+ (* -2 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			 (* 3 (Find-smallest-y y)))))
	       (equal (sqrt-posp (+ (* 2 b b) 1))
		      a)))
   :rule-classes nil
   :hints (("Goal"
	     :use (Find-smallest-y-Lemma-5
		   (:instance
		    Theorem-2-aa
		    (a (- (* 3 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			  (* 4 (Find-smallest-y y))))
		    (b (+ (* -2 (sqrt-posp (+ (* 2
						 (Find-smallest-y y)
						 (Find-smallest-y y))
					      1)))
			  (* 3 (Find-smallest-y y))))))))))

(local
 (defthm
   Theorem-2-ac
   (implies (and (equal (sqrt-posp (+ (* 2 b b) 1))
			 a)
		  (equal (- (* a a)
			    (* 2 b b))
			 1))
	     (equal (* (sqrt-posp (+ (* 2 b b) 1))
		       (sqrt-posp (+ (* 2 b b) 1)))
		    (+ (* 2 b b) 1)))
   :rule-classes nil))

(local
 (defthm
   Theorem-2-ad
   (implies (and (equal (* x x)
			 (+ (* 2 y y) 1))
		  (posp x)
		  (posp y)
		  (not (Exists-pair-pow-equal x y)))
	     (let ((b (+ (* -2 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			 (* 3 (Find-smallest-y y)))))
	       (equal (* (sqrt-posp (+ (* 2 b b) 1))
			 (sqrt-posp (+ (* 2 b b) 1)))
		      (+ (* 2 b b) 1))))
   :rule-classes nil
   :hints (("Goal"
	     :use (Find-smallest-y-Lemma-5
		   Theorem-2-ab
		   (:instance
		    Theorem-2-ac
		    (a (- (* 3 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			  (* 4 (Find-smallest-y y))))
		    (b (+ (* -2 (sqrt-posp (+ (* 2
						 (Find-smallest-y y)
						 (Find-smallest-y y))
					      1)))
			  (* 3 (Find-smallest-y y))))))))))

(local
 (defthm
   Theorem-2-ae
   (implies (and (equal (* x x)
			 (+ (* 2 y y) 1))
		  (posp x)
		  (posp y)
		  (not (Exists-pair-pow-equal x y)))
	     (let ((b (+ (* -2 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			 (* 3 (Find-smallest-y y)))))
	       (Exists-pair-pow-equal (sqrt-posp (+ (* 2 b b) 1))
				      b)))
   :rule-classes nil
   :hints (("Goal"
	     :use (Find-smallest-y-Lemma-5
		   Theorem-2-ad
		   (:instance
		    Find-smallest-y-finds-smallest
		    (b (+ (* -2 (sqrt-posp (+ (* 2
						 (Find-smallest-y y)
						 (Find-smallest-y y))
					      1)))
			  (* 3 (Find-smallest-y y))))))))))

(defthm
  Exists-pair-pow-a-b
  (implies (and (equal (* x x)
			(+ (* 2 y y) 1))
		 (posp x)
		 (posp y)
		 (not (Exists-pair-pow-equal x y)))
	    (let ((a (- (* 3 (sqrt-posp (+ (* 2
					      (Find-smallest-y y)
					      (Find-smallest-y y))
					   1)))
			(* 4 (Find-smallest-y y))))
		  (b (+ (* -2 (sqrt-posp (+ (* 2
					       (Find-smallest-y y)
					       (Find-smallest-y y))
					    1)))
			(* 3 (Find-smallest-y y)))))
	      (Exists-pair-pow-equal a b)))
  :hints (("Goal"
	    :use (Theorem-2-ab
		  Theorem-2-ae))))

(local
 (defthm
   Exists-pair-pow-witness-a-b
   (implies (and (equal (* x x)
			 (+ (* 2 y y) 1))
		  (posp x)
		  (posp y)
		  (not (Exists-pair-pow-equal x y)))
	     (let* ((a (- (* 3 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			  (* 4 (Find-smallest-y y))))
		    (b (+ (* -2 (sqrt-posp (+ (* 2
						 (Find-smallest-y y)
						 (Find-smallest-y y))
					      1)))
			  (* 3 (Find-smallest-y y))))
		    (j (Exists-pair-pow-equal-witness a b)))
	       (and (posp j)
		    (equal (pair-pow j)(list a b)))))
   :hints (("Goal"
	     :use Exists-pair-pow-a-b))))

(local
 (defthm
   Exists-pair-pow-witness-a-b+1
   (implies (and (equal (* x x)
			 (+ (* 2 y y) 1))
		  (posp x)
		  (posp y)
		  (not (Exists-pair-pow-equal x y)))
	     (let* ((a (- (* 3 (sqrt-posp (+ (* 2
						(Find-smallest-y y)
						(Find-smallest-y y))
					     1)))
			  (* 4 (Find-smallest-y y))))
		    (b (+ (* -2 (sqrt-posp (+ (* 2
						 (Find-smallest-y y)
						 (Find-smallest-y y))
					      1)))
			  (* 3 (Find-smallest-y y))))
		    (j (Exists-pair-pow-equal-witness a b)))
	       (and (posp (+ j 1))
		    (equal (pair-pow (+ 1 j))
			   (list (sqrt-posp (+ (* 2
						  (Find-smallest-y y)
						  (Find-smallest-y y))
					       1))
				 (Find-smallest-y y))))))
   :hints (("Goal"
	     :use Exists-pair-pow-witness-a-b))))

(defthm
  Exists-pair-pow-Find-smallest-y
  (implies (and (equal (* x x)
			(+ (* 2 y y) 1))
		 (posp x)
		 (posp y)
		 (not (Exists-pair-pow-equal x y)))
	    (Exists-pair-pow-equal (sqrt-posp (+ (* 2
						    (Find-smallest-y y)
						    (Find-smallest-y y))
						 1))
				   (Find-smallest-y y)))
  :hints (("Goal"
	    :use (Exists-pair-pow-witness-a-b+1
		  (:instance
		   Exists-pair-pow-equal-suff
		   (j (+ 1 (let ((a (- (* 3 (sqrt-posp (+ (* 2
							     (Find-smallest-y y)
							     (Find-smallest-y y))
							  1)))
				       (* 4 (Find-smallest-y y))))
				 (b (+ (* -2 (sqrt-posp (+ (* 2
							      (Find-smallest-y y)
							      (Find-smallest-y y))
							   1)))
				       (* 3 (Find-smallest-y y)))))
			     (Exists-pair-pow-equal-witness a b))))
		   (x (sqrt-posp (+ (* 2
				       (Find-smallest-y y)
				       (Find-smallest-y y))
				    1)))
		   (y (Find-smallest-y y)))))))

(defthm
  Not-Exists-pair-pow-Find-smallest-y
  (implies (and (equal (* x x)
			(+ (* 2 y y) 1))
		 (posp x)
		 (posp y)
		 (not (Exists-pair-pow-equal x y)))
	    (not (Exists-pair-pow-equal (sqrt-posp (+ (* 2
							 (Find-smallest-y y)
							 (Find-smallest-y y))
						      1))
					(Find-smallest-y y))))
  :hints (("Goal"
	    :use Find-smallest-y-not-exists)))
) ;; end encapsulate

(defthm
 Theorem-2
 (implies (and (posp x)
		(posp y)
		(equal (- (* x x)
			  (* 2 y y))
		       1))
	   (exists-pair-pow-equal x y))
 :hints (("Goal"
	   :use (Exists-pair-pow-Find-smallest-y
		 Not-Exists-pair-pow-Find-smallest-y))))

;; Summary of a human version of the above proof:

;; Note (pair-pow j) is denoted by ( x_j,y_j ).

;; By contradiction. Suppose there are positive
;; integers x and y such that for all positive integers j,
;; ( x,y ) |= ( x_j,y_j ) and  x^2 - 2 * y^2 = 1.
;; Since the positive integers are well-ordered, pick such an x
;; and y with y as small as possible.

;; Since y |= y_j for any j, then y > 2.
;; By Lemma 5, a = 3 * x - 4 * y and
;; b = -2 * x + 3 * y are positive integers that satisfy
;; b < y and a^2 - 2 * b^2 = 1.

;; Since y was chosen as small as possible and b < y, there must be
;; a j such that ( a,b ) = ( x_j,y_j ).

;; By Definition 1,
;; ( x_{j+1},y_{j+1} ) = ( x_1 * x_j + 2 * y_1 * y_j,
;;                         x_1 * y_j + x_j * y_1 )
;;                     = ( 3 * a + 2 * 2 * b,
;;                         3 * b + a * 2 )
;;                     = ( x,y ).
;; This contrdicts the above supposition.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Perhaps the most interesting step, to translate into ACL2, of this proof
;; is this: Given at least one pair, ( x,y ), of positive integers such that
;; x^2 - 2 * y^2 = 1$ and for all positive integers j, ( x,y ) |= ( x_j,y_j );
;; we wish to locate the pair, ( q,r ), of positive integers, with r as small
;; as possible}, such that q^2 - 2 * r^2 = 1 and for all positive integers j,
;; ( q,r ) |= ( x_j,y_j ). The desired ( q,r ) is found by an ACL2 function
;; that returns the first pair in this list, of y pairs,
;;                ( 1,1 ), ...,( q = floor(sqrt(2r^2 + 1)),r ),
;;                         ...,( x = floor(sqrt(2y^2 + 1)),y )
;; that satisfies both  q^2 - 2 * r^2 = 1 and for all positive integers j,
;; ( q,r ) |= ( x_j,y_j ).

;;=========Definition 2=================

;; Now the solutions of the Pell equation may be translated into solutions
;; of the original problem.

(defun
 Tri=Sq (n)
 (let* ((pair (pair-pow n))
	 (first (first pair))
	 (second (second pair)))
   (list (/ (- first 1) 2)
	  (/ second 2))))

;;=====Examples====

(defthm
 Examples-Tri=Sq
 (and (equal (Tri=Sq 1)
	      '(1 1))
      (equal (Tri=Sq 2)
	      '(8 6))
      (equal (Tri=Sq 3)
	      '(49 35))
      (equal (Tri=Sq 4)
	      '(288 204))
      (equal (Tri=Sq 5)
	      '(1681 1189))
      (equal (Tri=Sq 6)
	      '(9800 6930))
      (equal (Tri=Sq 7)
	      '(57121 40391))
      (equal (Tri=Sq 8)
	      '(332928 235416))
      (equal (Tri=Sq 9)
	      '(1940449 1372105))))

;;=====Theorem 3=============

;; Combining the results of Lemma 1, Lemma 3, Theorem 1, and Theorem 2
;; yields all the positive integer solutions of the original problem.

(defthm
 Theorem-3-part-1
 (let* ((pair (Tri=Sq j))
	 (nj (first pair))
	 (kj (second pair)))
   (equal (/ (* nj (+ nj 1)) 2)
	   (* kj kj))))

(defun-sk
 Exists-Tri=Sq-equal (n k)
 (exists j (and (posp j)
		 (equal (Tri=Sq j)
			(list n k)))))

(defthm
 Theorem-3-part-2-a
 (implies (and (posp n)
		(posp k)
		(equal (/ (* n (+ n 1)) 2)
		       (* k k)))
	   (let ((x (+ (* 2 n) 1))
		 (y (* 2 k)))
	     (Exists-pair-pow-equal x y)))
 :hints (("Goal"
	   :use Lemma-1)))

(defthm
 Theorem-3-part-2-b
 (implies (and (posp n)
		(posp k)
		(equal (/ (* n (+ n 1)) 2)
		       (* k k)))
	   (let* ((x (+ (* 2 n) 1))
		  (y (* 2 k))
		  (j (Exists-pair-pow-equal-witness x y)))
	     (and (posp j)
		  (equal (Tri=Sq j)
			 (list n k)))))
 :hints (("Goal"
	   :use Theorem-3-part-2-a)))

(defthm
 Theorem-3-part-2
 (implies (and (posp n)
		(posp k)
		(equal (/ (* n (+ n 1)) 2)
		       (* k k)))
	   (Exists-Tri=Sq-equal n k))
 :hints (("Goal"
	   :use Theorem-3-part-2-b)))

;;;;;;;;;;;;;
;; Conclusion

;; An algorithm, given by the functions in Definition 1 and Definition 2,
;; is presented that enumerates all pairs, ( n,k ), of positive integers
;; such that Delta_n = k^2. ACL2 is used to verify that the algorithm
;; is correct.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Appendix
;; More Efficient Generation of Solutions

;; Recall that (pair-pow n) computes all the positive integer
;; solutions (x y) to x^2 - 2 y^2 = 1.

;;====Definition 1=========
#|
(defun
 pair-pow (n)
 (if (and (integerp n)
	   (> n 1))
     (let* ((pair (pair-pow (- n 1)))
	     (first (first pair))
	     (second (second pair)))
	(list (+ (* 3 first)
		 (* 4 second))
	      (+ (* 3 second)
		 (* 2 first))))
     (list 3 2)))
|#

;; This straightforward implementation uses a linear number,
;; in $n$, of arithmetic operations to compute each solution
;; (pair-pow n).

(defun
 nbr-calls-pair-pow (n)
 (if (and (integerp n)
	   (> n 1))
     (+ 1 (nbr-calls-pair-pow (- n 1)))
     1))

(defthm
 pair-pow-is-linear
 (implies (posp n)
	   (equal (nbr-calls-pair-pow n)
		  n)))

;;====Definition 1A=========

(defun
 pair-pow-log (n)
 (if (and (integerp n)
	   (> n 1))
     (if (evenp n)
	  (let* ((pair (pair-pow-log (/ n 2)))
		 (first (first pair))
		 (second (second pair)))
	    (list (+ (* first first)
		     (* 2 second second))
		  (* 2 first second)))
	  (let* ((pair (pair-pow-log (/ (+ -1 n) 2)))
		 (first (first pair))
		 (second (second pair)))
	    (list (+ (* 3 first first)
		     (* 8 first second)
		     (* 6 second second))
		  (+ (* 2 first first)
		     (* 6 first second)
		     (* 4 second second)))))
     (list 3 2)))

;; (pair-pow-log n) produces an alternative sequence of pairs
;; that uses a logarithmic number, in n, of arithmetic
;; operations to compute each pair.

(defun
 nbr-calls-pair-pow-log (n)
 (if (and (integerp n)
	   (> n 1))
     (if (evenp n)
	  (+ 1 (nbr-calls-pair-pow-log (/ n 2)))
	  (+ 1 (nbr-calls-pair-pow-log (/ (- n 1) 2))))
     1))

;; (nbr-calls-pair-pow-log 1) = 1
;; (nbr-calls-pair-pow-log 2) = 2
;; (nbr-calls-pair-pow-log 3) = 2
;; (nbr-calls-pair-pow-log 4) = 3
;; (nbr-calls-pair-pow-log 5) = 3
;; (nbr-calls-pair-pow-log 6) = 3
;; (nbr-calls-pair-pow-log 7) = 3
;; (nbr-calls-pair-pow-log 8) = 4
;; (nbr-calls-pair-pow-log 9) = 4

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Include the log base 2 book.

(include-book "log2")

(defthm
 pair-pow-log-is-logarithmic
 (implies (posp n)
	   (equal (nbr-calls-pair-pow-log n)
		  (+ 1 (flog2 n)))))

;;=====Theorem 4=============

(defthm
 pair-pow-2n-2n+1
 (implies (posp n)
	   (let* ((pair (pair-pow n))
		  (first (first pair))
		  (second (second pair)))
	     (and (equal (pair-pow (* 2 n))
			 (list (+ (* first first)
				  (* 2 second second))
			       (* 2 first second)))
		  (equal (pair-pow (+ 1 (* 2 n)))
			 (list (+ (* 3 first first)
				  (* 8 first second)
				  (* 6 second second))
			       (+ (* 2 first first)
				  (* 6 first second)
				  (* 4 second second))))))))

(defthm
 pair-pow-log-is-correct
 (equal (pair-pow-log n)
	 (pair-pow n))
 :hints (("Subgoal *1/2"
	   :use (:instance
		 pair-pow-2n-2n+1
		 (n (/ (+ -1 n) 2))))
	  ("Subgoal *1/1"
	   :use (:instance
		 pair-pow-2n-2n+1
		 (n (/ n 2))))))

(in-theory (disable pair-pow-log-is-correct))
