; The ACL2 Matrix Algebra Book. Summary of definitions and algebra in matrix.lisp.
; Copyright (C) 2002 Ruben Gamboa and John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; Ruben Gamboa and John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

; Summer and Fall 2002.

#|
 To certify in ACL2 Version 2.6:

  (ld ;; Newline to fool dependency scanner
      "defpkg.lisp")
  (certify-book "kalman-defs" 1)

|#

(in-package "KALMAN")

(include-book "linalg")

 (set-ignore-ok :warn)
 (set-irrelevant-formals-ok :warn)

(defmacro m-id (n)
  `(acl2::m-1 ,n))

(defmacro m-zero (m n)
  `(acl2::m-0 ,m ,n))

(defmacro m-matrixp (m n a)
  `(acl2::matrixp ,m ,n ,a))

(defmacro l (a)
  `(acl2::r ,a))

(defmacro c (a)
  `(acl2::c ,a))

(defmacro m-+ (a b)
  `(acl2::m-+ ,a ,b))

(defmacro m-- (a b)
  `(acl2::m-- ,a ,b))

(defmacro m-unary-- (a)
  `(acl2::m-- ,a))

(defmacro m-* (a b)
  `(acl2::m-* ,a ,b))

(defmacro s-* (k a)
  `(acl2::s-* ,k ,a))

(defmacro m-inv (a)
  `(acl2::m-/ ,a))

(defmacro m-trans (a)
  `(acl2::m-trans ,a))

(defmacro m-singular (a)
  `(acl2::m-singularp ,a))

(defmacro m-= (a b)
  `(acl2::m-= ,a ,b))

(defmacro m-dim-p (n)
  `(acl2::m-dim-p ,n))

(in-theory (disable acl2::m-1 acl2::m-0 acl2::matrixp acl2::m-binary-+
		    acl2::m-unary-- acl2::m-binary-* acl2::s-* acl2::m-/ acl2::m-trans
		    acl2::m-singularp acl2::m-=))

(encapsulate
 (((x-0) => *)				; initial value of x
  ((phi *) => *)			; steps through an iteration of x
  ((ww *) => *)				; iteration step noise
  ((q *) => *)				; covariance of step noise
  ((h *) => *)				; matrix transforming observable to x
  ((v *) => *)				; observation noise
  ((r *) => *)				; covariance of observation noise
  ((xhatmin-0) => *)			; initial guess for best estimate of x
  ((pminus-0) => *)			; initial guess for covariance of estimate
  ((n) => *)				; dimension of x
  ((m) => *)				; dimension of y
  ((m-mean *) => *)			; mean of an expression
  )


 (set-ignore-ok :warn)
 (set-irrelevant-formals-ok :warn)

 (local
  (defun n ()
    1))

 (local
  (defun m ()
    1))

; Addition by Matt K. April 2016 to accommodate addition of type-set bit for
; the set {1}.
 (local (in-theory (disable (:t n) (:t m))))

 (local
  (defun phi (k)
    (m-id (n))))

 (defthm matrix-phi
   (m-matrixp (n) (n) (phi k)))

 (defthm numrows-cols-phi
   (and (equal (l (phi k)) (n))
	(equal (c (phi k)) (n)))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n (n))
			     (acl2::p (phi k)))))))
 (local
  (defun ww (k)
    (m-zero (n) 1)))

 (defthm matrix-w
   (m-matrixp (n) 1 (ww k)))

 (defthm numrows-cols-w
   (and (equal (l (ww k)) (n))
	(equal (c (ww k)) 1))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n 1)
			     (acl2::p (ww k)))))))

 (local
  (defun q (k)
    (m-zero (n) (n))))

 (defthm matrix-q
   (m-matrixp (n) (n) (q k)))

 (defthm numrows-cols-q
   (and (equal (l (q k)) (n))
	(equal (c (q k)) (n)))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n (n))
			     (acl2::p (q k)))))))

 (local
  (defun x-0 ()
    (m-zero (n) 1)))

 (local (in-theory (disable (x-0))))

 (defthm matrix-x-0
   (m-matrixp (n) 1 (x-0)))

 (defthm numrows-cols-x-0
   (and (equal (l (x-0)) (n))
	(equal (c (x-0)) 1))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n 1)
			     (acl2::p (x-0)))))))

 (defun x (k)
   (if (zp k)
       (x-0)
     (m-+ (m-* (phi (1- k)) (x (1- k)))
	  (ww (1- k)))))

 (defthm matrix-x
   (m-matrixp (n) 1 (x k)))

 (defthm numrows-cols-x
   (and (equal (l (x k)) (n))
	(equal (c (x k)) 1))
   :hints (("Goal"
	    :use ((:instance matrix-x)
		  (:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n 1)
			     (acl2::p (x k)))))))

 (local
  (defun mean-x (k)
    (x k)))

 (local
  (defun h (k)
    (m-zero (m) (n))))

 (defthm matrix-h
   (m-matrixp (m) (n) (h k)))

 (defthm numrows-cols-h
   (and (equal (l (h k)) (m))
	(equal (c (h k)) (n)))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (m))
			     (acl2::n (n))
			     (acl2::p (h k)))))))

 (local
  (defun v (k)
    (m-zero (m) 1)))

 (defthm matrix-v
   (m-matrixp (m) 1 (v k)))

 (defthm numrows-cols-v
   (and (equal (l (v k)) (m))
	(equal (c (v k)) 1))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (m))
			     (acl2::n 1)
			     (acl2::p (v k)))))))

 (defun z (k)
   (m-+ (m-* (h k) (x k))
	(v k)))

 (local (defthm matrix-x-1 (ACL2::MATRIXP 1 1 (X K))))

 (defthm matrix-z
   (m-matrixp (m) 1 (z k)))

 (defthm numrows-cols-z
   (and (equal (l (z k)) (m))
	(equal (c (z k)) 1))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (m))
			     (acl2::n 1)
			     (acl2::p (z k)))))))

 (local
  (defun r (k)
    (m-zero (m) (m))))

 (defthm matrix-r
   (m-matrixp (m) (m) (r k)))

 (defthm numrows-cols-r
   (and (equal (l (r k)) (m))
	(equal (c (r k)) (m)))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (m))
			     (acl2::n (m))
			     (acl2::p (r k)))))))
 (local
  (defun xhatmin-0 ()
    (x 0)))

 (defthm matrix-xhatmin-0
   (m-matrixp (n) 1 (xhatmin-0))
   :hints (("Goal"
	    :expand ((xhatmin-0))
	    :in-theory (disable (x) (xhatmin-0)))))

 (defthm numrows-cols-xhatmin-0
   (and (equal (l (xhatmin-0)) (n))
	(equal (c (xhatmin-0)) 1))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n 1)
			     (acl2::p (xhatmin-0)))
		  (:instance matrix-xhatmin-0)))))

 (local
  (defun pminus-0 ()
    (m-zero (n) (n))))

 (defthm matrix-pminus-0
   (m-matrixp (n) (n) (pminus-0))
   :hints (("Goal"
	    :expand ((pminus-0))
	    :in-theory (disable (pminus-0)))))

 (defthm numrows-cols-pminus-0
   (and (equal (l (pminus-0)) (n))
	(equal (c (pminus-0)) (n)))
   :hints (("Goal"
	    :use ((:instance acl2::matrix-p-numrows-cols
			     (acl2::m (n))
			     (acl2::n (n))
			     (acl2::p (pminus-0)))
		  (:instance matrix-pminus-0)))))
 (local
  (defun m-mean (m-expr)
    m-expr))

 (defthm matrix-mean
   (implies (m-matrixp m n m-expr)
	    (m-matrixp m n (m-mean m-expr))))

 (defthm numrows-cols-mean
   (and (equal (l (m-mean m-expr)) (l m-expr))
	(equal (c (m-mean m-expr)) (c m-expr))))

 (defcong
   m-= m-= (m-mean x) 1)

 (defthm mean-trans
   (equal (m-mean (m-trans p))
	  (m-trans (m-mean p))))

 (defthm mean-+
   (implies (and (equal (l p) (l q))
		 (equal (c p) (c q)))
	    (equal (m-mean (m-+ p q))
		   (m-+ (m-mean p) (m-mean q)))))

 (defthm mean-*
   (implies (equal (c p) (l q))
	    (equal (m-mean (m-* p q))
		   (m-* (m-mean p) (m-mean q)))))

 (defthm mean-unary--
   (equal (m-mean (m-unary-- p))
	  (m-unary-- (m-mean p))))

 (defthm mean-delete
   (equal (m-mean p)
	  p))

 (defthm mean-of-v-vtrans
   (m-= (m-mean (m-* (v k) (m-trans (v k))))
	(r k)))

 (defthm mean-of-w-wtrans
   (m-= (m-mean (m-* (ww k) (m-trans (ww k))))
	(q k)))

 (defmacro pminus-body (k)
   `(if (zp ,k)
	(pminus-0)
      (m-+ (m-* (phi (1- ,k))
		(m-* (pplus (1- ,k))
		     (m-trans (phi (1- ,k)))))
	   (q (1- ,k)))))

 (defmacro gain-body (k)
   `(m-* (pminus-body ,k)
	 (m-* (m-trans (h ,k))
	      (m-inv (m-+ (m-* (h ,k)
			       (m-* (pminus-body ,k)
				    (m-trans (h ,k))))
			  (r ,k))))))

 (defun pplus (k)
;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.
;    ":Doc-Section ACL2::Programming
;
; estimate of error covariance~/~/
; "
   (if (zp k)
       (m-* (m-- (m-id (l (x k)))
		 (m-* (m-* (pminus-0)
			   (m-* (m-trans (h k))
				(m-inv (m-+ (m-* (h k)
						 (m-* (pminus-0)
						      (m-trans (h k))))
					    (r k)))))
		      (h k)))
	    (pminus-0))
     (m-* (m-- (m-id (l (x k)))
	       (m-* (gain-body k)
		    (h k)))
	  (pminus-body k))))

 (defun pminus (k)
;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.
;    ":Doc-Section ACL2::Programming
;
; a priori estimate of error covariance~/~/
; "
   (pminus-body k))

 (defun gain (k)
;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.
;    ":Doc-Section ACL2::Programming
;
; Kalman gain modifies observation residual to get better estimate of x~/~/
; "
   (m-* (pminus k)
	(m-* (m-trans (h k))
	     (m-inv (m-+ (m-* (h k)
			      (m-* (pminus k)
				   (m-trans (h k))))
			 (r k))))))



 (defthm pplus-recdef
   (implies (and (integerp k)
		 (<= 0 k))
	    (equal (pplus k)
		   (m-* (m-- (m-id (l (x k)))
			     (m-* (gain k)
				  (h k)))
			(pminus k))))
   :hints (("Goal"
	    :in-theory (disable x (x)
				h (h)
				phi (phi)
				q (q)
				r (r)
				(pminus) (pplus) (gain))))
   :rule-classes ((:definition
		   :clique (pplus pminus gain)
		   :controller-alist ((pplus t)
				      (pminus t)
				      (gain t)))))

 (defthm pminus-recdef
   (implies (and (integerp k)
		 (< 0 k))
	    (equal (pminus k)
		   (m-+ (m-* (phi (1- k))
			     (m-* (pplus (1- k))
				  (m-trans (phi (1- k)))))
			(q (1- k)))))
   :hints (("Goal"
	    :in-theory (disable x (x)
				h (h)
				phi (phi)
				q (q)
				r (r)
				pplus-recdef (pminus) (pplus) (gain))))
   :rule-classes ((:definition
		   :clique (pplus pminus gain)
		   :controller-alist ((pplus t)
				      (pminus t)
				      (gain t)))))

 (defthm gain-recdef
   (implies (and (integerp k)
		 (<= 0 k))
	    (equal (gain k)
		   (m-* (pminus k)
			(m-* (m-trans (h k))
			     (m-inv (m-+ (m-* (h k)
					      (m-* (pminus k)
						   (m-trans (h k))))
					 (r k)))))))
   :hints (("Goal"
	    :in-theory (disable x (x)
				h (h)
				phi (phi)
				q (q)
				r (r)
				pplus-recdef (pminus) (pplus) (gain))))
   :rule-classes ((:definition
		   :clique (pplus pminus gain)
		   :controller-alist ((pplus t)
				      (pminus t)
				      (gain t)))))

 (in-theory (disable (:definition pminus)
		     (:definition pplus)
		     (:definition gain)))

 (defmacro xhat-body (k)
   `(m-+ (xhatmin ,k)
	 (m-* (gain ,k)
	      (m-- (z ,k)
		   (m-* (h ,k) (xhatmin ,k))))))

 (defun xhatmin (k)
;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.
;    ":Doc-Section ACL2::Programming
;
; estimate of x(k) before seeing measurement z(k)~/~/
; "
   (if (zp k)
       (xhatmin-0)
     (m-* (phi (1- k)) (xhat-body (1- k)))))

 (defun xhat (k)
;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form
;;; see defxdoc form towards in the last part of this file.
;    ":Doc-Section ACL2::Programming
;
; estimate of x(k) using measurement z(k)~/~/
; "
   (xhat-body k))

 (defthm xhatmin-recdef
   (implies (and (integerp k)
		 (< 0 k))
	    (equal (xhatmin k)
		   (m-* (phi (1- k)) (xhat (1- k)))))
   :rule-classes ((:definition
		   :clique (xhat xhatmin)
		   :controller-alist ((xhat t)
				      (xhatmin t)))))


 (in-theory (disable (:definition xhatmin)))

 (defthm dim-p-m
   (m-dim-p (m)))

 (defthm dim-p-n
   (m-dim-p (n)))

 (local (in-theory (disable n (n)
			    m (m)
			    (x)
			    (xhatmin-0)
			    (pminus-0))))

 (encapsulate
  ()

  (local
   (defthm lemma-1
     (implies (zp k)
	      (m-matrixp (n) 1 (xhatmin k)))
     :hints (("Goal"
; :With directives added 3/13/06 by Matt Kaufmann for after v2-9-4.
	      :expand ((:with xhatmin (xhatmin k)) (n))))))

  (local
   (defthm lemma-2
     (implies (and (not (zp k))
		   (m-matrixp (n) 1 (xhat (1- k))))
	      (m-matrixp (n) 1 (xhatmin k)))))

  (defthm lemma-2-5
    (acl2::matrixp (m) (m) (acl2::m-/ (ACL2::M-BINARY-+ (ACL2::M-0 (M) (M))
							(ACL2::M-0 (M) (M)))))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-inv
			      (acl2::P (ACL2::M-BINARY-+ (ACL2::M-0 (M) (M))
							 (ACL2::M-0 (M) (M))))
			      (acl2::n (m))))
	     :in-theory (disable acl2::matrix-inv))))

  (local
   (defthm lemma-3
     (implies (zp k)
	      (m-matrixp (n) (n) (pplus k)))
     :hints (("Goal"
; :With directives added 3/14/06 by Matt Kaufmann for after v2-9-4.
	      :expand ((:with pplus (pplus k)))))))

  (local
   (defthm lemma-4
     (implies (and (not (zp k))
		   (m-matrixp (n) (m) (gain k))
		   (m-matrixp (n) (n) (pminus k)))
	      (m-matrixp (n) (n) (pplus k)))))

  (local
   (defthm lemma-5
     (implies (zp k)
	      (m-matrixp (n) (n) (pminus k)))
     :hints (("Goal"
; :With directives added 3/14/06 by Matt Kaufmann for after v2-9-4.
	      :expand ((:with pminus (pminus k)))
	      :in-theory (disable gain-recdef pplus-recdef pminus-recdef)))))

  (local
   (defthm lemma-6
     (implies (and (not (zp k))
		   (or (zp (1- k))
		       (and (m-matrixp (n) (m) (gain (1- k)))
			    (m-matrixp (n) (n) (pminus (1- k))))))
	      (m-matrixp (n) (n) (pminus k)))
     :hints (("Goal"
	      :expand ((pminus k))
	      :in-theory (disable gain-recdef pplus-recdef pminus-recdef))
	     ("Subgoal 2"
	      :use ((:instance lemma-3 (k (1- k))))
	      :in-theory (disable lemma-3 pplus-recdef))
	     ("Subgoal 1"
	      :use ((:instance lemma-4 (k (1- k))))
	      :in-theory (disable lemma-4)))))

  (local
   (defun natural-induction (k)
     (if (zp k)
	 1
       (1+ (natural-induction (1- k))))))

  (local
   (defthm matrix-gain-pminus
     (and (m-matrixp (n) (n) (pminus k))
	  (m-matrixp (n) (m) (gain k)))
     :hints (("Goal"
	      :induct (natural-induction k))
	     ("Subgoal *1/2"
	      :use ((:instance lemma-6))
	      :in-theory (disable lemma-6 gain-recdef pminus-recdef))
; :With directives added 3/14/06 by Matt Kaufmann for after v2-9-4.
	     ("Subgoal *1/2'''"
	      :expand ((:with gain (gain k))))
	     ("Subgoal *1/1"
	      :expand ((:with gain (gain k))))
	     ("Subgoal *1/1'"
	      :use ((:instance lemma-5))
	      :in-theory (disable lemma-5)))))

  (defthm matrix-gain
    (m-matrixp (n) (m) (gain k)))

  (defthm numrows-cols-gain
    (and (equal (l (gain k)) (n))
	 (equal (c (gain k)) (m)))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-p-numrows-cols
			      (acl2::m (n))
			      (acl2::n (m))
			      (acl2::p (gain k)))))))


  (defthm matrix-pminus
    (m-matrixp (n) (n) (pminus k)))

  (defthm numrows-cols-pminus
    (and (equal (l (pminus k)) (n))
	 (equal (c (pminus k)) (n)))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-p-numrows-cols
			      (acl2::m (n))
			      (acl2::n (n))
			      (acl2::p (pminus k)))))))

  (defthm matrix-pplus
    (m-matrixp (n) (n) (pplus k))
    :hints (("Goal"
	     :use ((:instance lemma-3)
		   (:instance lemma-4)
		   (:instance matrix-gain-pminus))
	     :in-theory nil)))

  (defthm numrows-cols-pplus
    (and (equal (l (pplus k)) (n))
	 (equal (c (pplus k)) (n)))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-p-numrows-cols
			      (acl2::m (n))
			      (acl2::n (n))
			      (acl2::p (pplus k)))))))


  (local
   (defthm lemma-7
     (implies (zp k)
	      (m-matrixp (n) 1 (xhat k)))
     :hints (("Goal" :do-not-induct t
	      :expand ((xhat k)))
	     ("Goal'"
	      :use ((:instance lemma-1))
	      :in-theory (disable lemma-1)))))

  (local
   (defthm lemma-8
     (implies (and (not (zp k))
		   (m-matrixp (n) 1 (xhat (1- k))))
	      (m-matrixp (n) 1 (xhat k)))
     :hints (("Goal" :do-not-induct t
	      :in-theory (disable xhatmin-recdef gain-recdef))
	     ("Goal'"
	      :use ((:instance lemma-2))
	      :in-theory (disable xhatmin-recdef gain-recdef lemma-2))
	     ("Goal''"
	      :expand ((xhat k))))))


  (defthm matrix-xhat
    (m-matrixp (n) 1 (xhat k))
    :hints (("Goal"
	     :induct (natural-induction k))
	    ("Subgoal *1/2"
	     :by (:instance lemma-8))
	    ("Subgoal *1/1"
	     :by (:instance lemma-7))))

  (defthm numrows-cols-xhat
    (and (equal (l (xhat k)) (n))
	 (equal (c (xhat k)) 1))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-p-numrows-cols
			      (acl2::m (n))
			      (acl2::n 1)
			      (acl2::p (xhat k)))))))

  (defthm matrix-xhatmin
    (m-matrixp (n) 1 (xhatmin k))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance lemma-2)
		   (:instance matrix-xhat (k (1- k))))
	     :in-theory nil)))

  (defthm numrows-cols-xhatmin
    (and (equal (l (xhatmin k)) (n))
	 (equal (c (xhatmin k)) 1))
    :hints (("Goal"
	     :use ((:instance acl2::matrix-p-numrows-cols
			      (acl2::m (n))
			      (acl2::n 1)
			      (acl2::p (xhatmin k)))))))
  )

 (defthm mean-of-x-xhatmin*vtrans
   (m-= (m-mean (m-* (m-+ (x k)
			  (m-unary-- (xhatmin k)))
		     (m-trans (v k))))
	(m-zero (n) (m))))

 (defthm mean-of-v*trans-of-x-xhatmin
   (m-= (m-mean (m-* (v k)
		     (m-trans (m-+ (x k)
				   (m-unary-- (xhatmin k))))))
	(m-zero (m) (n))))

 (defthm mean-of-x-xhat*wtrans
   (m-= (m-mean (m-* (m-+ (x k)
			  (m-unary-- (xhat k)))
		     (m-trans (ww k))))
	(m-zero (n) (n))))

 (defthm mean-of-w*trans-of-x-xhat
   (m-= (m-mean (m-* (ww k)
		     (m-trans (m-+ (x k)
				   (m-unary-- (xhat k))))))
	(m-zero (n) (n))))

 (defthm pminus-0-def
   (m-= (pminus-0)
	(m-mean (m-* (m-- (x 0) (xhatmin-0))
		     (m-trans (m-- (x 0) (xhatmin-0))))))
   :hints (("Goal"
	    :in-theory (disable (pminus-0)
				(x)
				(xhatmin-0)))))

 )

(in-theory (disable mean-* mean-delete))

; The forms below were initially generated automatically from
; legacy documentation strings in this file.

(include-book "xdoc/top" :dir :system)
(defmacro defxdoc (&rest args)
  `(acl2::defxdoc ,@args))

(defxdoc kalman::gain
  :parents (programming)
  :short "Kalman gain modifies observation residual to get better estimate of x"
  :long "")

(defxdoc kalman::pminus
  :parents (programming)
  :short "A priori estimate of error covariance"
  :long "")

(defxdoc kalman::pplus
  :parents (programming)
  :short "Estimate of error covariance"
  :long "")

(defxdoc kalman::xhat
  :parents (programming)
  :short "Estimate of x(k) using measurement z(k)"
  :long "")

(defxdoc kalman::xhatmin
  :parents (programming)
  :short "Estimate of x(k) before seeing measurement z(k)"
  :long "")
