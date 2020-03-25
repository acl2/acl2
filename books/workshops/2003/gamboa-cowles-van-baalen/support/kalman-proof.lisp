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
;  Last modified 1 November 2002.

#|
 To certify in ACL2 Version 2.6

  (ld ;; Newline to fool dependency scanner
   "defpkg.lsp")
  (certify-book "kalman-proof" 1)
|#

(in-package "KALMAN")

(include-book "kalman-defs")

(defmacro enable-disable (enable-list disable-list)
  (list 'union-theories
	(cons 'disable disable-list)
	`(quote ,enable-list)))

(defstub best-estimate-of-x (*) => *)

(defun best-prior-estimate-of-x (k)
  (if (zp k)
      (xhatmin k)
    (m-* (phi (1- k))
	 (best-estimate-of-x (1- k)))))

(defun result-form (y Xp k)
  (m-+ Xp
       (m-* y
	    (m-- (z k)
		 (m-* (h k)
		      Xp)))))

(defun result-form-derivative (y Xp k)
  (m-+ (s-* 2 (m-mean (m-* (m-- Xp (x k))
			   (m-trans (m-- (z k)
					 (m-* (h k) Xp))))))
       (s-* 2 (m-* y
		   (m-mean (m-* (m-- (z k)
				     (m-* (h k) Xp))
				(m-trans (m-- (z k)
					      (m-* (h k) Xp)))))))))

(defaxiom best-estimate-of-x-def
  (implies (and (m-= (best-prior-estimate-of-x k) Xp)
		(m-= (result-form-derivative y Xp k) (m-zero (n) (m))))
	   (m-= (best-estimate-of-x k)
		(result-form y Xp k))))

(skip-proofs
 (defthm non-singular-gain-component
   (not (m-singular (m-mean (m-* (m-+ (z k)
                                 (m-unary-- (m-* (h k) (xhatmin k))))
                            (m-+ (m-trans (z k))
                                 (m-unary-- (m-* (m-trans (xhatmin k))
                                                 (m-trans (h k)))))))))))

(skip-proofs
 (defthm non-singular-gain-component-2
   (not (m-singular (m-+ (r k) (m-* (h k) (m-* (pminus k) (m-trans (h k)))))))))

(defthm pminus-as-mean-case-0
  (implies (= k 0)
	   (m-= (pminus k)
		(m-mean (m-* (m-- (x k) (xhatmin k))
			     (m-trans (m-- (x k) (xhatmin k)))))))
  :hints (("Goal"
	   :expand ((pminus k))
	   :in-theory (enable-disable (pminus xhatmin)
                                      (x ; added by Matt K. for v2-8, 7/31/03
                                       (pminus) (xhatmin)
; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
                                       (x))))))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (implies (and (integerp k)
		  (< 0 k))
	     (equal (m-- (x k) (xhatmin k))
		    (m-- (m-+ (m-* (phi (1- k)) (x (1- k)))
			      (ww (1- k)))
			 (m-* (phi (1- k))
			      (xhat (1- k))))))
    :hints (("Goal" :do-not-induct t
	     :in-theory (disable xhat)))
    :rule-classes nil))

 (local
  (defthm lemma-2
    (implies (and (integerp k)
		  (< 0 k))
	     (equal (m-- (x k) (xhatmin k))
		    (m-+ (m-* (phi (1- k))
			      (m-- (x (1- k))
				   (xhat (1- k))))
			 (ww (1- k)))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-1)
		   (:instance (:theorem
			       (implies (and (m-matrixp (l phi) (c phi) phi)
					     (m-matrixp (l x) (c x) x)
					     (m-matrixp (l xhat) (c xhat) xhat)
					     (m-matrixp (l ww) (c x) ww)
					     (equal (c phi) (l x))
					     (equal (l phi) (l ww))
					     (equal (c x) (c ww))
					     (equal (c phi) (l xhat))
					     (equal (c x) (c xhat))
					     (equal (l x) (l xhat)))
					(equal (m-- (m-+ (m-* phi x)
							 ww)
						    (m-* phi xhat))
					       (m-+ (m-* phi (m-- x xhat))
						    ww))))
			      (phi (phi (1- k)))
			      (x (x (1- k)))
			      (ww (ww (1- k)))
			      (xhat (xhat (1- k))))))
	    ("Subgoal 2'" :in-theory nil))
    :rule-classes nil))

 (local
  (defthm lemma-3a
    (implies (and (m-matrixp (l a) (c a) a)
		  (m-matrixp (l b) (c b) b)
		  (equal (l a) (l b))
		  (equal (c a) (c b)))
	     (m-= (m-* (m-+ a b)
		       (m-trans (m-+ a b)))
		  (m-+ (m-* a (m-trans a))
		       (m-+ (m-* a (m-trans b))
			    (m-+ (m-* b (m-trans a))
				 (m-* b (m-trans b)))))))
    :rule-classes nil))

 (local
  (defthm lemma-3b-1
    (implies (and (m-= (m-* (m-+ (m-* phi (m-+ x (m-unary-- xhat))) ww)
			    (m-trans (m-+ (m-* phi (m-+ x (m-unary-- xhat))) ww)))
		       (m-+ (m-* phi
				 (m-* (m-+ x (m-unary-- xhat))
				      (m-trans (m-* phi
						    (m-+ x
							 (m-unary-- xhat))))))
			    (m-+ (m-* phi (m-* (m-+ x (m-unary-- xhat))
					       (m-trans ww)))
				 (m-+ (m-* ww
					   (m-trans (m-* phi
							 (m-+ x
							      (m-unary-- xhat)))))
				      (m-* ww (m-trans ww))))))
		  (m-matrixp (l x) (c x) x)
		  (m-matrixp (l xhat) (c xhat) xhat)
		  (m-matrixp (l phi) (c phi) phi)
		  (m-matrixp (l ww) (c ww) ww)
		  (equal (l phi) (l ww))
		  (equal (c x) (c ww))
		  (equal (c phi) (l x))
		  (equal (c ww) (c xhat))
		  (equal (l x) (l xhat)))
	     (m-= (m-* (m-+ (m-* phi (m-+ x (m-unary-- xhat))) ww)
		       (m-trans (m-+ (m-* phi (m-+ x (m-unary-- xhat))) ww)))
		  (m-+ (m-* phi (m-* (m-+ x (m-unary-- xhat))
				     (m-* (m-trans (m-+ x (m-unary-- xhat)))
					  (m-trans phi))))
		   (m-+ (m-* phi (m-* (m-+ x (m-unary-- xhat)) (m-trans ww)))
			(m-+ (m-* ww (m-* (m-trans (m-+ x (m-unary-- xhat)))
					  (m-trans phi)))
			     (m-* ww (m-trans ww)))))))
    :hints (("Goal"
	     :use ((:instance acl2::trans-*
			      (acl2::p phi)
			      (acl2::q (m-- x xhat))))
	     :in-theory (disable acl2::trans-*
				 acl2::*-+-right
				 acl2::*-+-left)))
    :rule-classes nil))

 (local
  (defthm lemma-3b
    (implies (and (m-matrixp (l x) (c x) x)
		  (m-matrixp (l xhat) (c xhat) xhat)
		  (m-matrixp (l phi) (c phi) phi)
		  (m-matrixp (l ww) (c ww) ww)
		  (equal (c phi) (l x))
		  (equal (l phi) (l ww))
		  (equal (c x) (c ww))
		  (equal (c phi) (l xhat))
		  (equal (c x) (c xhat))
		  (equal (l x) (l xhat)))
	     (m-= (m-* (m-+ (m-* phi (m-- x xhat)) ww)
		       (m-trans (m-+ (m-* phi (m-- x xhat)) ww)))
		  (m-+ (m-* (m-* phi (m-- x xhat)) (m-* (m-trans (m-- x xhat))
							(m-trans phi)))
		       (m-+ (m-* (m-* phi (m-- x xhat)) (m-trans ww))
			    (m-+ (m-* ww (m-* (m-trans (m-- x xhat))
					      (m-trans phi)))
				 (m-* ww (m-trans ww)))))))
    :hints (("Goal"
	     :use ((:instance lemma-3a
			      (a (m-* phi (m-- x xhat)))
			      (b ww))))
	    ("Goal''"
	     :use ((:instance lemma-3b-1))
	     :in-theory (disable acl2::trans-*
				 acl2::*-+-right
				 acl2::*-+-left)))
    :rule-classes nil))

 (local
  (defthm lemma-3
    (m-= (m-* (m-+ (m-* (phi (1- k)) (m-- (x (1- k)) (xhat (1- k))))
		     (ww (1- k)))
		(m-trans (m-+ (m-* (phi (1- k))
				   (m-- (x (1- k)) (xhat (1- k))))
			      (ww (1- k)))))
	   (m-+ (m-* (m-* (phi (1- k))
			  (m-- (x (1- k)) (xhat (1- k))))
		     (m-* (m-trans (m-- (x (1- k)) (xhat (1- k))))
			  (m-trans (phi (1- k)))))
		(m-+ (m-* (m-* (phi (1- k))
			       (m-- (x (1- k)) (xhat (1- k))))
			  (m-trans (ww (1- k))))
		     (m-+ (m-* (ww (1- k))
			       (m-* (m-trans (m-- (x (1- k))
						  (xhat (1- k))))
				    (m-trans (phi (1- k)))))
			  (m-* (ww (1- k)) (m-trans (ww (1- k))))))))
    :hints (("Goal"
	     :use ((:instance lemma-3b
			      (phi (phi (1- k)))
			      (x (x (1- k)))
			      (ww (ww (1- k)))
			      (xhat (xhat (1- k)))))))
    :rule-classes nil))

 (local
  (defthm lemma-4a
    (m-= (M-MEAN
	  (ACL2::M-BINARY-* (PHI (+ -1 K))
			    (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X (+ -1 K))
								(ACL2::M-UNARY-- (XHAT (+ -1 K))))
					      (ACL2::M-TRANS (WW (+ -1 K))))))
	 (m-zero (n) (n)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance mean-*
			      (p (phi (+ -1 k)))
			      (q (m-* (m-+ (x (+ -1 k))
					   (m-unary-- (xhat (+ -1 k))))
				      (m-trans (ww (+ -1 k))))))
		   (:instance mean-of-x-xhat*wtrans
			      (k (1- k))))
	     :in-theory (disable xhat z
				 acl2::*-+-right
				 mean-of-x-xhat*wtrans)))))

 (local
  (defthm lemma-4b
    (m-= (M-MEAN
	  (ACL2::M-BINARY-* (WW (+ -1 K))
			    (ACL2::M-BINARY-*
			     (ACL2::M-BINARY-+ (ACL2::M-TRANS (X (+ -1 K)))
					       (ACL2::M-UNARY-- (ACL2::M-TRANS (XHAT (+ -1 K)))))
			     (ACL2::M-TRANS (PHI (+ -1 K))))))
	   (m-zero (n) (n)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance mean-*
			      (p (m-* (ww (+ -1 k))
				      (m-+ (m-trans (x (+ -1 k)))
					   (m-unary-- (m-trans (xhat (+ -1 k)))))))
			      (q (m-trans (phi (+ -1 k)))))
		   (:instance mean-of-w*trans-of-x-xhat
			      (k (1- k))))
	     :in-theory (disable xhat z
				 acl2::*-+-right
				 mean-of-w*trans-of-x-xhat)))))


 (local
  (defthm lemma-4c
    (m-= (M-MEAN
	  (ACL2::M-BINARY-* (PHI (+ -1 K))
			    (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X (+ -1 K))
								(ACL2::M-UNARY-- (XHAT (+ -1 K))))
					      (ACL2::M-BINARY-*
					       (ACL2::M-BINARY-+ (ACL2::M-TRANS (X (+ -1 K)))
								 (ACL2::M-UNARY-- (ACL2::M-TRANS (XHAT (+ -1 K)))))
					       (ACL2::M-TRANS (PHI (+ -1 K)))))))
	 (m-* (m-* (phi (1- k))
		   (m-mean (m-* (m-+ (x (+ -1 k))
				     (m-unary-- (xhat (+ -1 k))))
				(m-trans (m-+ (x (+ -1 k))
					      (m-unary-- (xhat (+ -1 k))))))))
	      (m-trans (phi (1- k)))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance mean-*
			      (p (m-* (phi (1- k))
				      (m-* (m-+ (x (+ -1 k))
						(m-unary-- (xhat (+ -1 k))))
					   (m-trans (m-+ (x (+ -1 k))
							 (m-unary-- (xhat (+ -1 k))))))))
			      (q (m-trans (phi (+ -1 k)))))
		   (:instance mean-*
			      (p (phi (+ -1 k)))
			      (q (m-* (m-+ (x (+ -1 k))
					   (m-unary-- (xhat (+ -1 k))))
				      (m-trans (m-+ (x (+ -1 k))
						    (m-unary-- (xhat (+ -1 k))))))))
		   (:instance mean-delete
			      (p (phi (1- k)))))
	     :in-theory (disable xhat z acl2::*-+-right)))))

 (local
  (defthm lemma-4-1
    (acl2::m-=
     (m-mean
      (acl2::m-binary-+
       (acl2::m-binary-*
	(phi (+ -1 k))
	(acl2::m-binary-*
	 (acl2::m-binary-+ (x (+ -1 k))
			   (acl2::m-unary-- (xhat (+ -1 k))))
	 (acl2::m-binary-*
	  (acl2::m-binary-+ (acl2::m-trans (x (+ -1 k)))
			    (acl2::m-unary-- (acl2::m-trans (xhat (+ -1 k)))))
	  (acl2::m-trans (phi (+ -1 k))))))
       (acl2::m-binary-+
	(acl2::m-binary-*
	 (phi (+ -1 k))
	 (acl2::m-binary-* (acl2::m-binary-+ (x (+ -1 k))
					     (acl2::m-unary-- (xhat (+ -1 k))))
			   (acl2::m-trans (ww (+ -1 k)))))
	(acl2::m-binary-+
	 (acl2::m-binary-* (ww (+ -1 k))
			   (acl2::m-trans (ww (+ -1 k))))
	 (acl2::m-binary-*
	  (ww (+ -1 k))
	  (acl2::m-binary-*
	   (acl2::m-binary-+ (acl2::m-trans (x (+ -1 k)))
			     (acl2::m-unary-- (acl2::m-trans (xhat (+ -1 k)))))
	   (acl2::m-trans (phi (+ -1 k)))))))))
     (acl2::m-binary-+
      (q (+ -1 k))
      (acl2::m-binary-*
       (phi (+ -1 k))
       (acl2::m-binary-*
	(m-mean
	 (acl2::m-binary-*
	  (acl2::m-binary-+ (x (+ -1 k))
			    (acl2::m-unary-- (xhat (+ -1 k))))
	  (acl2::m-binary-+ (acl2::m-trans (x (+ -1 k)))
			    (acl2::m-unary-- (acl2::m-trans (xhat (+ -1 k)))))))
	(acl2::m-trans (phi (+ -1 k)))))))
    :hints (("Goal" :in-theory (disable acl2::*-+-right
					acl2::*---right
					acl2::*-+-left
					acl2::*---left
					acl2::right-distributivity-of-m-*-over-m-+
					acl2::left-distributivity-of-m-*-over-m-+
					xhat x z xhatmin-recdef gain-recdef)))))

 (local
  (defthm lemma-4
    (m-= (m-mean (m-* (m-+ (m-* (phi (1- k)) (m-- (x (1- k)) (xhat (1- k))))
			   (ww (1- k)))
		      (m-trans (m-+ (m-* (phi (1- k))
					 (m-- (x (1- k)) (xhat (1- k))))
				    (ww (1- k))))))
	 (m-+ (m-* (m-* (phi (1- k))
			(m-mean (m-* (m-- (x (1- k)) (xhat (1- k)))
				     (m-trans (m-- (x (1- k)) (xhat (1- k)))))))
		   (m-trans (phi (1- k))))
	      (q (1- k))))
    :hints (("Goal"
	     :use ((:instance lemma-3))
	     :in-theory nil)
	    ("Goal'"
	     :use ((:theorem  (m-=
			       (m-mean
				(m-+ (m-* (m-* (phi (+ -1 k))
					       (m-- (x (+ -1 k)) (xhat (+ -1 k))))
					  (m-* (m-trans (m-- (x (+ -1 k)) (xhat (+ -1 k))))
					       (m-trans (phi (+ -1 k)))))
				     (m-+ (m-* (m-* (phi (+ -1 k))
						    (m-- (x (+ -1 k)) (xhat (+ -1 k))))
					       (m-trans (ww (+ -1 k))))
					  (m-+ (m-* (ww (+ -1 k))
						    (m-* (m-trans (m-- (x (+ -1 k)) (xhat (+ -1 k))))
							 (m-trans (phi (+ -1 k)))))
					       (m-* (ww (+ -1 k))
						    (m-trans (ww (+ -1 k))))))))
			       (m-+ (m-* (m-* (phi (+ -1 k))
					      (m-mean (m-* (m-- (x (+ -1 k)) (xhat (+ -1 k)))
							   (m-trans (m-- (x (+ -1 k)) (xhat (+ -1 k)))))))
					 (m-trans (phi (+ -1 k))))
				    (q (+ -1 k))))))
	     :in-theory (disable acl2::*-+-right
				 acl2::*---right
				 acl2::*-+-left
				 acl2::*---left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+
				 acl2::commutativity-2-of-m-+
				 xhat
				 x
				 z
				 xhatmin-recdef
				 gain-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-5
    (implies (and (integerp k)
		  (< 0 k))
	     (m-= (m-mean (m-* (m-- (x k) (xhatmin k))
			       (m-trans (m-- (x k) (xhatmin k)))))
		  (m-+ (m-* (m-* (phi (1- k))
				 (m-mean (m-* (m-- (x (1- k)) (xhat (1- k)))
					      (m-trans (m-- (x (1- k)) (xhat (1- k)))))))
			    (m-trans (phi (1- k))))
		       (q (1- k)))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-2)
		   (:instance lemma-4))
	     :in-theory (disable x xhat xhatmin-recdef
				 acl2::*-+-right
				 acl2::*---right
				 acl2::*-+-left
				 acl2::*---left
				 acl2::right-distributivity-of-m-*-over-m-+
				 acl2::left-distributivity-of-m-*-over-m-+
				 acl2::commutativity-2-of-m-+)))
    :rule-classes nil))

 (defthm pminus-as-mean-almost
   (implies (and (integerp k)
		 (< 0 k)
		 (m-= (pplus (1- k))
		      (m-mean (m-* (m-- (x (1- k))
					(xhat (1- k)))
				   (m-trans (m-- (x (1- k))
						 (xhat (1- k))))))))
	    (m-= (pminus k)
		 (m-mean (m-* (m-- (x k) (xhatmin k))
			      (m-trans (m-- (x k) (xhatmin k)))))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-5))
	    :in-theory (disable x xhat xhatmin
				gain-recdef pplus-recdef xhatmin-recdef
				acl2::*-+-right
				acl2::*---right
				acl2::*-+-left
				acl2::*---left
				acl2::right-distributivity-of-m-*-over-m-+
				acl2::left-distributivity-of-m-*-over-m-+
				acl2::commutativity-2-of-m-+))))
 )

(defthm matrix-*-trans
  (implies (and (equal m (l x))
		(equal n (l x))
		(m-matrixp m n x))
	   (m-matrixp m n (m-* x (m-trans x)))))

(defthm id-*-x-useful
   (implies (and (equal (l p) n)
		 (m-matrixp (l p) (c p) p))
	    (m-= (m-* (m-id n) p) p))
   :hints (("Goal"
	    :use ((:instance acl2::id-*-x
			     (acl2::n (l p))
			     (acl2::n2 (c p))
			     (acl2::p p)))
	    :in-theory (disable acl2::id-*-x))))

(defthm x-*-id-useful
   (implies (and (equal (c p) n)
		 (m-matrixp (l p) (c p) p))
	    (m-= (m-* p (m-id n)) p))
   :hints (("Goal"
	    :use ((:instance acl2::x-*-id
			     (acl2::m (l p))
			     (acl2::n (c p))
			     (acl2::p p)))
	    :in-theory (disable acl2::x-*-id))))

(encapsulate
 ()

 (local
  (defthm lemma-1
    (m-= (m-- (x k) (xhat k))
	 (m-- (m-* (m-- (m-id (n))
			(m-* (gain k) (h k)))
		   (m-- (x k) (xhatmin k)))
	      (m-* (gain k)
		   (v k))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance acl2::id-*-x
			      (acl2::p (x k))
			      (acl2::n (n))
			      (acl2::n2 1))
		   (:instance acl2::id-*-x
			      (acl2::p (xhatmin k))
			      (acl2::n (n))
			      (acl2::n2 1)))
	     :in-theory (disable acl2::id-*-x)))
    :rule-classes nil))


 (local
  (defthm lemma-2a
    (implies (and (equal (l a) (l b))
		  (equal (c a) (c b))
		  (m-matrixp (l b) (c b) b)
		  (m-matrixp (l a) (c a) a))
	     (m-= (m-* (m-- a b)
		       (m-trans (m-- a b)))
		  (m-+ (m-* a (m-trans a))
		       (m-+ (m-unary-- (m-* a (m-trans b)))
			    (m-+ (m-unary-- (m-* b (m-trans a)))
				 (m-* b (m-trans b)))))))
    :hints (("Goal"
	     :use ((:instance acl2::unary---unary--
			      (acl2::p (m-* b (m-trans b)))))
	     :in-theory (disable acl2::unary---unary--)))
    :rule-classes nil))

 (local
  (defthm lemma-2
    (m-= (m-* (m-- (x k) (xhat k))
	      (m-trans (m-- (x k) (xhat k))))
	 (m-+ (m-* (m-- (m-id (n))
			(m-* (gain k) (h k)))
		   (m-* (m-* (m-- (x k) (xhatmin k))
			     (m-trans (m-- (x k) (xhatmin k))))
			(m-trans (m-- (m-id (n))
				      (m-* (gain k) (h k))))))
	      (m-+ (m-unary-- (m-* (m-- (m-id (n))
					(m-* (gain k) (h k)))
				   (m-* (m-* (m-- (x k) (xhatmin k))
					     (m-trans (v k)))
					(m-trans (gain k)))))
		   (m-+ (m-unary-- (m-* (gain k)
					(m-* (m-* (v k)
						  (m-trans (m-- (x k) (xhatmin k))))
					     (m-trans (m-- (m-id (n))
							   (m-* (gain k) (h k)))))))
			(m-* (gain k)
			     (m-* (m-* (v k)
				       (m-trans (v k)))
				  (m-trans (gain k))))))))
    :hints (("Goal"
	     :use ((:instance lemma-1)
		   (:instance lemma-2a
			      (a (m-* (m-- (m-id (n))
					   (m-* (gain k) (h k)))
				      (m-- (x k) (xhatmin k))))
			      (b (m-* (gain k)
				      (v k)))))
	     :in-theory (disable x xhat xhatmin
				 gain-recdef pplus-recdef xhatmin-recdef
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))
    :rule-classes nil))


 (local
  (defthm lemma-3a1
    (and (equal (l (m-- (x k) (xhatmin k))) (n))
	 (equal (c (m-- (m-id (n)) (m-* (gain k) (h k)))) (n)))))

 (local
  (defthm lemma-3a
    (m-= (m-mean (ACL2::M-BINARY-*
		  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
				    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
		  (ACL2::M-BINARY-*
		   (ACL2::M-BINARY-+ (X K)
				     (ACL2::M-UNARY-- (XHATMIN K)))
		   (ACL2::M-BINARY-*
		    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
				      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
		    (ACL2::M-BINARY-+
		     (ACL2::M-1 (N))
		     (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
							(ACL2::M-TRANS (GAIN K)))))))))
	 (m-* (m-- (m-id (n))
		   (m-* (gain k) (h k)))
	      (m-* (m-mean (m-* (m-- (x k) (xhatmin k))
				(m-trans (m-- (x k) (xhatmin k)))))
		   (m-trans (m-- (m-id (n))
				 (m-* (gain k) (h k)))))))
    :hints (("Goal"
	     :use ((:instance mean-*
			      (p (m-- (m-id (n))
				      (m-* (gain k) (h k))))
			      (q (m-* (m-- (x k) (xhatmin k))
				      (m-* (m-trans (m-- (x k) (xhatmin k)))
					   (m-trans (m-- (m-id (n))
							 (m-* (gain k) (h k))))))))
		   (:instance mean-*
			      (p (m-* (m-- (x k) (xhatmin k))
				      (m-trans (m-- (x k) (xhatmin k)))))
			      (q (m-trans (m-- (m-id (n))
					       (m-* (gain k) (h k))))))
		   (:instance mean-delete
			      (p (m-id (n))))
		   (:instance mean-delete
			      (p (m-* (gain k) (h k)))))
	     :in-theory (disable x xhatmin gain gain-recdef
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
					;acl2::trans-* acl2::trans-+ acl2::trans---
				 )))))

 (local
  (defthm lemma-3b
    (m-= (m-mean (ACL2::M-UNARY--
		  (ACL2::M-BINARY-*
		   (ACL2::M-BINARY-+ (ACL2::M-1 (N))
				     (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
		   (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
						       (ACL2::M-UNARY-- (XHATMIN K)))
				     (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
						       (ACL2::M-TRANS (GAIN K)))))))
	 (m-zero (n) (n)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance mean-*
			      (p (m-- (m-id (n))
				      (m-* (gain k) (h k))))
			      (q (m-* (m-* (m-- (x k) (xhatmin k))
					   (m-trans (v k)))
				      (m-trans (gain k)))))
		   (:instance mean-*
			      (p (m-* (m-- (x k) (xhatmin k))
				      (m-trans (v k))))
			      (q (m-trans (gain k))))
		   (:instance mean-of-x-xhatmin*vtrans))
	     :in-theory (disable mean-of-x-xhatmin*vtrans
				 mean-+
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 )))))

 (local
  (defthm lemma-3c
    (m-=  (M-MEAN
	   (ACL2::M-UNARY--
	    (ACL2::M-BINARY-*
	     (GAIN K)
	     (ACL2::M-BINARY-*
	      (V K)
	      (ACL2::M-BINARY-*
	       (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
				 (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	       (ACL2::M-BINARY-+
		(ACL2::M-1 (N))
		(ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						   (ACL2::M-TRANS (GAIN K))))))))))


	  (m-zero (n) (n)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance mean-*
			      (p (gain k))
			      (q (m-* (m-* (v k)
					   (m-trans (m-- (x k) (xhatmin k))))
				      (m-trans (m-- (m-id (n))
						    (m-* (gain k) (h k)))))))
		   (:instance mean-*
			      (p (m-* (v k)
				      (m-trans (m-- (x k) (xhatmin k)))))
			      (q (m-trans (m-- (m-id (n))
					       (m-* (gain k) (h k))))))
		   (:instance mean-of-v*trans-of-x-xhatmin))
	     :in-theory (disable mean-of-v*trans-of-x-xhatmin
				 mean-+
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 )))))


 (local
  (defthm lemma-3d
    (equal (m-mean (m-* (gain k)
			(m-* (v k)
			     (m-* (m-trans (v k))
				  (m-trans (gain k))))))
	   (m-* (gain k)
		(m-* (r k)
		     (m-trans (gain k)))))
    :hints (("Goal"
	     :use ((:instance mean-*
			      (p (gain k))
			      (q (m-* (m-* (v k)
					   (m-trans (v k)))
				      (m-trans (gain k)))))
		   (:instance mean-*
			      (p (m-* (v k)
				      (m-trans (v k))))
			      (q (m-trans (gain k))))
		   (:instance mean-delete
			      (p (gain k))))
	     :in-theory (disable gain gain-recdef)))))




 (local
  (defthm lemma-3e

    (EQUAL
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-*
	(GAIN K)
	(ACL2::M-BINARY-* (V K)
			  (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					    (ACL2::M-TRANS (GAIN K)))))))
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-+
	(ACL2::M-UNARY--
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
					      (ACL2::M-UNARY-- (XHATMIN K)))
			    (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					      (ACL2::M-TRANS (GAIN K))))))
	(ACL2::M-BINARY-+
	 (ACL2::M-UNARY--
	  (ACL2::M-BINARY-*
	   (GAIN K)
	   (ACL2::M-BINARY-*
	    (V K)
	    (ACL2::M-BINARY-*
	     (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			       (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	     (ACL2::M-BINARY-+
	      (ACL2::M-1 (N))
	      (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						 (ACL2::M-TRANS (GAIN K)))))))))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (X K)
			     (ACL2::M-UNARY-- (XHATMIN K)))
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	    (ACL2::M-BINARY-+
	     (ACL2::M-1 (N))
	     (ACL2::M-UNARY--
	      (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
				(ACL2::M-TRANS (GAIN K)))))))))))))
    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-3f

    (EQUAL
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-*
	(GAIN K)
	(ACL2::M-BINARY-* (V K)
			  (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					    (ACL2::M-TRANS (GAIN K)))))))
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-+
	(ACL2::M-UNARY--
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
					      (ACL2::M-UNARY-- (XHATMIN K)))
			    (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					      (ACL2::M-TRANS (GAIN K))))))
	(ACL2::M-BINARY-+
	 (ACL2::M-UNARY--
	  (ACL2::M-BINARY-*
	   (GAIN K)
	   (ACL2::M-BINARY-*
	    (V K)
	    (ACL2::M-BINARY-*
	     (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			       (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	     (ACL2::M-BINARY-+
	      (ACL2::M-1 (N))
	      (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						 (ACL2::M-TRANS (GAIN K)))))))))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (X K)
			     (ACL2::M-UNARY-- (XHATMIN K)))
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	    (ACL2::M-BINARY-+
	     (ACL2::M-1 (N))
	     (ACL2::M-UNARY--
	      (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
				(ACL2::M-TRANS (GAIN K)))))))))))))
    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-3g

    (EQUAL
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-UNARY--
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	 (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
					     (ACL2::M-UNARY-- (XHATMIN K)))
			   (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					     (ACL2::M-TRANS (GAIN K))))))))
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-+
	(ACL2::M-UNARY--
	 (ACL2::M-BINARY-*
	  (GAIN K)
	  (ACL2::M-BINARY-*
	   (V K)
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	    (ACL2::M-BINARY-+
	     (ACL2::M-1 (N))
	     (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						(ACL2::M-TRANS (GAIN K)))))))))
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (X K)
			    (ACL2::M-UNARY-- (XHATMIN K)))
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			     (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	   (ACL2::M-BINARY-+
	    (ACL2::M-1 (N))
	    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					       (ACL2::M-TRANS (GAIN K))))))))))))

    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-3h

    (EQUAL
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-UNARY--
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	 (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
					     (ACL2::M-UNARY-- (XHATMIN K)))
			   (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					     (ACL2::M-TRANS (GAIN K))))))))
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-+
	(ACL2::M-UNARY--
	 (ACL2::M-BINARY-*
	  (GAIN K)
	  (ACL2::M-BINARY-*
	   (V K)
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	    (ACL2::M-BINARY-+
	     (ACL2::M-1 (N))
	     (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						(ACL2::M-TRANS (GAIN K)))))))))
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (X K)
			    (ACL2::M-UNARY-- (XHATMIN K)))
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			     (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	   (ACL2::M-BINARY-+
	    (ACL2::M-1 (N))
	    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					       (ACL2::M-TRANS (GAIN K))))))))))))

    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-3i

    (EQUAL
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-UNARY--
	(ACL2::M-BINARY-*
	 (GAIN K)
	 (ACL2::M-BINARY-*
	  (V K)
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			     (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	   (ACL2::M-BINARY-+
	    (ACL2::M-1 (N))
	    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					       (ACL2::M-TRANS (GAIN K)))))))))))
     (CAR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-*
	(ACL2::M-BINARY-+ (ACL2::M-1 (N))
			  (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (X K)
			   (ACL2::M-UNARY-- (XHATMIN K)))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			    (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	  (ACL2::M-BINARY-+
	   (ACL2::M-1 (N))
	   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					      (ACL2::M-TRANS (GAIN K)))))))))))

    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-3j

    (EQUAL
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-UNARY--
	(ACL2::M-BINARY-*
	 (GAIN K)
	 (ACL2::M-BINARY-*
	  (V K)
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			     (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	   (ACL2::M-BINARY-+
	    (ACL2::M-1 (N))
	    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					       (ACL2::M-TRANS (GAIN K)))))))))))
     (CADR
      (DIMENSIONS
       'ACL2::$ARG
       (ACL2::M-BINARY-*
	(ACL2::M-BINARY-+ (ACL2::M-1 (N))
			  (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (X K)
			   (ACL2::M-UNARY-- (XHATMIN K)))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			    (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	  (ACL2::M-BINARY-+
	   (ACL2::M-1 (N))
	   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					      (ACL2::M-TRANS (GAIN K)))))))))))

    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))



 (local
  (defthm lemma-3k

    (ACL2::M-=
     (ACL2::M-BINARY-+
      (ACL2::M-0 (N) (N))
      (ACL2::M-BINARY-+
       (ACL2::M-0 (N) (N))
       (ACL2::M-BINARY-+
	(ACL2::M-BINARY-* (GAIN K)
			  (ACL2::M-BINARY-* (R K)
					    (ACL2::M-TRANS (GAIN K))))
	(ACL2::M-BINARY-*
	 (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			   (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	 (ACL2::M-BINARY-*
	  (M-MEAN
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (X K)
			      (ACL2::M-UNARY-- (XHATMIN K)))
	    (ACL2::M-TRANS (ACL2::M-BINARY-+ (X K)
					     (ACL2::M-UNARY-- (XHATMIN K))))))
	  (ACL2::M-TRANS
	   (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			     (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K)
								(H K))))))))))
     (ACL2::M-BINARY-+
      (ACL2::M-BINARY-* (GAIN K)
			(ACL2::M-BINARY-* (R K)
					  (ACL2::M-TRANS (GAIN K))))
      (ACL2::M-BINARY-*
       (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			 (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
       (ACL2::M-BINARY-*
	(M-MEAN
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (X K)
			    (ACL2::M-UNARY-- (XHATMIN K)))
	  (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			    (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))))
	(ACL2::M-BINARY-+
         (ACL2::M-1 (N))
         (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
                                            (ACL2::M-TRANS (GAIN K)))))))))

    :hints (("Goal"
	     :in-theory (disable gain gain-recdef x xhat xhatmin
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))


 (local
  (DEFTHM
    lemma-3l
    (ACL2::M-=
     (M-MEAN
      (ACL2::M-BINARY-+
       (ACL2::M-BINARY-*
	(GAIN K)
	(ACL2::M-BINARY-* (V K)
			  (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					    (ACL2::M-TRANS (GAIN K)))))
       (ACL2::M-BINARY-+
	(ACL2::M-UNARY--
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-* (ACL2::M-BINARY-+ (X K)
					      (ACL2::M-UNARY-- (XHATMIN K)))
			    (ACL2::M-BINARY-* (ACL2::M-TRANS (V K))
					      (ACL2::M-TRANS (GAIN K))))))
	(ACL2::M-BINARY-+
	 (ACL2::M-UNARY--
	  (ACL2::M-BINARY-*
	   (GAIN K)
	   (ACL2::M-BINARY-*
	    (V K)
	    (ACL2::M-BINARY-*
	     (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			       (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	     (ACL2::M-BINARY-+
	      (ACL2::M-1 (N))
	      (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
						 (ACL2::M-TRANS (GAIN K)))))))))
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			    (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
	  (ACL2::M-BINARY-*
	   (ACL2::M-BINARY-+ (X K)
			     (ACL2::M-UNARY-- (XHATMIN K)))
	   (ACL2::M-BINARY-*
	    (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			      (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))
	    (ACL2::M-BINARY-+
	     (ACL2::M-1 (N))
	     (ACL2::M-UNARY--
	      (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
				(ACL2::M-TRANS (GAIN K))))))))))))
     (ACL2::M-BINARY-+
      (ACL2::M-BINARY-* (GAIN K)
			(ACL2::M-BINARY-* (R K)
					  (ACL2::M-TRANS (GAIN K))))
      (ACL2::M-BINARY-*
       (ACL2::M-BINARY-+ (ACL2::M-1 (N))
			 (ACL2::M-UNARY-- (ACL2::M-BINARY-* (GAIN K) (H K))))
       (ACL2::M-BINARY-*
	(M-MEAN
	 (ACL2::M-BINARY-*
	  (ACL2::M-BINARY-+ (X K)
			    (ACL2::M-UNARY-- (XHATMIN K)))
	  (ACL2::M-BINARY-+ (ACL2::M-TRANS (X K))
			    (ACL2::M-UNARY-- (ACL2::M-TRANS (XHATMIN K))))))
	(ACL2::M-BINARY-+
	 (ACL2::M-1 (N))
	 (ACL2::M-UNARY-- (ACL2::M-BINARY-* (ACL2::M-TRANS (H K))
					    (ACL2::M-TRANS (GAIN K)))))))))
    :INSTRUCTIONS
    ((:DV 1)
     (:REWRITE MEAN-+)
     (:CHANGE-GOAL NIL T)
     (:USE LEMMA-3E)
     (:USE LEMMA-3F)
     (:DV 1)
     (:REWRITE LEMMA-3D)
     :NX (:REWRITE MEAN-+)
     (:CHANGE-GOAL NIL T)
     (:USE LEMMA-3G)
     (:USE LEMMA-3H)
     (:DV 1)
     (:REWRITE LEMMA-3B)
     :NX (:REWRITE MEAN-+)
     (:CHANGE-GOAL NIL T)
     (:USE LEMMA-3I)
     (:USE LEMMA-3J)
     (:DV 1)
     (:REWRITE LEMMA-3C)
     :NX (:REWRITE LEMMA-3A)
     :TOP (:DV 1)
     (:REWRITE ACL2::COMMUTATIVITY-2-OF-M-+)
     (:DIVE 2) ; changed by Matt K. for v2-9 due to proof-builder DV fix for binops
     (:REWRITE ACL2::COMMUTATIVITY-2-OF-M-+)
     :TOP (:USE LEMMA-3K))))

 (local
  (defthm lemma-3
    (m-= (m-mean (m-* (m-- (x k) (xhat k))
		      (m-trans (m-- (x k) (xhat k)))))
	 (m-+ (m-* (m-- (m-id (n))
			(m-* (gain k) (h k)))
		   (m-* (m-mean (m-* (m-- (x k) (xhatmin k))
				     (m-trans (m-- (x k) (xhatmin k)))))
			(m-trans (m-- (m-id (n))
				      (m-* (gain k) (h k))))))
	      (m-* (gain k)
		   (m-* (r k)
			(m-trans (gain k))))))
    :hints (("Goal"
	     :use ((:instance lemma-2))
	     :in-theory (disable x xhat xhatmin
				 gain-recdef pplus-recdef xhatmin-recdef
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ))
	    ("Goal'4'"
	     :by (:instance lemma-3l)))
    :rule-classes nil))

 (local
  (defthm lemma-4
    (m-= (m-* (m-- (m-id (n))
		   (m-* (gain k) (h k)))
	      (m-* (pminus k)
		   (m-trans (m-- (m-id (n))
				 (m-* (gain k) (h k))))))
	 (m-+ (pminus k)
	      (m-+ (m-unary-- (m-* (gain k) (m-* (h k) (pminus k))))
		   (m-+ (m-unary-- (m-* (pminus k)
					(m-* (m-trans (h k))
					     (m-trans (gain k)))))
			(m-* (gain k)
			     (m-* (h k)
				  (m-* (pminus k)
				       (m-* (m-trans (h k))
					    (m-trans (gain k))))))))))
    :hints (("Goal" :do-not-induct t
	     :in-theory (disable gain gain-recdef
				 pminus pminus-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-5
    (m-= (m-+ (m-* (m-- (m-id (n))
			(m-* (gain k) (h k)))
		   (m-* (pminus k)
			(m-trans (m-- (m-id (n))
				      (m-* (gain k) (h k))))))
	      (m-* (gain k)
		   (m-* (r k)
			(m-trans (gain k)))))
	 (m-+ (pminus k)
	      (m-+ (m-unary-- (m-* (gain k) (m-* (h k) (pminus k))))
		   (m-+ (m-unary-- (m-* (pminus k)
					(m-* (m-trans (h k))
					     (m-trans (gain k)))))
			(m-+ (m-* (gain k)
				  (m-* (h k)
				       (m-* (pminus k)
					    (m-* (m-trans (h k))
						 (m-trans (gain k))))))
			     (m-* (gain k)
				  (m-* (r k)
				       (m-trans (gain k)))))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-4))
	     :in-theory (disable gain gain-recdef
				 pminus pminus-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-6
    (m-= (m-+ (m-* (gain k)
		   (m-* (h k)
			(m-* (pminus k)
			     (m-* (m-trans (h k))
				  (m-trans (gain k))))))
	      (m-* (gain k)
		   (m-* (r k)
			(m-trans (gain k)))))
	 (m-* (gain k)
	      (m-* (m-+ (m-* (h k) (m-* (pminus k) (m-trans (h k))))
			(r k))
		   (m-trans (gain k)))))
    :hints (("Goal"
	     :in-theory (disable gain gain-recdef pminus pminus-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-7a
    (implies (and (not (m-singular x))
		  (m-matrixp (l x) (c x) x)
		  (m-matrixp (l y) (c y) y)
		  (equal (c v) (l w))
		  (equal (c w) (l x))
		  (equal (c x) (l y)))
	     (m-= (m-* v
		       (m-* w
			    (m-* (m-inv x)
				 (m-* x y))))
		  (m-* v (m-* w y))))
    :hints (("Goal"
	     :use ((:instance acl2::assoc-*
			      (acl2::p (m-inv x))
			      (acl2::q x)
			      (acl2::r y))
		   (:instance acl2::inv-*-x
			      (acl2::p x)))
	     :in-theory (disable acl2::assoc-*
				 acl2::inv-*-x))
	    ("Goal'4'"
	     :in-theory (enable acl2::assoc-*)))))

 (local
  (defthm lemma-7
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (gain k)
			    (m-* (h k)
				 (m-* (pminus k)
				      (m-* (m-trans (h k))
					   (m-trans (gain k))))))
		       (m-* (gain k)
			    (m-* (r k)
				 (m-trans (gain k)))))
		  (m-* (pminus k)
		       (m-* (m-trans (h k)) (m-trans (gain k))))))
    :hints (("Goal"
	     :use ((:instance lemma-6))
	     :in-theory (disable gain pminus pminus-recdef
				 acl2::assoc-*
				 acl2::comm-+
				 ACL2::*-+-RIGHT
				 ACL2::*---RIGHT
				 ACL2::*-+-left
				 ACL2::*---left
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::left-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 acl2::COMMUTATIVITY-2-OF-M-+
				 ))
	    ("Goal'''"
	     :use (:theorem
		   (implies (and (integerp k) (<= 0 k))
			    (m-= (m-* (gain k)
				      (m-* (m-+ (m-* (h k)
						     (m-* (pminus k) (m-trans (h k))))
						(r k))
					   (m-trans (gain k))))
				 (m-* (pminus k)
				      (m-* (m-trans (h k))
					   (m-trans (gain k))))))))
	    ("Subgoal 1"
	     :in-theory (disable gain pminus pminus-recdef
					;acl2::comm-+
				 ACL2::*-+-RIGHT
				 ACL2::*---RIGHT
				 ACL2::*-+-left
				 ACL2::*---left
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::left-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 acl2::COMMUTATIVITY-2-OF-M-+
				 ))
	    )
    :rule-classes nil))

 (local
  (defthm lemma-8
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (m-- (m-id (n))
				 (m-* (gain k) (h k)))
			    (m-* (pminus k)
				 (m-trans (m-- (m-id (n))
					       (m-* (gain k) (h k))))))
		       (m-* (gain k)
			    (m-* (r k)
				 (m-trans (gain k)))))
		  (m-- (pminus k)
		       (m-* (gain k) (m-* (h k) (pminus k))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-5)
		   (:instance lemma-6)
		   (:instance lemma-7))
	     :in-theory (disable gain gain-recdef
				 pminus pminus-recdef
				 acl2::assoc-*
				 acl2::comm-+
				 ACL2::*-+-RIGHT
				 ACL2::*---RIGHT
				 ACL2::*-+-left
				 ACL2::*---left
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::left-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 acl2::COMMUTATIVITY-2-OF-M-+
				 acl2::trans-*
				 acl2::trans-+
				 acl2::trans---))
	    ("Goal'7'"
	     :by (:theorem
		  (m-= (m-+ (pminus k)
			    (m-+ (m-unary-- (m-* (gain k) (m-* (h k) (pminus k))))
				 (m-zero (n) (n))))
		       (m-- (pminus k)
			    (m-* (gain k)
				 (m-* (h k) (pminus k))))))
	     :in-theory (disable pminus pminus-recdef gain gain-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-9-for-lemma-10
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (m-- (m-id (n))
				 (m-* (gain k) (h k)))
			    (m-* (pminus k)
				 (m-trans (m-- (m-id (n))
					       (m-* (gain k) (h k))))))
		       (m-* (gain k)
			    (m-* (r k)
				 (m-trans (gain k)))))
		  (m-* (m-- (m-id (n))
			    (m-* (gain k) (h k)))
		       (pminus k))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-8))
	     :in-theory (disable pminus pminus-recdef gain gain-recdef)))
    :rule-classes nil))

 (local
  (defthm lemma-10
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (m-- (m-id (n))
				 (m-* (gain k) (h k)))
			    (m-* (pminus k)
				 (m-trans (m-- (m-id (n))
					       (m-* (gain k) (h k))))))
		       (m-* (gain k)
			    (m-* (r k)
				 (m-trans (gain k)))))
		  (pplus k)))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-9-for-lemma-10))
	     :in-theory (disable pminus pminus-recdef gain gain-recdef)))
    :rule-classes nil))

 (local
  (defthm pplus-as-mean-case-0
    (implies (equal k 0)
	     (m-= (pplus k)
		  (m-mean (m-* (m-- (x k) (xhat k))
			       (m-trans (m-- (x k) (xhat k)))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-3)
		   (:instance lemma-10)
		   (:instance pminus-as-mean-case-0))
	     :in-theory (disable pminus pminus-recdef gain gain-recdef)))
    :rule-classes nil))

 (local
  (defthm pplus-as-mean-almost
    (implies (and (integerp k)
		  (< 0 k)
		  (m-= (pplus (1- k))
		       (m-mean (m-* (m-- (x (1- k))
					 (xhat (1- k)))
				    (m-trans (m-- (x (1- k))
						  (xhat (1- k))))))))
	     (m-= (pplus k)
		  (m-mean (m-* (m-- (x k) (xhat k))
			       (m-trans (m-- (x k) (xhat k)))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-3)
		   (:instance lemma-10)
		   (:instance pminus-as-mean-almost))
	     :in-theory (disable gain gain-recdef
				 pminus pminus-recdef
				 acl2::assoc-*
				 acl2::comm-+
				 ACL2::*-+-RIGHT
				 ACL2::*---RIGHT
				 ACL2::*-+-left
				 ACL2::*---left
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::left-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 acl2::COMMUTATIVITY-2-OF-M-+
				 acl2::trans-*
				 acl2::trans-+
				 acl2::trans---)))
    :rule-classes nil))

 (local
  (defun natural-induction (n)
    (if (zp n)
	0
      (1+ (natural-induction (1- n))))))

 (defthm pplus-as-mean
   (implies (and (integerp k)
		 (<= 0 k))
	    (m-= (pplus k)
		 (m-mean (m-* (m-- (x k) (xhat k))
			      (m-trans (m-- (x k) (xhat k)))))))
   :hints (("Goal"
	    :induct (natural-induction k))
	   ("Subgoal *1/2"
	    :use ((:instance pplus-as-mean-almost)))
	   ("Subgoal *1/1"
	    :use ((:instance pplus-as-mean-case-0)))
	   ))

 )

(defthm pminus-as-mean
  (implies (and (integerp k) (<= 0 k))
	   (m-= (pminus k)
		(m-mean (m-* (m-- (x k) (xhatmin k))
			     (m-trans (m-- (x k) (xhatmin k)))))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance pminus-as-mean-almost)
		 (:instance pplus-as-mean (k (1- k))))
	   :in-theory (disable pminus-as-mean-almost pplus-as-mean
			       x xhat xhatmin
			       gain-recdef pplus-recdef xhatmin-recdef
			       (pminus) (x) (xhatmin)))))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (local
    (defthm lemma-0-1
      (implies (and (m-matrixp (l y) (c y) y)
		    (m-matrixp (l z) (c z) z)
		    (equal (c x) (l y))
		    (equal (c y) (l z)))
	       (equal (m-* x (m-mean (m-* y z)))
		      (m-mean (m-* (m-* x y) z))))
      :hints (("Goal"
	       :use ((:instance mean-*
				(p x)
				(q (m-* y z)))
		     (:instance mean-delete
				(p x)))))))

   (local
    (defthm lemma-0-2
      (implies (and (m-matrixp (l x) (c x) x)
		    (m-matrixp (l y) (c y) y)
		    (equal (c x) (l y))
		    (equal (c y) (l z)))
	       (equal (m-* (m-mean (m-* x y)) z)
		      (m-mean (m-* x (m-* y z)))))
      :hints (("Goal"
	       :use ((:instance mean-*
				(p (m-* x y))
				(q z))
		     (:instance mean-delete
				(p z)))))))

   (defthm lemma-0
     (implies (and (integerp k) (<= 0 k))
	      (m-= (m-* (pminus k) (m-trans (h k)))
		   (m-mean (m-* (m-- (x k) (xhatmin k))
				(m-trans (m-- (m-* (h k) (x k))
					      (m-* (h k) (xhatmin k))))))))
     :hints (("Goal" :do-not-induct t
	      :use ((:instance pminus-as-mean))
	      :in-theory (disable pplus-as-mean pminus-as-mean))))


   (defthm lemma-1
     (implies (and (integerp k) (<= 0 k))
	      (m-= (m-* (h k) (m-* (pminus k) (m-trans (h k))))
		   (m-mean (m-* (m-- (m-* (h k) (x k))
				     (m-* (h k) (xhatmin k)))
				(m-trans (m-- (m-* (h k) (x k))
					      (m-* (h k) (xhatmin k)))))))))
   ))

 (local
  (encapsulate
   ()

   (local
    (defthm lemma-2-1
      (equal (l (m-* (v k) (m-trans (v k))))
	     (l (m-* (m-- (m-* (h k) (x k))
			  (m-* (h k) (xhatmin k)))
		     (m-trans (m-- (m-* (h k) (x k))
				   (m-* (h k) (xhatmin k)))))))))

   (local
    (defthm lemma-2-2
      (equal (c (m-* (v k) (m-trans (v k))))
	     (c (m-* (m-- (m-* (h k) (x k))
			  (m-* (h k) (xhatmin k)))
		     (m-trans (m-- (m-* (h k) (x k))
				   (m-* (h k) (xhatmin k)))))))))

   (defthm lemma-2
     (implies (and (integerp k) (<= 0 k))
	      (m-= (m-+ (m-* (h k)
			     (m-* (pminus k) (m-trans (h k))))
			(m-mean (m-* (v k) (m-trans (v k)))))
		   (m-mean (m-+ (m-* (m-- (m-* (h k) (x k))
					  (m-* (h k) (xhatmin k)))
				     (m-trans (m-- (m-* (h k) (x k))
						   (m-* (h k) (xhatmin k)))))
				(m-* (v k) (m-trans (v k)))))))
     :hints (("Goal" :do-not-induct t
	      :in-theory '(lemma-1 mean-+ lemma-2-1 lemma-2-2
				   acl2::m-=-implies-equal-m-+-1))))

   ))

 (local
  (defthm lemma-3
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (h k)
			    (m-* (pminus k)
				 (m-trans (h k))))
		       (r k))
		  (m-mean (m-+ (m-* (m-- (m-* (h k) (x k))
					 (m-* (h k) (xhatmin k)))
				    (m-trans (m-- (m-* (h k) (x k))
						  (m-* (h k) (xhatmin k)))))
			       (m-* (v k) (m-trans (v k)))))))
    :hints (("Goal"
	     :use ((:instance mean-of-v-vtrans)
		   (:instance lemma-2))
	     :in-theory '(acl2::m-=-implies-equal-m-+-2)))))

 (local
  (encapsulate
   nil

   (local
    (defthm lemma-4-1
      (implies (and (m-matrixp (l a) (c a) a)
		    (m-matrixp (l b) (c b) b)
		    (equal (l a) (l b))
		    (equal (c a) (c b)))
	       (m-= (m-mean (m-* (m-+ a b) (m-trans (m-+ a b))))
		    (m-+ (m-mean (m-* a (m-trans a)))
			 (m-+ (m-mean (m-* a (m-trans b)))
			      (m-+ (m-mean (m-* b (m-trans a)))
				   (m-mean (m-* b (m-trans b))))))))))

   (local
    (defthm lemma-4-2
      (m-= (m-mean (m-* (m-- (m-* (h k) (x k))
			     (m-* (h k) (xhatmin k)))
			(m-trans (v k))))
	   (m-zero (m) (m)))
      :hints (("Goal" :do-not-induct t
	       :use ((:instance mean-of-x-xhatmin*vtrans)
		     (:instance acl2::x-*-zero
				(acl2::p (h k))
				(acl2::m (n))
				(acl2::n (m)))
		     (:instance acl2::*-+-right
				(acl2::p (h k))
				(acl2::q (m-* (x k) (m-trans (v k))))
				(acl2::r (m-* (m-unary-- (xhatmin k))
					      (m-trans (v k)))))
		     (:instance mean-*
				(p (h k))
				(q (m-* (m-- (x k) (xhatmin k))
					(m-trans (v k)))))
		     (:instance mean-delete
				(p (h k))))
	       :in-theory (disable mean-of-x-xhatmin*vtrans
				   acl2::x-*-zero
				   acl2::*-+-right)))))

   (local
    (defthm lemma-4-3
      (m-= (m-mean (m-* (v k)
			(m-trans (m-- (m-* (h k) (x k))
				      (m-* (h k) (xhatmin k))))))
	   (m-zero (m) (m)))
      :hints (("Goal" :do-not-induct t
	       :use ((:instance mean-of-v*trans-of-x-xhatmin)
		     (:instance acl2::zero-*-x
				(acl2::p (m-trans (h k)))
				(acl2::m (m))
				(acl2::n (n)))
		     (:instance mean-*
				(p (m-* (v k)
					(m-trans (m-- (x k) (xhatmin k)))))
				(q (m-trans (h k))))
		     (:instance mean-delete
				(p (m-trans (h k)))))
	       :in-theory (disable mean-of-v*trans-of-x-xhatmin
				   acl2::*-+-left
				   acl2::*-+-right
				   acl2::*---left
				   acl2::*---right
				   ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				   ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				   acl2::x-*-zero))
	      ("Goal'7'"
	       :use ((:theorem
		      (IMPLIES (m-= (m-mean (m-* (v k)
						 (m-* (m-- (m-trans (x k))
							   (m-trans (xhatmin k)))
						      (m-trans (h k)))))
				    (m-* (m-zero (m) (n))
					 (m-trans (h k))))
			       (m-= (m-mean (m-* (v k)
						 (m-- (m-* (m-trans (x k))
							   (m-trans (h k)))
						      (m-* (m-trans (xhatmin k))
							   (m-trans (h k))))))
				    (m-zero (m) (m)))))))
	      ("Subgoal 1"
	       :in-theory (enable acl2::*-+-left)))))

   (defthm lemma-4
     (m-= (m-mean (m-* (m-+ (m-- (m-* (h k) (x k))
				 (m-* (h k) (xhatmin k)))
			    (v k))
		       (m-trans (m-+ (m-- (m-* (h k) (x k))
					  (m-* (h k) (xhatmin k)))
				     (v k)))))
	  (m-mean (m-+ (m-* (m-- (m-* (h k) (x k))
				 (m-* (h k) (xhatmin k)))
			    (m-trans (m-- (m-* (h k) (x k))
					  (m-* (h k) (xhatmin k)))))
		       (m-* (v k) (m-trans (v k))))))
     :hints (("Goal" :do-not-induct t
	      :use ((:instance lemma-4-1
			       (a (m-- (m-* (h k) (x k))
				       (m-* (h k) (xhatmin k))))
			       (b (v k))))
	      :in-theory (disable lemma-4-1
				  xhatmin-recdef
				  mean-of-v-vtrans
				  mean-unary--
				  acl2::trans-*
				  acl2::trans-+
				  acl2::assoc-*
				  acl2::assoc-+
				  acl2::comm-+
				  acl2::*-+-left
				  acl2::*---left
				  ))))
   ))

 (local
  (encapsulate
   ()

   (local
    (defthm lemma-5-1
      (implies (and (equal (l a) (l b))
		    (equal (c a) (c b))
		    (equal (l b) (l c))
		    (equal (c b) (c c)))
	       (m-= (m-+ b (m-+ a c))
		    (m-+ a (m-+ b c))))
      :hints (("Goal"
	       :use ((:instance acl2::assoc-+
				(acl2::p b)
				(acl2::q a)
				(acl2::r c))
		     (:instance acl2::assoc-+
				(acl2::p a)
				(acl2::q b)
				(acl2::r c)))
	       :in-theory (disable acl2::assoc-+)))))

   (defthm lemma-5
     (m-= (m-+ (m-- (m-* (h k) (x k))
		    (m-* (h k) (xhatmin k)))
	       (v k))
	  (m-- (z k) (m-* (h k) (xhatmin k))))
     :hints (("Goal" :do-not-induct t)))
   ))

 (local
  (defthm lemma-6
    (m-= (m-mean (m-* (m-- (z k) (m-* (h k) (xhatmin k)))
		      (m-trans (m-- (z k) (m-* (h k) (xhatmin k))))))
	 (m-mean (m-+ (m-* (m-- (m-* (h k) (x k))
				(m-* (h k) (xhatmin k)))
			   (m-trans (m-- (m-* (h k) (x k))
					 (m-* (h k) (xhatmin k)))))
		      (m-* (v k) (m-trans (v k))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-4)
		   (:instance lemma-5))
	     :in-theory (disable lemma-4
				 lemma-5
				 z
				 xhatmin
				 x
				 mean-+
				 acl2::assoc-+
				 acl2::comm-+
				 acl2::commutativity-2-of-m-+
				 acl2::trans-*
				 acl2::trans-+
				 acl2::trans---
				 acl2::*-+-left
				 acl2::*-+-right
				 acl2::*---left
				 acl2::*---right
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-7
    (implies (and (integerp k) (<= 0 k))
	     (m-= (m-+ (m-* (h k)
			    (m-* (pminus k)
				 (m-trans (h k))))
		       (r k))
		  (m-mean (m-* (m-- (z k) (m-* (h k) (xhatmin k)))
			       (m-trans (m-- (z k) (m-* (h k) (xhatmin k))))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-3)
		   (:instance lemma-6))
	     :in-theory (disable lemma-3
				 lemma-6
				 z
				 xhatmin
				 x
				 mean-+
				 acl2::assoc-+
				 acl2::comm-+
				 acl2::commutativity-2-of-m-+
				 acl2::trans-*
				 acl2::trans-+
				 acl2::trans---
				 acl2::*-+-left
				 acl2::*-+-right
				 acl2::*---left
				 acl2::*---right
				 ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				 ACL2::RIGHT-DISTRIBUTIVITY-OF-M-*-OVER-M-+)))))

 (local
  (defthm lemma-8
    (implies (and (integerp k) (<= 0 k))
	     (m-= (s-* 2 (m-* (gain k)
			      (m-mean (m-* (m-- (z k)
						(m-* (h k) (xhatmin k)))
					   (m-trans (m-- (z k)
							 (m-* (h k) (xhatmin k))))))))
		  (s-* 2 (m-* (pminus k) (m-trans (h k))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-7)
		   (:instance gain-recdef))
	     :in-theory (disable lemma-0 lemma-1 lemma-3 lemma-7
				 gain-recdef
				 z
				 acl2::*-+-right
				 acl2::*-+-left
				 acl2::*---right
				 acl2::*---left
				 acl2::assoc-+
				 acl2::comm-+
				 acl2::left-distributivity-of-m-*-over-m-+
				 acl2::right-distributivity-of-m-*-over-m-+
				 pminus-as-mean))
	    ("Goal'5'"
	     :by (:theorem
		  (implies (and (integerp k) (<= 0 k))
			   (m-= (s-* 2 (m-* (pminus k)
					    (m-* (m-trans (h k))
						 (m-* (m-inv (m-+
							      (m-* (h k)
								   (m-* (pminus k)
									(m-trans (h k))))
							      (r k)))
						      (m-+
						       (m-* (h k)
							    (m-* (pminus k)
								 (m-trans (h k))))
						       (r k))))))
				(s-* 2
				     (m-* (pminus k)
					  (m-trans (h k))))))))
	    ("Goal'6'"
	     :use ((:instance acl2::inv-*-x
			      (acl2::p (m-+ (r k)
					    (m-* (h k)
						 (m-* (pminus k)
						      (m-trans (h k))))))))
	     :in-theory (disable lemma-0 lemma-1 lemma-3 lemma-7
				 z
				 acl2::inv-*-x
				 acl2::*-+-left
				 acl2::*-+-right
				 acl2::*---left
				 acl2::*---right
				 acl2::assoc-*
				 acl2::assoc-+
					;acl2::comm-+
				 acl2::k-*---p
				 acl2::k-*-x-+-y
				 mean-+
				 mean-of-v-vtrans
				 mean-unary--
				 acl2::trans-*
				 acl2::trans-+
				 acl2::unary---+
				 pminus-as-mean)))))

 (local
  (defthm lemma-9
    (implies (and (integerp k) (<= 0 k))
	     (m-= (s-* 2 (m-* (gain k)
			      (m-mean (m-* (m-- (z k)
						(m-* (h k) (xhatmin k)))
					   (m-trans (m-- (z k)
							 (m-* (h k) (xhatmin k))))))))
		  (s-* 2 (m-mean (m-* (m-- (x k) (xhatmin k))
				      (m-trans (m-- (m-* (h k) (x k))
						    (m-* (h k) (xhatmin k)))))))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance lemma-0)
		   (:instance lemma-8))
	     :in-theory (disable lemma-0 lemma-8
				 gain gain-recdef
				 z
				 xhatmin
				 x
				 )
	     ))))

 (local
  (encapsulate
   ()

   (local
    (defthm lemma-10-1
      (implies (and (equal (l a) (l b))
		    (equal (c a) (c b))
		    (equal (l b) (l c))
		    (equal (c b) (c c)))
	       (m-= (m-+ b (m-+ a c))
		    (m-+ a (m-+ b c))))
      :hints (("Goal"
	       :use ((:instance acl2::assoc-+
				(acl2::p b)
				(acl2::q a)
				(acl2::r c))
		     (:instance acl2::assoc-+
				(acl2::p a)
				(acl2::q b)
				(acl2::r c)))
	       :in-theory (disable acl2::assoc-+)))))

   (local
    (defthm lemma-10-2
      (equal (m-- (z k) (m-* (h k) (xhatmin k)))
	     (m-+ (m-* (h k) (m-- (x k) (xhatmin k))) (v k)))
      :hints (("Goal" :do-not-induct t))
      ))

   (local
    (defthm lemma-10-3
      (m-= (m-trans (m-- (z k) (m-* (h k) (xhatmin k))))
	   (m-+ (m-trans (m-- (m-* (h k) (x k))
			      (m-* (h k) (xhatmin k))))
		(m-trans (v k))))
      :hints (("Goal" :do-not-induct t))))

   (local
    (defthm lemma-10-4
      (m-= (m-mean (m-* (m-- (xhatmin k) (x k))
			(m-trans (m-- (z k)
				      (m-* (h k) (xhatmin k))))))
	   (m-mean (m-* (m-- (xhatmin k) (x k))
			(m-trans (m-- (m-* (h k) (x k))
				      (m-* (h k) (xhatmin k)))))))
      :hints (("Goal" :do-not-induct t
	       :in-theory (disable MEAN-UNARY--
				   z
				   mean-+
				   acl2::trans---
				   acl2::trans-+
				   acl2::trans-*
				   lemma-10-1
				   lemma-10-2
				   acl2::*-+-left
				   acl2::*---left
				   acl2::*-+-right
				   acl2::*---right
				   acl2::left-distributivity-of-m-*-over-m-+
				   acl2::right-distributivity-of-m-*-over-m-+
				   acl2::comm-+
				   ))


	      ("Goal'"
	       :use ((:instance acl2::*-+-right
				(acl2::p (M-- (XHATMIN K) (X K)))
				(acl2::q (M-TRANS (M-- (M-* (H K) (X K))
						       (M-* (H K) (XHATMIN K)))))
				(acl2::r (M-TRANS (V K)))))
	       :in-theory (disable z
				   MEAN-UNARY--
				   mean-+
				   acl2::trans---
				   acl2::trans-+
				   acl2::trans-*
				   acl2::*-+-right
				   acl2::*---right
				   acl2::*-+-left
				   acl2::*---left
				   acl2::comm-+
				   acl2::left-distributivity-of-m-*-over-m-+
				   acl2::right-distributivity-of-m-*-over-m-+
				   ))

	      ("Goal'5'"
	       :by (:theorem
		    (m-=
		     (m-mean (m-+ (m-* (m-+ (xhatmin k) (m-unary-- (x k)))
				       (m-trans (m-+ (m-* (h k) (x k))
						     (m-unary-- (m-* (h k) (xhatmin k))))))
				  (m-* (m-+ (xhatmin k) (m-unary-- (x k)))
				       (m-trans (v k)))))
		     (m-mean (m-* (m-+ (xhatmin k) (m-unary-- (x k)))
				  (m-trans (m-+ (m-* (h k) (x k))
						(m-unary-- (m-* (h k) (xhatmin k))))))))))
	      ("Goal'6'"
	       :use ((:instance mean-of-x-xhatmin*vtrans)
		     (:instance mean-unary--
				(p (m-* (m-+ (x k)
					     (m-unary-- (xhatmin k)))
					(m-trans (v k)))))
		     (:theorem (m-= (m-unary-- (m-* (m-+ (x k)
							 (m-unary-- (xhatmin k)))
						    (m-trans (v k))))
				    (m-* (m-+ (xhatmin k) (m-unary-- (x k)))
					 (m-trans (v k))))))
	       :in-theory (disable mean-of-x-xhatmin*vtrans
				   mean-unary--))

	      ("Subgoal 2"
	       :use ((:instance M-=-IMPLIES-M-=-M-MEAN-1
				(x (m-* (m-- (xhatmin k) (x k))
					(m-trans (v k))))
				(x-equiv (m-unary-- (m-* (m-- (x k) (xhatmin k))
							 (m-trans (v k))))))
		     )
	       :in-theory (disable mean-of-x-xhatmin*vtrans
				   mean-unary--
				   lemma-10-1
				   acl2::*-+-left
				   acl2::*-+-right
				   acl2::*---left
				   acl2::*---right
					;acl2::comm-+
				   acl2::trans-*
				   acl2::trans-+
				   acl2::trans---
				   acl2::left-distributivity-of-m-*-over-m-+
				   acl2::right-distributivity-of-m-*-over-m-+
				   (:congruence M-=-IMPLIES-M-=-M-MEAN-1)
				   ))
	      )))

   (local
    (defthm lemma-10-5
      (implies (and (m-matrixp (l a) (c a) a)
		    (m-matrixp (l b) (c b) b)
		    (equal (l a) (l b))
		    (equal (c a) (c b)))
	       (m-= (m-- b a)
		    (m-unary-- (m-- a b))))))


   (local
    (defthm lemma-10-6
      (implies (and (m-matrixp (l a) (c a) a)
		    (m-matrixp (l b) (c b) b)
		    (m-matrixp (l c) (c c) c)
		    (equal (l a) (l b))
		    (equal (c a) (c b))
		    (equal (c b) (l c)))
	       (m-= (m-unary-- (m-mean (m-* (m-- a b) c)))
		    (m-mean (m-* (m-- b a) c))))
      :hints (("Goal"
	       :use ((:instance lemma-10-5)
		     (:instance M-=-IMPLIES-M-=-M-MEAN-1
				(x (ACL2::M-BINARY-* (ACL2::M-BINARY-+ B (ACL2::M-UNARY-- A))
						     C))
				(x-equiv (m-* (m-unary-- (m-- a b)) c)))
		     )
	       :in-theory (disable lemma-10-5 acl2::unary---+ acl2::assoc-+
				   m-=-implies-m-=-m-mean-1))
	      ("Goal'4'"
	       :by (:theorem
		    (implies
		     (and (acl2::matrixp (car (dimensions 'acl2::$arg a))
					 (car (dimensions 'acl2::$arg c))
					 a)
			  (acl2::matrixp (car (dimensions 'acl2::$arg a))
					 (car (dimensions 'acl2::$arg c))
					 b)
			  (acl2::matrixp (car (dimensions 'acl2::$arg c))
					 (cadr (dimensions 'acl2::$arg c))
					 c))
		     (acl2::m-=
		      (acl2::m-unary--
		       (m-mean (acl2::m-binary-* (acl2::m-binary-+ a (acl2::m-unary-- b))
						 c)))
		      (m-mean (acl2::m-binary-*
			       (acl2::m-unary-- (acl2::m-binary-+ a (acl2::m-unary-- b)))
			       c)))))
	       :in-theory (disable lemma-10-5 acl2::unary---+ acl2::assoc-+)))))

   (defthm lemma-10
     (m-= (m-mean (m-* (m-- (xhatmin k) (x k))
		       (m-trans (m-- (z k)
				     (m-* (h k) (xhatmin k))))))
	  (m-unary-- (m-mean (m-* (m-- (x k) (xhatmin k))
				  (m-trans (m-- (m-* (h k) (x k))
						(m-* (h k) (xhatmin k))))))))
     :hints (("Goal" :do-not-induct t
	      :use ((:instance lemma-10-4)
		    (:instance lemma-10-6
			       (a (xhatmin k))
			       (b (x k))
			       (c (m-trans (m-- (m-* (h k) (x k))
						(m-* (h k) (xhatmin k))))))
		    )
	      :in-theory (disable lemma-10-2
				  lemma-10-3
				  lemma-10-4
				  lemma-10-5
				  lemma-10-6
				  z
				  mean-unary--
				  acl2::*---left
				  acl2::*---right
				  acl2::*-+-left
				  acl2::*-+-right
				  acl2::unary---+
				  acl2::trans-*
				  acl2::trans-+
				  acl2::trans---
				  acl2::comm-+
				  acl2::assoc-+
				  ACL2::LEFT-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				  ACL2::right-DISTRIBUTIVITY-OF-M-*-OVER-M-+
				  mean-+))))
   ))

 (defthm gain-minimizes-error
   (implies (and (integerp k) (<= 0 k))
	    (m-= (result-form-derivative (gain k) (xhatmin k) k)
		 (m-zero (n) (m))))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance lemma-9)
		  (:instance lemma-10)
		  (:instance gain-recdef))
	    :in-theory (disable lemma-9
				lemma-10
				lemma-0
				lemma-1
				lemma-3
				lemma-6
				lemma-7
				lemma-8
				gain-recdef
				xhatmin-recdef
				acl2::assoc-+
				acl2::*-+-left
				acl2::*-+-right
				acl2::*---left
				acl2::*---right
				acl2::assoc-*
				acl2::comm-+
				z
				acl2::trans-*
				acl2::trans-+
				acl2::trans---
				pminus-recdef
					;MINUS-AS-PLUS-INVERSE
				))))
 )

(defthm xhatmin=best-prior-almost
  (implies (m-= (xhat (1- k))
		(best-estimate-of-x (1- k)))
	   (m-= (xhatmin k)
		(best-prior-estimate-of-x k)))
  :hints (("Goal" :do-not-induct t
	   :in-theory (disable xhat z)))
  :rule-classes nil)

(local
 (defun natural-induction (k)
   (if (zp k)
       1
     (1+ (natural-induction (1- k))))))

(defthm result-form-=-xhat
  (equal (result-form (gain k) (xhatmin k) k)
	 (xhat k)))

(defthm xhat=best-estimate
  (implies (and (integerp k)
		(<= 0 k))
	   (m-= (xhat k)
		(best-estimate-of-x k)))
  :hints (("Goal"
	   :induct (natural-induction k))
	  ("Subgoal *1/2"
	   :use ((:instance xhatmin=best-prior-almost)
		 (:instance best-estimate-of-x-def
			    (y (gain k))
			    (Xp (xhatmin k)))
		 (:instance gain-minimizes-error))
	   :in-theory (disable xhat))
	  ("Subgoal *1/1"
	   :use ((:instance best-estimate-of-x-def
			    (y (gain 0))
			    (Xp (xhatmin 0))
			    (k 0)))
	   :in-theory (disable gain-recdef
			       (best-prior-estimate-of-x)
			       (xhatmin)
			       (gain)
; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
                               (xhat)))
	  )
  :rule-classes nil)

(defthm xhatmin=best-prior
  (implies (and (integerp k)
                (<= 0 k))
	   (m-= (xhatmin k)
		(best-prior-estimate-of-x k)))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance xhatmin=best-prior-almost)
		 (:instance xhat=best-estimate (k (1- k))))
	   :in-theory '(best-prior-estimate-of-x zp)))
  :rule-classes nil)

