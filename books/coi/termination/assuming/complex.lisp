; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

#|

  A proof of the universal termination of tarai in the ACL2 logic.

  This work extends the measure given by Moore to handle complex
values (by Cowles) and subsequently all ACL2 objects (by Greve).

|#
(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)

;; This function is similar to RTL::fl.
;; Its domain is extended, so there are no hyps in fl-ext-t-def

(defund fl-ext (x)
  (if (and (integerp (realpart x)) (< (imagpart x) 0))
      (1- (realpart x))
      (floor (realpart x) 1)))

(local (defrule fl-ext-def
  (and
    (<= (fl-ext x) x)
    (< x (1+ (fl-ext x))))
  :prep-lemmas (
    (defrule lemma
      (implies (real/rationalp x) (equal (realpart x) x))))
  :prep-books ((include-book "arithmetic-5/top" :dir :system))
  :enable (fl-ext)
  :use ((:instance completion-of-<
          (x x)
          (y (fl-ext x)))
        (:instance completion-of-<
          (x x)
          (y (1+ (fl-ext x)))))
  :rule-classes :linear))

(include-book "compiler")
(include-book "ordinals/lexicographic-ordering" :dir :system)

;; This tarai-measure is similar to tarai-measure from zero.lisp .
;; However, it permits to prove tarai-always-terminate in ACL2(r)

(defun m1 (x y z)
  (declare (ignore z))
  (if (<= x y) 0 1))

(defun m2 (x y z)
  (fl-ext (- (max (max x y) z) (min (min x y) z))))

(defun m3 (x y z)
  (fl-ext (- x (min (min x y) z))))

(defun m4 (x y z)
  (declare (ignore x))
  (if (<= y z) 0 1))

(defun tarai-measure (x y z)
  (acl2::llist (m1 x y z) (m2 x y z) (m3 x y z) (m4 x y z)))

(defun tarai-open (x y z)
  (if (<= x y) y
    (if (<= y z) z
      x)))

(defun tarai-induction (x y z)
  (declare (xargs :measure (tarai-measure x y z)
		  :well-founded-relation acl2::l<))
  (cond
   ((> x y)
    (list
     (tarai-induction (tarai-open (1- x) y z)
		      (tarai-open (1- y) z x)
		      (tarai-open (1- z) x y))
     (tarai-induction (1- x) y z)
     (tarai-induction (1- y) z x)
     (tarai-induction (1- z) x y)))
   (t y)))

(defthm open-tarai_terminates_closed
  (equal (tarai_terminates-closed x y z)
	 (tarai_terminates x y z))
  :hints (("Goal" :in-theory (enable
			      tarai_terminates-closed
			      tarai_terminates
			      tarai-5_terminates-call
			      ))))

(defrule tarai-always-terminates
  (tarai_terminates x y z)
  :induct (tarai-induction x y z))

;; It is problematic to extend the proof of tarai-always-terminate below to
;; real arguments in ACL2(r),
;; because it considers numerator/denominator of arguments.
#|
(encapsulate
    (
     ((tarai * * *) => *)
     ((tarai_terminates * * *) => *)
     )

  (local (include-book "compiler"))

  (local (in-theory (enable tarai_terminates-closed-open)))

  (defthm tarai_terminates-definition
    (equal (tarai_terminates x y z)
	   (if (> x y)
	       (and
		(tarai_terminates (1- x) y z)
		(tarai_terminates (1- y) z x)
		(tarai_terminates (1- z) x y)
		(tarai_terminates (tarai-open (1- x) y z)
				  (tarai-open (1- y) z x)
				  (tarai-open (1- z) x y)))
	     t))
    :rule-classes ((:definition :controller-alist ((tarai_terminates t t t)))))

  (defthm tarai_terminates_opener
    (implies
     (tarai_terminates x y z)
     (equal (tarai x y z)
	    (tarai-open x y z))))


  )

(include-book "ordinals/ordinal-definitions" :dir :system)

(encapsulate
    (
     ((l< * *) => *)
     ((d< * *) => *)
     ((ltoo *) => *)
     )

  (local (include-book "ordinals/lexicographic-ordering" :dir :system))

  (DEFUN LLIST-MACRO (LST)
    (DECLARE (XARGS :GUARD T))
    (IF (CONSP LST)
	(CONS (CONS 'NFIX (CONS (CAR LST) 'NIL))
	      (LLIST-MACRO (CDR LST)))
	NIL))

  (DEFMACRO LLIST (&REST LST)
    (CONS 'LIST (LLIST-MACRO LST)))

  (DEFUN NATP-LISTP (X)
    (DECLARE (XARGS :GUARD T))
    (COND ((ATOM X) (NULL X))
	  (T (AND (NATP (CAR X))
		  (NATP-LISTP (CDR X))))))

  (DEFUN LEXP (X)
    (DECLARE (XARGS :GUARD T))
    (OR (NATP X)
	(AND (CONSP X) (NATP-LISTP X))))

  (DEFthm D<-definition
    (equal (d< X Y)
	   (AND (CONSP X)
		(CONSP Y)
		(OR (< (CAR X) (CAR Y))
		    (AND (= (CAR X) (CAR Y))
			 (D< (CDR X) (CDR Y))))))
    :rule-classes (:definition))

  (DEfthm L<-definition
    (equal (l< x y)
	   (OR (< (LEN X) (LEN Y))
	       (AND (= (LEN X) (LEN Y))
		    (IF (ATOM X) (< X Y) (D< X Y)))))
    :rule-classes (:definition))

  (defthm well-founded-l<
    (and (implies (lexp x) (o-p (ltoo x)))
	 (implies (and (lexp x)
		       (lexp y)
		       (l< x y))
		  (o< (ltoo x) (ltoo y))))
    :rule-classes :well-founded-relation)

  )

(include-book "arithmetic-5/top" :dir :system)

(encapsulate
    ()

  (local
   (defthm hack0
     (implies (and (rationalp x)
		   (rationalp y)
		   (rationalp z))
	      (equal (* z (complex x y))
		     (complex (* x z) (* y z))))
     :hints (("goal" :use ((:instance complex-definition)
			   (:instance complex-definition (x (* x z))
				      (y (* y z)))))
	     ("goal'4'" :use ((:instance distributivity (x z)
					 (y x)
					 (z (* #c(0 1) y))))))))

  (defthm realpart-*
    (implies (rationalp y)
	     (and (equal (realpart (* y x))
			 (* y (realpart x)))
		  (equal (realpart (* x y))
			 (* y (realpart x))))))

  (defthm imagpart-*
    (implies (rationalp y)
	     (and (equal (imagpart (* y x))
			 (* y (imagpart x)))
		  (equal (imagpart (* x y))
			 (* y (imagpart x))))))

  )


(defun either-not-rationalp (x y)
  (or (not (rationalp x))
      (not (rationalp y))))

(defthm either-not-rationalp-1
  (implies
   (not (rationalp x))
   (either-not-rationalp x y)))

(defthm either-not-rationalp-2
  (implies
   (not (rationalp y))
   (either-not-rationalp x y)))

(defthm open-<
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (either-not-rationalp x y))
   (equal (< x y)
	  (or (< (realpart x) (realpart y))
	      (and (equal (realpart x) (realpart y))
		   (< (imagpart x) (imagpart y))))))
  :hints (("Goal" :use completion-of-<)))

(in-theory (disable either-not-rationalp))

(defthm acl2-numberp-reduction
  (iff (acl2-numberp x)
       (or (complex-rationalp x)
	   (rationalp x))))

(defun cc (x y)
  (let ((y (rfix y)))
    (if (equal y 0)
	(complex (rfix x) 1)
      (complex (rfix x) y))))

;; This rule appears to fight with REDUCE-MULTIPLICATIVE-CONSTANT-EQUA
;;(in-theory (disable EQUAL-/))

;; THis rule definately fights with |(- (* c x))|
;;(in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))

;; THis rule seems to fight with REDUCE-MULTIPLICATIVE-CONSTANT-<
;;(in-theory (disable <-UNARY-/-POSITIVE-LEFT))

;; More fighting ..
;;(in-theory (disable <-UNARY-/-NEGATIVE-RIGHT))

(defthm complex-rational-cc
  (complex-rationalp (cc x y))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((cc x y)))))

(defthm realpart-cc
  (equal (realpart (cc x y))
	 (rfix x)))

(defthm imagpart-cc
  (equal (imagpart (cc x y))
	 (let ((y (rfix y)))
	   (if (equal y 0) 1
	     y))))

(defthm complex-to-cc
  (equal (complex x y)
	 (if (equal (rfix y) 0) (rfix x)
	   (cc x y))))

(in-theory (disable cc))

(defthmd unary-minus-is-*
  (equal (- x)
	 (* -1 x)))

(defthm realpart--
  (implies
   (acl2-numberp x)
   (equal (realpart (- x))
	  (- (realpart x))))
  :hints (("Goal" :in-theory (e/d (unary-minus-is-*) (|(* -1 x)| realpart-*))
	   :use (:instance realpart-* (y -1)))))

(defthm imagpart--
  (implies
   (acl2-numberp x)
   (equal (imagpart (- x))
	  (- (imagpart x))))
  :hints (("Goal" :in-theory (e/d (unary-minus-is-*) (|(* -1 x)| imagpart-*))
	   :use (:instance imagpart-* (y -1)))))

(defthm realpart-of-rational
  (implies
   (rationalp x)
   (equal (realpart x) x)))

(defthm integerp-implies-rationalp
  (implies
   (integerp x)
   (rationalp x))
  :rule-classes (:forward-chaining))

(in-theory (disable SIMPLIFY-SUMS-< |(< (- x) (- y))|))

(defthm acl2-numberp-fix
  (acl2-numberp (fix x))
  :rule-classes ((:forward-chaining :trigger-terms ((fix x)))))

(defthm fix-acl2-numberp
  (implies
   (acl2-numberp x)
   (equal (fix x) x)))

(defthm acl2-numberp-from-complex-rationalp
  (implies
   (complex-rationalp x)
   (acl2-numberp x))
  :rule-classes (:forward-chaining))

(defthm acl2-numberp-from-rationalp
  (implies
   (rationalp x)
   (acl2-numberp x))
  :rule-classes (:forward-chaining))

(defun insert-and-count (x n list)
  (if (acl2-numberp x) (mv n list)
    (if (member x list) (mv n list)
      (mv (1+ n) (cons x list)))))

(defun unique-nonnumbers (x y z)
  (mv-let (n list) (insert-and-count x 0 nil)
	  (mv-let (n list) (insert-and-count y n list)
		  (mv-let (n list) (insert-and-count z n list)
			  (declare (ignore list))
			  n))))

(defun m0 (x y z)
  (unique-nonnumbers x y z))

(defun m1 (x y z)
  (declare (ignore z))
  (if (<= x y) 0 1))

(defun m2 (x y z)
  (let ((rx (realpart x))
	(ry (realpart y))
	(rz (realpart z)))
    (- (max (max rx ry) rz) (min (min rx ry) rz))))

(defun m3 (x y z)
  (let ((rx (realpart x))
	(ry (realpart y))
	(rz (realpart z)))
    (- rx (min (min rx ry) rz))))

(defun m4 (x y z)
  (let ((ix (imagpart x))
	(iy (imagpart y))
	(iz (imagpart z)))
    (- ix (min (min ix iy) iz))))

(defun tarai-measure (d x y z)
  (let ((m0 (m0 x y z)))
    (let ((x (* d x))
	  (y (* d y))
	  (z (* d z)))
      (llist m0 (m1 x y z) (m2 x y z) (m3 x y z) (m4 x y z)))))

(defun d-check-complex (d x)
  (and (integerp (* d (realpart x)))
       (integerp (* d (imagpart x)))))

(defun d-check (d x y z)
  (and
   (< 0 d) (integerp d)
   (d-check-complex d (fix x))
   (d-check-complex d (fix y))
   (d-check-complex d (fix z))))

(defthm measure-obligation-0
  (lexp (tarai-measure d x y z))
  :hints (("Goal" :do-not '(preprocess) :in-theory (disable fix))))

(defthm measure-obligation-1
  (implies
   (and
    (d-check d x y z)
    (> x y))
   (L< (tarai-measure d (1- x) y z)
       (tarai-measure d x y z)))
  :hints (("Goal" :do-not '(preprocess) :in-theory (disable fix))))

(defthm measure-obligation-2
  (implies
   (and
    (d-check d x y z)
    (> x y))
   (L< (tarai-measure d (1- y) z x)
       (tarai-measure d x y z)))
  :hints (("Goal" :do-not '(preprocess) :in-theory (disable fix))))

(defthm measure-obligation-3
  (implies
   (and
    (d-check d x y z)
    (> x y))
   (L< (tarai-measure d (1- z) x y)
       (tarai-measure d x y z)))
  :hints (("Goal" :do-not '(preprocess) :in-theory (disable fix))))

(defthm measure-obligation-4
  (implies
   (and
    (d-check d x y z)
    (> x y))
   (L< (tarai-measure d
		      (tarai-open (1- x) y z)
		      (tarai-open (1- y) z x)
		      (tarai-open (1- z) x y))
       (tarai-measure d x y z)))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (disable L<-DEFINITION tarai-measure fix))
	  (and stable-under-simplificationp
	       '(:in-theory (disable fix)))))

(defun tarai-induction (d x y z)
  (declare (xargs :measure (tarai-measure d x y z)
		  :hints (("Goal" :in-theory '(measure-obligation-0
					       measure-obligation-1
					       measure-obligation-2
					       measure-obligation-3
					       measure-obligation-4)))
		  :well-founded-relation l<))
  (cond
   ((and (d-check d x y z)
	 (> x y))
    (list
     (tarai-induction d (tarai-open (1- x) y z)
		        (tarai-open (1- y) z x)
		        (tarai-open (1- z) x y))
     (tarai-induction d (1- x) y z)
     (tarai-induction d (1- y) z x)
     (tarai-induction d (1- z) x y)))
   (t y)))

(defun d-complex-witness (x)
  (* (denominator (realpart x)) (denominator (imagpart x))))

(defun d-witness (x y z)
  (* (d-complex-witness (fix x))
     (d-complex-witness (fix y))
     (d-complex-witness (fix z))))

(defthm rationalp-reduction
  (implies
   (rationalp x)
   (equal (/ (numerator x) (denominator x)) x))
  :rule-classes (:elim))

(in-theory (disable complex-to-cc))

(defthm tarai_terminates_helper
  (implies
   (d-check d x y z)
   (tarai_terminates x y z))
  :hints (("Goal" :do-not-induct t
	   :do-not '(preprocess generalize)
	   :in-theory (disable tarai-open)
	   :expand ((TARAI_TERMINATES X Y Z))
	   :induct (tarai-induction d x y z))
	  (and stable-under-simplificationp
	       '(:in-theory (enable tarai-open)))))

(defthm d-check-d-witness
  (d-check (d-witness x y z) x y z))

(defthm tarai-always-terminates
  (tarai_terminates x y z)
  :hints (("Goal" :in-theory '(d-check-d-witness)
	   :use (:instance tarai_terminates_helper
			   (d (d-witness x y z))))))
|#
