; Fully Ordered Finite Sets, Version 0.9
; Copyright (C) 2003, 2004 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>
;
; fast.lisp
;
; The MBE feature in ACL2 version 2.8 provides the opportunity to introduce
; functions which take advantage of the set order for good execution
; efficiency, while still using simple/nice functions for reasoning about.
;
; This file contains efficient versions of the union, intersect, and difference
; functions, and a few theorems about them.  The goal is to show that for each
; of these "fast" functions, when given two sets as inputs:
;
;   (1) produces a set, and
;   (2) has the correct membership properties
;
; These facts can then be used to make an equal-by-membership argu- ment with
; the simple versions as required by MBE.
;
; Note that this file is very ugly.  There are many factors that con- tribute
; to this problem.  For one, these functions are written in terms of cons and
; therefore we have to consider many cases.  This also means we have lots of
; subgoals when we do inductions.  It is also challenging to develop a "good"
; rewrite theory when it comes to the cons function, which does not have very
; nice properties when related to sets.

(in-package "SET")
(include-book "membership")
(set-verify-guards-eagerness 2)


;;; First we introduce some basic theory about cons and sets.  Note
;;; that this theory is disabled at the end of this file.  However, if
;;; you are introducing fast versions of new set functions, you can
;;; enable these theorems by enabling cons-theory.

(defthm cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X))))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory
                                    primitive-order-theory))))

(defthm cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))



;;; These fast versions recur on one or both of their arguments, but
;;; not always the same argument.  Hence, we need to introduce a more
;;; flexible measure to prove that they terminate.  Fortunately, this
;;; is still relatively simple:

(defun fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))




;;; Fast Union
;;;
;;; We want to show that fast union always produces a set, and has the
;;; expected membership property.  This is ugly because reasoning
;;; about set order is hard.

(defun fast-union (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) Y)
        ((empty Y) X)
        ((equal (head X) (head Y))
         (cons (head X) (fast-union (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (cons (head X) (fast-union (tail X) Y)))
        (t (cons (head Y) (fast-union X (tail Y))))))


(encapsulate ()

  (local (defthmd fast-union-head-weak
	   (implies (and (setp X)
			 (setp Y)
			 (setp (fast-union X Y))
			 (not (equal (head (fast-union X Y)) (head X))))
		    (equal (head (fast-union X Y)) (head Y)))
	   :hints(("Goal"
		   :in-theory (enable primitive-order-theory)
		   :use (:instance fast-union (X X) (Y Y))))))

  (defthm fast-union-set
    (implies (and (setp X) (setp Y))
	     (setp (fast-union X Y)))
    :hints(("Goal"
	    :in-theory (enable primitive-order-theory))
	   ("Subgoal *1/9"
	    :use (:instance fast-union-head-weak
			    (X X)
			    (Y (tail Y))))
	   ("Subgoal *1/7"
	    :use (:instance fast-union-head-weak
			    (X (tail X))
			    (Y Y)))
	   ("Subgoal *1/5"
	    :use (:instance fast-union-head-weak
			    (X (tail X))
			    (Y (tail Y))))))


  (local (defthm fast-union-head-strong
	   (implies (and (setp X) (setp Y))
		    (equal (head (fast-union X Y))
			   (cond ((empty X)              (head Y))
				 ((empty Y)              (head X))
				 ((<< (head X) (head Y)) (head X))
				 (t                      (head Y)))))
	   :hints(("Goal"
		   :in-theory (enable primitive-order-theory))
		  ("Subgoal *1/3" :use
		   (:instance cons-head
			      (a (head X))
			      (X (fast-union (tail X) (tail Y))))))))


  (defthm fast-union-membership
    (implies (and (setp X) (setp Y))
	     (equal (in a (fast-union X Y))
		    (or (in a X) (in a Y))))
    :hints(("Goal"
	    :in-theory (enable primitive-order-theory))
           ("Subgoal *1/5"
	    :use (:instance cons-head
			    (a (head Y))
			    (X (fast-union X (tail Y)))))
	   ("Subgoal *1/4"
	    :use ((:instance cons-head
			     (a (head X))
			     (X (fast-union (tail X) Y)))
		  (:instance cons-to-insert-nonempty
			     (a (head X))
			     (X (fast-union (tail X) Y)))
		  (:instance in-insert
			     (a a)
			     (b (head X))
			     (X (fast-union (tail X) Y)))))
	   ("Subgoal *1/3"
	    :use (:instance cons-head
			    (a (head X))
			    (X (fast-union (tail X) (tail Y)))))))
)




;;; Fast Intersect
;;;
;;; Again we are only interested in showing that fast-intersect
;;; creates sets and has the expected membership property.  And again,
;;; the proofs are quite ugly.

(defun fast-intersect (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) (sfix Y))
        ((equal (head X) (head Y))
         (cons (head X)
               (fast-intersect (tail X) (tail Y))))
        ((<< (head X) (head Y))
         (fast-intersect (tail X) Y))
        (t (fast-intersect X (tail Y)))))


(encapsulate ()

  (defthm fast-intersect-empty
    (implies (empty X)
	     (equal (fast-intersect X Y) (sfix X))))

  (local (defthm lemma
	   (implies (and (not (empty X))
			 (not (empty Y))
			 (not (equal (head X) (head Y)))
			 (not (empty (fast-intersect X Y)))
			 (not (<< (head X) (head Y))))
		    (not (empty (tail Y))))))

  (local (defthm lemma-2
	   (implies (and (not (empty X))
			 (not (empty Y))
			 (not (equal (head X) (head Y)))
			 (not (empty (fast-intersect X Y)))
			 (<< (head X) (head Y)))
		    (not (empty (tail X))))))

  (local (defthmd fast-intersect-head
    (implies (and (not (empty X))
		  (not (empty Y))
		  (equal (head X) (head Y))
		  (not (empty (fast-intersect X Y))))
	     (equal (head (fast-intersect X Y))
		    (head X)))
    :hints(("Goal" :in-theory (disable cons-set)))))

  (local (defthm fast-intersect-order-weak
    (implies (and (setp X)
		  (setp Y)
		  (not (empty X))
		  (not (empty Y))
		  (not (empty (fast-intersect X Y)))
		  (<< a (head X))
		  (<< a (head Y)))
	     (<< a (head (fast-intersect X Y))))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
	   ("Subgoal *1/6" :use (:instance fast-intersect-head))
	   ("Subgoal *1/5" :use (:instance fast-intersect-head))
	   ("Subgoal *1/4" :use (:instance fast-intersect-head))
	   ("Subgoal *1/3" :use (:instance fast-intersect-head)))))

  (local (defthm fast-intersect-nonempty-weak
    (implies (not (empty (fast-intersect X Y)))
	     (and (not (empty X))
		  (not (empty Y))))))

  (local (defthm lemma-3
    (implies (and (not (empty x))
		  (not (empty y))
		  (equal (head x) (head y))
		  (setp (fast-intersect (tail x) (tail y)))
		  (setp x)
		  (setp y))
	     (setp (fast-intersect x y)))
    :hints(("Goal" :in-theory (e/d (primitive-order-theory)
				   (cons-set
				    fast-intersect-nonempty-weak
				    fast-intersect-order-weak))
	    :use ((:instance fast-intersect-nonempty-weak
			     (x (tail x))
			     (y (tail y)))
		  (:instance fast-intersect-order-weak
			     (a (head X))
			     (X (tail X))
			     (Y (tail Y))))))))

  (defthm fast-intersect-set
    (implies (and (setp X) (setp Y))
	     (setp (fast-intersect X Y)))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
	   ("Subgoal *1/5" :use (:instance lemma-3))))

  (defthm fast-intersect-membership
    (implies (and (setp X) (setp Y))
	     (equal (in a (fast-intersect X Y))
		    (and (in a X) (in a Y))))
    :hints(("Goal" :in-theory (enable primitive-order-theory
				      head-minimal))
	   ("Subgoal *1/3" :use (:instance fast-intersect-order-weak
					   (a (head X))
					   (X (tail X))
					   (Y (tail Y))))))

)



;;; Fast Difference
;;;
;;; As before, we want to show that difference always creates a set
;;; and that the produced set has the expected membership properties.
;;; Also as before, these proofs are ugly.

(defun fast-difference (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) X)
        ((equal (head X) (head Y))
         (fast-difference (tail X) (tail Y)))
        ((<< (head X) (head Y))
         (cons (head X) (fast-difference (tail X) Y)))
        (t (fast-difference X (tail Y)))))




(encapsulate ()

  (local (defthm lemma
    (implies (and (not (empty X))
		  (not (empty Y))
		  (not (empty (fast-difference X Y)))
		  (not (equal (head X) (head Y)))
		  (<< (head X) (head Y)))
	     (equal (head (fast-difference X Y))
		    (head X)))
    :hints(("Goal"
	    :in-theory (disable cons-set)
	    :use (:instance cons-head
			    (a (head X))
			    (X (fast-difference (tail X) Y)))))))

  (local (defthm lemma-2
    (implies (and (not (empty X))
		  (not (empty Y))
		  (not (empty (fast-difference X Y)))
		  (equal (head X) (head Y)))
	     (not (empty (tail X))))))

  (local (defthm fast-difference-order-weak
    (implies (and (not (empty X))
		  (not (empty (fast-difference X Y)))
		  (<< a (head X)))
	     (<< a (head (fast-difference X Y))))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
	   ("Subgoal *1/9" :use (:instance lemma))
	   ("Subgoal *1/8" :use (:instance lemma))
	   ("Subgoal *1/7" :use (:instance lemma)))))

  (defthm fast-difference-set
    (implies (and (setp X) (setp Y))
	     (setp (fast-difference X Y)))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
	   ("Subgoal *1/7" :use (:instance fast-difference-order-weak
					   (a (head X))
					   (X (tail X))
					   (Y Y)))))

  (defthm fast-difference-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-difference X Y))
                    (and (in a X)
                         (not (in a Y)))))
    :hints(("Goal" :in-theory (enable primitive-order-theory
                                      head-minimal))
           ("Subgoal *1/4" :use (:instance fast-difference-order-weak
                                           (a (head X))
                                           (X (tail X))
                                           (Y Y)))))

  (defthm fast-difference-empty
    (implies (empty X)
	     (equal (fast-difference X Y) (sfix X))))
)



;;; We don't really want to reason about these functions again.  So,
;;; we will go ahead and disable all these theorems and put them into
;;; nice packages for the future.

(deftheory fast-union-theory
  '(fast-union-set
    fast-union-membership))

(deftheory fast-intersect-theory
  '(fast-intersect-set
    fast-intersect-membership
    fast-intersect-empty))

(deftheory fast-difference-theory
  '(fast-difference-set
    fast-difference-membership
    fast-difference-empty))

(deftheory cons-theory
  '(cons-set
    cons-head
    cons-to-insert-empty
    cons-to-insert-nonempty
    cons-in))

(in-theory (disable fast-measure
		    fast-union
		    fast-intersect
		    fast-difference
		    fast-union-theory
                    fast-intersect-theory
                    fast-difference-theory
		    cons-theory))

