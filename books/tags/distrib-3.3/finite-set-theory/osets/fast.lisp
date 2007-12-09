#| 

   Fully Ordered Finite Sets, Version 0.91
   Copyright (C) 2003-2006 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.



 fast.lisp

  The MBE feature in ACL2 version 2.8 provides the opportunity to
  introduce functions which take advantage of the set order for good
  execution efficiency, while still using simple/nice functions for
  reasoning about.  

  This file contains efficient versions of the union, intersect, and
  difference functions, and a few theorems about them.  The goal is
  to show that for each of these "fast" functions, when given two 
  sets as inputs:

    (1) produces a set, and
    (2) has the correct membership properties

  These facts can then be used to make an equal-by-membership argu-
  ment with the simple versions as required by MBE. 

  Note that this file is very ugly.  There are many factors that con-
  tribute to this problem.  For one, these functions are written in
  terms of cons and therefore we have to consider many cases.  This 
  also means we have lots of subgoals when we do inductions.  It is
  also challenging to develop a "good" rewrite theory when it comes
  to the cons function, which does not have very nice properties when
  related to sets.

|#

(in-package "SETS")
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


;; PATCH (0.91): David Rager noticed that as of v0.9, fast-union was not tail
;; recursive, and submitted an updated version.  The original fast-union has
;; been renamed to fast-union-old, and the new fast-union replaces it.

(local (defun fast-union-old (X Y)
         (declare (xargs :measure (fast-measure X Y)
                         :guard (and (setp X) (setp Y))))
         (cond ((empty X) Y)
               ((empty Y) X)
               ((equal (head X) (head Y))
                (cons (head X) (fast-union-old (tail X) (tail Y))))
               ((<< (head X) (head Y))
                (cons (head X) (fast-union-old (tail X) Y)))
               (t (cons (head Y) (fast-union-old X (tail Y)))))))

(local 
 (encapsulate ()
              
  (local (defthmd fast-union-old-head-weak
           (implies (and (setp X) 
                         (setp Y)
                         (setp (fast-union-old X Y))
                         (not (equal (head (fast-union-old X Y)) (head X))))
                    (equal (head (fast-union-old X Y)) (head Y)))
           :hints(("Goal" 
                   :in-theory (enable primitive-order-theory)
                   :use (:instance fast-union-old (X X) (Y Y))))))

  (defthm fast-union-old-set
    (implies (and (setp X) (setp Y))
             (setp (fast-union-old X Y)))
    :hints(("Goal" 
            :in-theory (enable primitive-order-theory))
           ("Subgoal *1/9" 
            :use (:instance fast-union-old-head-weak 
                            (X X) 
                            (Y (tail Y))))
           ("Subgoal *1/7" 
            :use (:instance fast-union-old-head-weak
                            (X (tail X)) 
                            (Y Y)))
           ("Subgoal *1/5" 
            :use (:instance fast-union-old-head-weak
                            (X (tail X)) 
                            (Y (tail Y))))))


  (local (defthm fast-union-old-head-strong
           (implies (and (setp X) (setp Y))
                    (equal (head (fast-union-old X Y))
                           (cond ((empty X)              (head Y))
                                 ((empty Y)              (head X))
                                 ((<< (head X) (head Y)) (head X))
                                 (t                      (head Y)))))
           :hints(("Goal" 
                   :in-theory (enable primitive-order-theory))
                  ("Subgoal *1/3" :use 
                   (:instance cons-head 
                              (a (head X)) 
                              (X (fast-union-old (tail X) (tail Y))))))))

            
  (defthm fast-union-old-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-union-old X Y))
                    (or (in a X) (in a Y))))
    :hints(("Goal" 
            :in-theory (enable primitive-order-theory))
           ("Subgoal *1/5" 
            :use (:instance cons-head 
                            (a (head Y)) 
                            (X (fast-union-old X (tail Y)))))
           ("Subgoal *1/4" 
            :use ((:instance cons-head
                             (a (head X))
                             (X (fast-union-old (tail X) Y)))
                  (:instance cons-to-insert-nonempty
                             (a (head X))
                             (X (fast-union-old (tail X) Y)))
                  (:instance in-insert
                             (a a)
                             (b (head X))
                             (X (fast-union-old (tail X) Y)))))
           ("Subgoal *1/3" 
            :use (:instance cons-head
                            (a (head X))
                            (X (fast-union-old (tail X) (tail Y)))))))
  ))


(defun fast-union (x y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp x)
                              (setp y)
                              (true-listp acc))))

  (cond
   ((empty x) (revappend acc y))
   ((empty y) (revappend acc x))
   ((equal (head x) (head y))
    (fast-union (tail x) (tail y) (cons (head x) acc)))
   ((<< (head x) (head y))
    (fast-union (tail x) y (cons (head x) acc)))
   (t
    (fast-union x (tail y) (cons (head y) acc)))))


(encapsulate
 ()

 (local (defthm lemma
          (equal (fast-union x y acc)
                 (revappend acc (fast-union-old x y)))))

 (local (defthm lemma2
          (equal (fast-union x y nil)
                 (fast-union-old x y))))

 (defthm fast-union-set
   (implies (and (setp X) (setp Y))
            (setp (fast-union X Y nil))))
            
 (defthm fast-union-membership
   (implies (and (setp X) (setp Y))
            (equal (in a (fast-union X Y nil))
                   (or (in a X) (in a Y))))))






;;; Fast Intersect
;;;
;;; Again we are only interested in showing that fast-intersect
;;; creates sets and has the expected membership property.  And again,
;;; the proofs are quite ugly.

;; PATCH (0.91): David Rager noticed that as of v0.9, fast-intersect was not
;; tail recursive, and submitted an updated version.  The original
;; fast-intersect has been renamed to fast-intersect-old, and the new
;; fast-intersect replaces it.

(local (defun fast-intersect-old (X Y)
         (declare (xargs :measure (fast-measure X Y)
                         :guard (and (setp X) (setp Y))))
         (cond ((empty X) (sfix X))
               ((empty Y) (sfix Y))
               ((equal (head X) (head Y))
                (cons (head X) 
                      (fast-intersect-old (tail X) (tail Y))))
               ((<< (head X) (head Y))
                (fast-intersect-old (tail X) Y))
               (t (fast-intersect-old X (tail Y))))))

(local
 (encapsulate 
  ()

  (defthm fast-intersect-old-empty
    (implies (empty X)
             (equal (fast-intersect-old X Y) (sfix X))))

  (local (defthm lemma
           (implies (and (not (empty X))
                         (not (empty Y))
                         (not (equal (head X) (head Y)))
                         (not (empty (fast-intersect-old X Y)))
                         (not (<< (head X) (head Y))))
                    (not (empty (tail Y))))))
			 
  (local (defthm lemma-2
           (implies (and (not (empty X))
                         (not (empty Y))
                         (not (equal (head X) (head Y)))
                         (not (empty (fast-intersect-old X Y)))
                         (<< (head X) (head Y)))
                    (not (empty (tail X))))))

  (local (defthmd fast-intersect-old-head
           (implies (and (not (empty X))
                         (not (empty Y))
                         (equal (head X) (head Y))
                         (not (empty (fast-intersect-old X Y))))
                    (equal (head (fast-intersect-old X Y))
                           (head X)))
           :hints(("Goal" :in-theory (disable cons-set)))))

  (local (defthm fast-intersect-old-order-weak
           (implies (and (setp X)
                         (setp Y)
                         (not (empty X))
                         (not (empty Y))
                         (not (empty (fast-intersect-old X Y)))
                         (<< a (head X))
                         (<< a (head Y)))
                    (<< a (head (fast-intersect-old X Y))))
           :hints(("Goal" :in-theory (enable primitive-order-theory))
                  ("Subgoal *1/6" :use (:instance fast-intersect-old-head))
                  ("Subgoal *1/5" :use (:instance fast-intersect-old-head))
                  ("Subgoal *1/4" :use (:instance fast-intersect-old-head))
                  ("Subgoal *1/3" :use (:instance fast-intersect-old-head)))))

  (local (defthm fast-intersect-old-nonempty-weak
           (implies (not (empty (fast-intersect-old X Y)))
                    (and (not (empty X))
                         (not (empty Y))))))

  (local (defthm lemma-3
           (implies (and (not (empty x))
                         (not (empty y))
                         (equal (head x) (head y))
                         (setp (fast-intersect-old (tail x) (tail y)))
                         (setp x)
                         (setp y))
                    (setp (fast-intersect-old x y)))
           :hints(("Goal" :in-theory (e/d (primitive-order-theory)
                                          (cons-set
                                           fast-intersect-old-nonempty-weak
                                           fast-intersect-old-order-weak))
                   :use ((:instance fast-intersect-old-nonempty-weak
                                    (x (tail x))
                                    (y (tail y)))
                         (:instance fast-intersect-old-order-weak
                                    (a (head X))
                                    (X (tail X))
                                    (Y (tail Y))))))))

  (defthm fast-intersect-old-set
    (implies (and (setp X) (setp Y))
             (setp (fast-intersect-old X Y)))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
           ("Subgoal *1/5" :use (:instance lemma-3))))

  (defthm fast-intersect-old-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-intersect-old X Y))
                    (and (in a X) (in a Y))))
    :hints(("Goal" :in-theory (enable primitive-order-theory 
                                      head-minimal))
           ("Subgoal *1/3" :use (:instance fast-intersect-old-order-weak
                                           (a (head X))
                                           (X (tail X))
                                           (Y (tail Y))))))
  ))


(defun fast-intersect (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) 
                              (setp Y) 
                              (true-listp acc))))
  (cond ((empty X) (reverse acc))
        ((empty Y) (reverse acc))
        ((equal (head X) (head Y))
         (fast-intersect (tail X)
                         (tail Y)
                         (cons (head X) acc)))
        
        ((<< (head X) (head Y))
         (fast-intersect (tail X) Y acc))
        (t (fast-intersect X (tail Y) acc))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (true-listp acc)
                   (equal (fast-intersect x y acc)
                          (revappend acc (fast-intersect-old x y))))
          :hints (("Goal" :in-theory (enable sfix empty)))))


 (local (defthm lemma2
          (equal (fast-intersect x y nil)
                 (fast-intersect-old x y))))

 (defthm fast-intersect-empty
   (implies (empty X)
            (equal (fast-intersect X Y nil) 
                   (sfix X))))

 (defthm fast-intersect-set
   (implies (and (setp X) (setp Y))
            (setp (fast-intersect X Y nil))))

 (defthm fast-intersect-membership
   (implies (and (setp X) (setp Y))
            (equal (in a (fast-intersect X Y nil))
                   (and (in a X) (in a Y)))))
 )



;;; Fast Difference
;;;
;;; As before, we want to show that difference always creates a set
;;; and that the produced set has the expected membership properties.
;;; Also as before, these proofs are ugly.

;; PATCH (0.91): David Rager noticed that as of v0.9, fast-difference was not
;; tail recursive, and submitted an updated version.  The original
;; fast-difference has been renamed to fast-difference-old, and the new
;; fast-difference replaces it.

(defun fast-difference-old (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))))
  (cond ((empty X) (sfix X))
        ((empty Y) X)
        ((equal (head X) (head Y))
         (fast-difference-old (tail X) (tail Y)))
        ((<< (head X) (head Y))
         (cons (head X) (fast-difference-old (tail X) Y)))
        (t (fast-difference-old X (tail Y)))))

(local
 (encapsulate ()

  (local (defthm lemma
           (implies (and (not (empty X))
                         (not (empty Y))
                         (not (empty (fast-difference-old X Y)))
                         (not (equal (head X) (head Y)))
                         (<< (head X) (head Y)))
                    (equal (head (fast-difference-old X Y))
                           (head X)))
           :hints(("Goal" 
                   :in-theory (disable cons-set)
                   :use (:instance cons-head
                                   (a (head X))
                                   (X (fast-difference-old (tail X) Y)))))))

  (local (defthm lemma2
           (implies (and (not (empty X))
                         (not (empty Y))
                         (not (empty (fast-difference-old X Y)))
                         (equal (head X) (head Y)))
                    (not (empty (tail X))))))

  (local (defthm fast-difference-old-order-weak
           (implies (and (not (empty X))
                         (not (empty (fast-difference-old X Y)))
                         (<< a (head X)))
                    (<< a (head (fast-difference-old X Y))))
           :hints(("Goal" :in-theory (enable primitive-order-theory))
                  ("Subgoal *1/9" :use (:instance lemma))
                  ("Subgoal *1/8" :use (:instance lemma))
                  ("Subgoal *1/7" :use (:instance lemma)))))

  (defthm fast-difference-old-set
    (implies (and (setp X) (setp Y))
             (setp (fast-difference-old X Y)))
    :hints(("Goal" :in-theory (enable primitive-order-theory))
           ("Subgoal *1/7" :use (:instance fast-difference-old-order-weak
                                           (a (head X))
                                           (X (tail X))
                                           (Y Y)))))

  (defthm fast-difference-old-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-difference-old X Y))
                    (and (in a X)
                         (not (in a Y)))))
    :hints(("Goal" :in-theory (enable primitive-order-theory
                                      head-minimal))
           ("Subgoal *1/4" :use (:instance fast-difference-old-order-weak
                                           (a (head X))
                                           (X (tail X))
                                           (Y Y)))))

  (defthm fast-difference-old-empty
    (implies (empty X)
             (equal (fast-difference-old X Y) (sfix X))))
  ))


(defun fast-difference (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y) (true-listp acc))))

  (cond ((empty X) (reverse acc))
        ((empty Y) (revappend acc X))

        ((equal (head X) (head Y))
         (fast-difference (tail X) (tail Y) acc))

        ((<< (head X) (head Y))
         (fast-difference (tail X) Y (cons (head X) acc)))

        (t (fast-difference X (tail Y) acc))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (empty x)
                   (not (sfix x)))
          :hints(("Goal" :in-theory (enable empty sfix)))))
  
 (local (defthm lemma2
          (implies (true-listp acc)
                   (equal (fast-difference x y acc)
                          (revappend acc (fast-difference-old x y))))))

 (local (defthm lemma3
          (equal (fast-difference x y nil)
                 (fast-difference-old x y))))

 (defthm fast-difference-set
   (implies (and (setp X) (setp Y))
            (setp (fast-difference X Y nil))))

 (defthm fast-difference-membership
   (implies (and (setp X) (setp Y))
            (equal (in a (fast-difference X Y nil))
                   (and (in a X)
                        (not (in a Y))))))

 (defthm fast-difference-empty
   (implies (empty X)
            (equal (fast-difference X Y nil) 
                   (sfix X))))
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
                    
