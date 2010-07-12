#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
#|

   Fully Ordered Finite Sets, Version 0.9
   Copyright (C) 2003, 2004 by Jared Davis <jared@cs.utexas.edu>

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public Lic-
   ense along with this program; if not, write to the Free Soft-
   ware Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
   02111-1307, USA.

 primitives.lisp 

  Consider implementing a set theory library in ACL2.  Lists are a 
  natural choice for an underlying representation.  And, naturally,
  we are drawn to define our functions in terms of the primitive 
  list functions (car, cdr, endp, cons).  

  These functions are ill-suited for use in our set theory books be-
  cause of the non-set convention.  This convention states that non-
  sets should be treated as the empty set.  But the primitive list 
  functions do not support this idea.  For example:

    (car '(1 1 1)) = 1, but (car nil) = nil
    (cdr '(1 1 1)) = (1 1), but (cdr nil) = nil
    (cons 1 '(1 1 1)) = (1 1 1 1), but (cons 1 nil) = (1)
    (endp '(1 1 1)) = nil, but (endp nil) = t

  These are "problems" in the sense that, when reasoning about sets, 
  the primitive list functions do not respect the non-set convention.
  These functions do not fit our problem well, and will introduce all
  manner of cases into our proofs that we should not have to con-
  sider.

  Having recognized this as a problem, here is what we are going to
  do.  Instead of using the list primitives to manipulate sets, we 
  will use new primitives which are very similar, but which respect
  the non-set convention.  These primitives get the following names:
  
    (head X) - the first element of a set, nil for non/empty sets.
    (tail X) - all but the first element, nil for non/empty sets.
    (insert a X) - ordered insert of a into the set X
    (empty X) - recognizer for non/empty sets.

  This file introduces these functions, and shows several theorems 
  about them.  The purpose of all of this is to, at the end of this
  file, disable the definitions for these functions, and thereby 
  keep the primitive list functions (car, cdr, ...) confined where
  they cannot cause case splits.

  Before we can introduce the list primitives, we need to be able
  to define a set.  Our sets will be ordered under a total order, 
  <<.  Note that this order is encapsulated: we locally use the 
  same order as the standard "misc/total-order" book, which was 
  put together by Matt Kaufmann, Pete Manolios, and Rob Sumners.
  However, we will only use this locally and will allow other 
  orders to be used, in order to be a more flexible library.

|#


(in-package "SET")
(set-verify-guards-eagerness 2)



;;; First we introduce the total order, <<. and prove that it is a
;;; total order (irreflexivity, transitivity, asymmetricity, trichot-
;;; omy). 

(defun << (x y)
  (declare (xargs :guard t))
  (and (lexorder x y)
       (not (equal x y))))

(defthm <<-type
  (or (equal (<< a b) t)
      (equal (<< a b) nil))
  :rule-classes :type-prescription)

(defthm <<-irreflexive
  (not (<< a a)))

(defthm <<-transitive
  (implies (and (<< a b) (<< b c))
           (<< a c)))

(defthm <<-asymmetric
  (implies (<< a b)
           (not (<< b a))))

(defthm <<-trichotomy
  (implies (and (not (<< b a))
                (not (equal a b)))
           (<< a b)))

(in-theory (disable <<))




;;; Now we can define sets.  Sets are those lists whose elements are
;;; fully ordered under the relation above.  Note that this implicitly
;;; means that sets contain no duplicate elements.  Testing for sets
;;; will inherently be somewhat slow since we have to check that the
;;; elements are in order.  However, its complexity is still only lin-
;;; ear with the size of X.
 
(defun setp (X)
  (declare (xargs :guard t))
  (if (atom X)
      (null X)
    (or (null (cdr X))
        (and (consp (cdr X))
             (<< (car X) (cadr X))
             (setp (cdr X))))))

(defthm setp-type
  (or (equal (setp X) t)
      (equal (setp X) nil))
  :rule-classes :type-prescription)

(defthm sets-are-true-lists
  (implies (setp X)
           (true-listp X)))

(defmacro emptyset ()
  nil)



;;; At this point, we simply introduce the remainder of the primitive
;;; functions.  These definitions should hold few surprises.  The MBE
;;; macro is used in all of these functions except for insert, to
;;; avoid potentially slow calls to setp. 
 
(defun empty (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (or (null X)
                  (not (setp X)))
       :exec  (null X)))
 
(defthm empty-type
  (or (equal (empty X) t)
      (equal (empty X) nil))
  :rule-classes :type-prescription)
 
(defun sfix (X)
  (declare (xargs :guard (setp X)))
  (mbe :logic (if (empty X) nil X)
       :exec  X))
 
(defun head (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (car (sfix X))
       :exec  (car X)))
 
(defun tail (X)
  (declare (xargs :guard (and (setp X)
                              (not (empty X)))))
  (mbe :logic (cdr (sfix X))
       :exec  (cdr X)))
 
(defun insert (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) (list a))
        ((equal (head X) a) X)
        ((<< a (head X)) (cons a X))
        (t (cons (head X) (insert a (tail X))))))

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defthmd setp-list-to-set
  (setp (list-to-set X))
  :hints (("Goal" :in-theory (enable insert))))

;;; Our goal is to "hide" the list primitives (car, cdr, ...) within
;;; head, tail, etc.  This means that an end-user's functions will end
;;; up recurring over tail.  It is therefore important to show that
;;; tail actually decreases some measure, so that they can prove their
;;; functions terminate.  Naturally, we show that acl2-count decreases
;;; with tail.  We also show that acl2-count decreases with head, in
;;; case this fact is needed.
 
(defthm tail-count
  (implies (not (empty X))
           (< (acl2-count (tail X)) (acl2-count X)))
  :rule-classes :linear)

(defthm head-count
  (implies (not (empty X))
           (< (acl2-count (head X)) (acl2-count X)))
  :rule-classes :linear)

;;; Concluding that objects are sets is important for satisfying guard
;;; conjectures, and also for proofs of equality via a double contain-
;;; ment approach.  Here are some nice theorems to help with this:

(defthm sfix-produces-set
  (setp (sfix X)))

(defthm tail-produces-set
  (setp (tail X)))

(defthm insert-produces-set
  (setp (insert a X)))

(defthm nonempty-means-set
  (implies (not (empty X))
           (setp X)))

;;; Does every set have a unique representation?  Yes and no.  It is
;;; true in the sense that, if (setp X) holds, then there is no Y such
;;; that (in a X) <=> (in a Y) except for Y = X.  But what about when
;;; (setp X) does not hold?  Well, technically X is no longer a set,
;;; but our functions treat X as if it were empty.  We would like to
;;; be able to reason about this case.
;;;
;;; Well, although we cannot say (empty X) ^ (empty Y) => X = Y, we
;;; can state several similarly spirited theorems.  For example, we
;;; can say that the heads, tails, sfix's, and results of inserting
;;; elements into X and Y are always the same.  Here are several the-
;;; orems to this effect:

(defthm empty-set-unique
  (implies (and (setp X)
                (setp Y)
                (empty X)
                (empty Y))
           (equal (equal X Y) t)))

(defthm head-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (head X) (head Y)) t)))

(defthm tail-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (tail X) (tail Y)) t)))

(defthm insert-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (insert a X) (insert a Y)) t)))

(defthm sfix-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (sfix X) (sfix Y)) t)))

(defthm head-tail-same
  (implies (and (not (empty X))
                (not (empty Y))
                (equal (head X) (head Y))
                (equal (tail X) (tail Y)))
           (equal (equal X Y) t)))

;;; While the above theorems show a sort of equivalence between empty
;;; sets, it is also important to know what operations preserve and
;;; destroy emptiness.

(defthm insert-never-empty
  (not (empty (insert a X))))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

;;; While it did take quite a few theorems to have enough information
;;; about empty, the sfix function is more simple.  Sfix is the ident-
;;; ity function on sets, and maps all non-sets to nil.  We can show
;;; that all of the other primitives treat have a sort of equivalence
;;; under sfix, and quickly eliminate it when we see it:

(defthm sfix-set-identity
  (implies (setp X)
           (equal (sfix X) X)))

(defthm empty-sfix-cancel
  (equal (empty (sfix X)) (empty X)))

(defthm head-sfix-cancel
  (equal (head (sfix X)) (head X)))

(defthm tail-sfix-cancel
  (equal (tail (sfix X)) (tail X)))

(defthm insert-sfix-cancel
  (equal (insert a (sfix X)) (insert a X)))

;;; Now it is time to reason about insert.  These theorems are about
;;; as most complicated that we get.
;;;
;;; Historic Note: We used to require that nil was "greater than"
;;; everything else in our order.  This had the advantage that the
;;; following theorems could have a combined case for (empty X) and
;;; (<< a (head X)).  Starting in Version 0.9, we remove this res-
;;; triction in order to be more flexible about our order.

(defthm head-insert
  (equal (head (insert a X))
         (cond ((empty X) a)
               ((<< a (head X)) a)
               (t (head X)))))

(defthm tail-insert
  (equal (tail (insert a X))
         (cond ((empty X) (sfix X))
               ((<< a (head X)) (sfix X))
               ((equal a (head X)) (tail X))
               (t (insert a (tail X))))))

(defthm insert-insert
  (equal (insert a (insert b X))
         (insert b (insert a X)))
  :rule-classes ((:rewrite :loop-stopper ((a b)))))

(defthm repeated-insert
  (equal (insert a (insert a X))
         (insert a X)))

(defthm insert-head
  (implies (not (empty X))
           (equal (insert (head X) X) X)))

(defthm insert-head-tail
  (implies (not (empty X))
           (equal (insert (head X) (tail X)) X)))

;;; We also need to be able to reason about insertions into empty
;;; sets.  Do not move these theorems above head-insert and
;;; tail-insert, or they will be subsumed and proofs in
;;; membership.lisp will fail.

(defthm head-insert-empty
  (implies (empty X) 
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
            (empty (tail (insert a X)))))

;;; Insert can be reasoned about in terms of induction, but its induc-
;;; tive case contains a call to "cons", and we cannot let that escape
;;; into the wild.  Instead, we write a theorem to rephrase this cons
;;; into an insert.  WARNING: This can cause loops.  It is disabled by
;;; default for this reason.

(defthmd insert-induction-case
  (implies (and (not (empty X))
                (not (equal a (head X)))
                (not (<< a (head X))))
           (equal (insert a X)
                  (insert (head X) (insert a (tail X))))))

;;; The last thing we really need to do is reason about element order.
;;; The following theorems are crucial for proofs in the membership
;;; level, which must stricly use induction and arguments about the
;;; set elements' order for proofs.  Since we are disabling all of
;;; the functions at the end of this book, these are the only facts
;;; which membership.lisp will be able to use.

(defthm head-tail-order
  (implies (not (empty (tail X)))
           (<< (head X) (head (tail X)))))

(defthm head-tail-order-contrapositive
  (implies (not (<< (head X) (head (tail X))))
           (empty (tail X))))

(defthm head-not-head-tail
  (implies (not (empty (tail X)))
           (not (equal (head X) (head (tail X))))))

;;; Finally, this is an obscure looking theorem, which is only used to
;;; prove (not (in X X)) in membership.lisp.  TODO: Make sure it gets
;;; disabled afterwards.  This is a really odd theorem to just leave
;;; lying around enabled.

(defthm head-not-whole
  (implies (not (empty X))
           (not (equal (head X) X))))

;;; And that concludes the theorems we need about the primitive set
;;; functions.  Now we are interested in setting up theories and in
;;; disabling most of the potentially bad issues that might arise.
;;;
;;; You should never need to use primitive-theory unless you are using
;;; non-set functions, e.g. cons, to build sets.
;;;
;;; The primitive order theory is intended to be disabled for typical
;;; reasoning, but is needed for some theorems in the membership level.

(deftheory primitives-theory
  '(setp
    empty
    head
    tail
    sfix
    (:definition insert)))

(deftheory primitive-order-theory
  '(<<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

(in-theory (disable primitives-theory
                    primitive-order-theory))

