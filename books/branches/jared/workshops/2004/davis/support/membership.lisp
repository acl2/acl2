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



 membership.lisp

  We are now getting into more interesting territory.  The primitive
  set functions nicely contain the potential messes that we would 
  have to face if we were implementing sets just using the primitive 
  list functions.  However, they are still plagued with order.

  The end user of the set library should not have to care that the 
  elements of the set are ordered or not.  (Well, with the exception
  that if they are trying to make a fast version of a function, they 
  might decide to exploit that order.)  

  Set reasoning should be done in terms of membership.  In tradition-
  al mathematics, subsets are defined through quantification over 
  membership, as is set equailty, and so forth.  But right now, the
  best we can do is induct over insert, which is somewhat messy.

  This file introduces the notions of set membership and subset.  We 
  also go into an abstract argument which will form the basis for 
  quantification.  The goal is to transform the insertion induction 
  proofs into more traditional pick-a-point and double containment 
  proofs.  

  At the end of this file, we will disable all of the theorems that 
  pertain to the order of elements, providing an entirely membership-
  based reasoning environment for the outer level.

|#

(in-package "SETS")
(include-book "primitives")
(include-book "computed-hints")
(set-verify-guards-eagerness 2)



;;; Set Membership.
;;;
;;; We could go ahead and write another version of in, which could use
;;; the total order to stop early if it ever encountered an element
;;; too big.  I.e., looking for 1 in the list '(2 3 4), it could say
;;; that since 1 << 2, we are done.  
;;;
;;; Should we do so?  Really the only question is whether or not it
;;; would be faster.  Certainly we can contrive situations in which it
;;; would be better, i.e. (in 1 '(2 3 4 .... 100000)), where we would
;;; save 100,000 calls to in.  But we can also contrive situations
;;; that it would be slower, for example (in 100001 '(1 2 3 4
;;; ... 100000)), where we would incur the extra cost of 100,000 calls
;;; to <<.  
;;;
;;; I have arbitrarily decided not to implement short-circuiting.  My
;;; reasoning is that (1) it is not clear which would be faster, (2)
;;; it is not clear what "typical" usage behavior of in would be, so
;;; even if we wanted to benchmark the two solutions, we could
;;; probably not come up with a good benchmarking suite, (3) both
;;; solutions are O(n) anyway so I don't think there's much to be
;;; gained here, and (4) the current method is arguably "no less
;;; efficient" than an unordered implementation.

(defun in (a X)
  (declare (xargs :guard (setp X)))
  (and (not (empty X))
       (or (equal a (head X))
	   (in a (tail X)))))

(defthm in-type
  (or (equal (in a X) t) 
      (equal (in a X) nil))
  :rule-classes :type-prescription)

(encapsulate ()

  (local (defthm lemma 
    (implies (> (acl2-count x) (acl2-count y))
             (not (in x y)))))

  (defthm not-in-self 
    (not (in x x)))

)

(defthm in-sfix-cancel
  (equal (in a (sfix X)) (in a X)))

(defthm never-in-empty
  (implies (empty X) (not (in a X))))

(defthm in-set
  (implies (in a X) (setp X)))

(defthm in-tail
  (implies (in a (tail X)) (in a X)))

(defthm in-tail-or-head
  (implies (and (in a X) 
                (not (in a (tail X))))
           (equal (head X) a)))


;;; We now begin to move away from set order.

(encapsulate ()

  (local (defthm lemma
	   (implies (and (not (empty X))
			 (not (equal a (head X)))
			 (not (<< a (head (tail X))))
			 (<< a (head X)))
		    (not (in a X)))
	   :hints(("Goal" 
		   :in-theory (enable primitive-order-theory)
		   :cases ((empty (tail X)))))))

  (defthm head-minimal
    (implies (<< a (head X))
	     (not (in a X)))
    :hints(("Goal" 
	    :in-theory (enable primitive-order-theory))))

  (defthm head-minimal-2
    (implies (in a X)
	     (not (<< a (head X)))))

)

(encapsulate ()

  (local (defthm lemma
	   (implies (empty (tail X))
		    (not (in (head X) (tail X))))))
  
  (local (defthm lemma-2
	   (implies (not (empty (tail X)))
		    (not (in (head X) (tail X))))
	   :hints(("Goal" :in-theory (enable primitive-order-theory)))))
  
  ;; This is an interesting theorem, which gives us a concept of 
  ;; uniqueness without using the set order to state it!

  (defthm head-unique
    (not (in (head X) (tail X)))
    :hints(("Goal" 
	    :use ((:instance lemma)
		  (:instance lemma-2)))))
)


(defthm insert-identity
  (implies (in a X)
           (equal (insert a X) X))
  :hints(("Goal" :in-theory (enable insert-induction-case))))


(defthm in-insert
  (equal (in a (insert b X))
         (or (in a X) 
             (equal a b)))
  :hints(("Goal" :in-theory (enable primitive-order-theory)
                 :induct (insert b X))))




;;; The behavior of insert is, of course, determined by the set order.
;;; Yet, we often need to induct upon insert's definition to prove
;;; theorems.  So, here we introduce a new induction scheme which
;;; hides the set order, yet still allows us to induct on insert very
;;; nicely.  We then disable the induction scheme that insert normally
;;; uses, and set up an induction hint so that weak-insert-induction
;;; will automatically be used instead.
 
(defthm weak-insert-induction-helper-1
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (head (insert a X)) (head X)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(defthm weak-insert-induction-helper-2
  (implies (and (not (in a X))
                (not (equal (head (insert a X)) a)))
           (equal (tail (insert a X)) (insert a (tail X)))) 
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(defthm weak-insert-induction-helper-3
  (implies (and (not (in a X))
                (equal (head (insert a X)) a))
           (equal (tail (insert a X)) (sfix X)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))

(defun weak-insert-induction (a X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
        ((in a X) nil)
        ((equal (head (insert a X)) a) nil)
        (t (list (weak-insert-induction a (tail X))))))

(in-theory (disable (:induction insert)))

(defthm use-weak-insert-induction t 
  :rule-classes ((:induction 
                  :pattern (insert a X)
                  :scheme (weak-insert-induction a X))))





;;; Subset Testing.
;;;
;;; Now we introduce subset.  This becomes complicated because we want
;;; to use MBE to make it fast.  The fast-subset function is a tail
;;; re- cursive, linear pass through both lists.  Subset, by
;;; comparison, is a nice to reason about definition and much simpler,
;;; but would require quadratic time if we didn't use MBE here.

(defun fast-subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (cond ((empty X) t)
        ((empty Y) nil)
        ((<< (head X) (head Y)) nil)
        ((equal (head X) (head Y)) (fast-subset (tail X) (tail Y)))
        (t (fast-subset X (tail Y)))))

(defun subset (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (mbe :logic (if (empty X)
		  t
		(and (in (head X) Y)
		     (subset (tail X) Y)))
       :exec (fast-subset X Y)))

(defthm subset-type
  (or (equal (subset X Y) t)
      (equal (subset X Y) nil))
  :rule-classes :type-prescription)

(encapsulate ()

  (local (defthmd lemma
	   (implies (not (in (head Y) X))
		    (equal (subset X Y) (subset X (tail Y))))))

  (local (defthm case-1
	   (implies (and (not (empty X))
			 (not (empty Y))
			 (not (<< (head X) (head Y)))
			 (not (equal (head X) (head Y)))
			 (implies (and (setp X) (setp (tail Y)))
				  (equal (fast-subset X (tail Y))
					 (subset X (tail Y)))))
		    (implies (and (setp X) (setp Y))
			     (equal (fast-subset X Y)
				    (subset X Y))))
	   :hints(("Goal" :in-theory (enable primitive-order-theory)
		   :use (:instance lemma)))))

  (local (defthm case-2
	   (implies (and (not (empty x))
			 (not (empty y))
			 (not (<< (head x) (head y)))
			 (equal (head x) (head y))
			 (implies (and (setp (tail x)) (setp (tail y)))
				  (equal (fast-subset (tail x) (tail y))
					 (subset (tail x) (tail y)))))
		    (implies (and (setp x) (setp y))
			     (equal (fast-subset x y)
				    (subset x y))))
	   :hints(("Goal" :in-theory (enable primitive-order-theory)
		   :use (:instance lemma (X (tail X)))))))

  (local (defthm fast-subset-equivalence
	   (implies (and (setp X) (setp Y))
		    (equal (fast-subset X Y) (subset X Y)))
	   :hints(("Goal" :in-theory (enable primitive-order-theory)
		   :induct (fast-subset X Y)))))

  (verify-guards subset)

)




;;; Quantification over Sets.
;;;
;;; Up until version 0.81, we used an explicit argument to reduce subset
;;; proofs to pick-a-point style membership arguments.  Starting in 0.9,
;;; we generalize this argument to arbitrary predicates instead.
;;; 
;;; I'll begin with some background on what we historically wanted to
;;; do.  The "ultimate goal" was to use pick-a-point reasoning to
;;; prove subset relationships.  In traditional mathematics, subset is
;;; defined using quantification over members, e.g., as follows:
;;;
;;;    (subset X Y) iff "forall a : (in a X) implies (in a Y)"
;;; 
;;; Traditionally, one would prove the membership part of this
;;; statement, and use it to conclude whether or not (subset X Y) is
;;; true.  But, in ACL2, we cannot write a theorem of the following
;;; form, because all variables are implicitly universally quantified.
;;;
;;;    [ "forall a : (in a ...) implies (in a ___)" ]
;;;       => 
;;;    (subset ... ___)
;;;
;;; However, we can take the contrapositive of this theorem, which
;;; looks like the following:
;;;
;;;    ~(subset ... ___) => "exists a : (in a ...) ^ ~(in a ___)
;;; 
;;; And we can prove this, by using a new function to search for an
;;; element which satisfies the existential predicate.  
;;;
;;; Once we prove the above, we still need to be able to "reduce" a
;;; proof of (subset X Y) to a proof of (in a X) => (in a Y).  While
;;; we can't do this with a direct rewrite rule, we can sort of fake
;;; it using functional instantiation.  In other words, we set up an
;;; encapsulated event with (in a X) => (in a Y) as its constraint,
;;; then we can use this constraint to prove that (subset X Y).  By
;;; functionally instantiating the resulting theorem, we can reduce
;;; the subset problem to a membership problem.
;;;
;;; All of this was an explicit argument until version 0.9.  But, now
;;; the process is generalized.  First notice that subset is really
;;; nothing more than "forall a, (in a x) => (in a Y)."  If you let (P
;;; x) = (in a Y), then this is "forall a, (in a x) => (P a)".  This
;;; is a more general concept which can capture not only subset, but
;;; also many other ideas by simply changing the meaning of (P x).
;;; For example, if P = integerp, then we can test if every element in
;;; the set is an integer, and so forth.  So, starting in v0.9, we use
;;; this more general form of encapsulate instead of the more specific
;;; version used in previous versions.
;;;
;;; We begin by introducing a completely arbitrary predicate.  Based
;;; on this generic predicate we will introduce a new function, all,
;;; which checks to see if every member in a set satisfies a
;;; predicate.  We also introduce find-not, which can be used to find
;;; us a witness for proving all-by-membership.  Finally, we set up an
;;; encapsulate which allows us to assume that if some hypotheses are
;;; true, then any member of some set satisfies the predicate, and use
;;; this constraint to prove that if those same hypotheses are
;;; satisfied, then all is true for the same set.

(encapsulate
 (((predicate *) => *))
  (local (defun predicate (x) x)))

(defun all (set-for-all-reduction) 
  (declare (xargs :guard (setp set-for-all-reduction)))
  (if (empty set-for-all-reduction)
      t
    (and (predicate (head set-for-all-reduction))
	 (all (tail set-for-all-reduction)))))

(defun find-not (X)
  (declare (xargs :guard (setp X)))
  (cond ((empty X) nil)
	((not (predicate (head X))) (head X))
	(t (find-not (tail X)))))



(encapsulate 
 (((all-hyps) => *)
  ((all-set) => *))

 (local (defun all-hyps () nil))
 (local (defun all-set () nil))

 (defthmd membership-constraint
   (implies (all-hyps)
	    (implies (in arbitrary-element (all-set))
		     (predicate arbitrary-element))))
)

(encapsulate ()

  (local (defthm lemma-find-not-is-a-witness
	   (implies (not (all x))
		    (and (in (find-not x) x)
			 (not (predicate (find-not x)))))))

  (defthmd all-by-membership
    (implies (all-hyps)
	     (all (all-set)))
    :hints(("Goal" 
	    :use (:instance membership-constraint 
			    (arbitrary-element (find-not (all-set)))))))
)


;;; The theorem all-by-membership is massively important.  It is the basis
;;; for reducing subset arguments to membership arguments.  It also has a 
;;; sufficiently general character that we can reuse it to make similar
;;; reductions for problems other than subset.
;;;
;;; However, for the time being, it's important that we actually do apply
;;; this theorem to the subset function, which is a particularly useful 
;;; way of reasoning about sets.  Two important questions are: how can we
;;; apply the theorem, and when should we apply it?  
;;;
;;; To support these notions, a framework is introduced in the file 
;;; computed-hints.lisp.  Basically, we introduce a "trigger" function 
;;; which is nothing more than an alias for subset.  We then use the
;;; "tagging theorem" pick-a-point-subset-strategy in order to rewrite
;;; subsets into subset-triggers.  This theorem is constrained so that
;;; it will only rewrite conclusions and it will not apply while 
;;; backchaining, via syntaxp hypotheses.  This process is described 
;;; in more detail in computed-hints.lisp.

(defun subset-trigger (X Y)
  (declare (xargs :guard (and (setp X) (setp Y))))
  (subset X Y))

(defthm pick-a-point-subset-strategy
  (implies (and (syntaxp (rewriting-goal-lit mfc state))
		(syntaxp (rewriting-conc-lit `(subset ,X ,Y) mfc state)))
	   (equal (subset X Y)
		  (subset-trigger X Y))))

(in-theory (disable subset-trigger))



(COMPUTED-HINTS::automate-instantiation 
  :new-hint-name pick-a-point-subset-hint 
  :generic-theorem all-by-membership
  :generic-predicate predicate
  :generic-hyps all-hyps
  :generic-collection all-set
  :generic-collection-predicate all
  :actual-collection-predicate subset
  :actual-trigger subset-trigger
  :predicate-rewrite (((predicate ?x ?y) (in ?x ?y)))
  :tagging-theorem pick-a-point-subset-strategy
)





;;; We now show the basic properties of subset.  The first theorems
;;; are mundane but then we get more interesting, showing that subset
;;; is reflexive and transitive.  The goal here is to build up
;;; sufficient theorems to do pick-a-point proofs, which come next.

(defthm subset-sfix-cancel-X
  (equal (subset (sfix X) Y) 
	 (subset X Y)))

(defthm subset-sfix-cancel-Y
  (equal (subset X (sfix Y)) 
	 (subset X Y)))

(defthm empty-subset
  (implies (empty X) 
	   (subset X Y)))

(defthm empty-subset-2
  (implies (empty Y)
	   (equal (subset X Y) (empty X))))

(defthm subset-in
  (implies (and (subset X Y) 
		(in a X))
           (in a Y)))

(defthm subset-in-2
  (implies (and (subset X Y) 
		(not (in a Y)))
           (not (in a X))))

(defthm subset-insert-X
  (equal (subset (insert a X) Y)
	 (and (subset X Y)
	      (in a Y)))
  :hints(("Goal" :induct (insert a X))))

(defthm subset-reflexive
  (subset X X))

(defthm subset-transitive
  (implies (and (subset X Y) 
		(subset Y Z))
           (subset X Z)))

(defthm subset-membership-tail
  (implies (and (subset X Y) 
		(in a (tail X)))
           (in a (tail Y)))
  :hints(("Goal" :in-theory (enable primitive-order-theory))))
          
(defthm subset-membership-tail-2
  (implies (and (subset X Y) 
		(not (in a (tail Y))))
           (not (in a (tail X))))
  :hints(("Goal" :in-theory (disable subset-membership-tail)
                 :use (:instance subset-membership-tail))))

(defthm subset-insert
  (subset X (insert a X)))

(defthm subset-tail
  (subset (tail X) X)
  :rule-classes ((:rewrite) 
		 (:forward-chaining :trigger-terms ((tail x)))))






;;; Proofs of equality by double containment are also very common.  So,
;;; to support these, we want to show that double containment is the 
;;; same as equality.  
;;;
;;; The general argument is the following:
;;;
;;;  Suppose that we have two sets which are subsets of one another, 
;;;  i.e. (subset X Y) and (subset Y X) are true.  First, we will show
;;;  that (head X) = (head Y).  Next we will show that (in a (tail X))
;;;  implies that (in a (tail Y)).  This fact is then used for a sub-
;;;  set by membership argument to show that (tail X) = (tail Y).
;;;  Now, (head X) = (head Y) and (tail X) = (tail Y) can be used 
;;;  together to show that X = Y (see primitives.lisp, head-tail-same)
;;;  so we are done.  

(encapsulate ()

  ;; Here are the details.  First we show that the heads are the same:

  (local (defthmd double-containment-lemma-head
	   (implies (and (subset X Y)
			 (subset Y X))
		    (equal (head X) (head Y)))
	   :hints(("Goal" :in-theory (enable primitive-order-theory)))))


  ;; Next we show that (tail X) is a subset of (tail Y), using a subset
  ;; by membership argument:

  (local (defthmd in-tail-expand
	   (equal (in a (tail X))
		  (and (in a X)
		       (not (equal a (head X)))))))

  (local (defthmd double-containment-lemma-in-tail
	   (implies (and (subset X Y)
			 (subset Y X))
		    (implies (in a (tail X))     ; could be "equal" instead, 
			     (in a (tail Y))))   ; but that makes loops.
	   :hints(("Goal"
		   :in-theory (enable primitive-order-theory)
		   :use ((:instance in-tail-expand (a a) (X X))
			 (:instance in-tail-expand (a a) (X Y)))))))

  (local (defthmd double-containment-lemma-tail 
	   (implies (and (subset X Y)
			 (subset Y X))
		    (subset (tail X) (tail Y)))
	   :hints(("Goal" :in-theory (enable double-containment-lemma-in-tail)))))

  ;; Finally, we are ready to show that double containment is equality.
  ;; To do this, we need to induct in such a way that we consider the 
  ;; tails of X and Y.  Then, we will use our fact that about the tails
  ;; being subsets of one another in the inductive case.

  (local (defun double-tail-induction (X Y)
	   (declare (xargs :guard (and (setp X) (setp Y))))
	   (if (or (empty X) (empty Y))
	       (list X Y)
	     (double-tail-induction (tail X) (tail Y)))))

  (local (defthm double-containment-is-equality-lemma
	   (IMPLIES (AND (NOT (OR (EMPTY X) (EMPTY Y)))
			 (IMPLIES (AND (SUBSET (TAIL X) (TAIL Y))
				       (SUBSET (TAIL Y) (TAIL X)))
				  (EQUAL (EQUAL (TAIL X) (TAIL Y)) T))
			 (SETP X)
			 (SETP Y)
			 (SUBSET X Y)
			 (SUBSET Y X))
		    (EQUAL (EQUAL X Y) T))
	   :hints(("Goal" 
		   :use ((:instance double-containment-lemma-tail
				    (X X) (Y Y))
			 (:instance double-containment-lemma-tail 
				    (X Y) (Y X))
			 (:instance double-containment-lemma-head
				    (X X) (Y Y)))))))

  (local (defthmd double-containment-is-equality
	   (implies (and (setp X) 
			 (setp Y)
			 (subset X Y)
			 (subset Y X))
		    (equal (equal X Y) t))
	   :hints(("Goal" :induct (double-tail-induction X Y)))))

  (defthm double-containment 
    (implies (and (setp X)
		  (setp Y))
	     (equal (equal X Y)
		    (and (subset X Y)
			 (subset Y X))))
    :hints(("Goal" :use (:instance double-containment-is-equality))))

)


;;; We are now done with the membership level.  We disable all of the
;;; order based reasoning that we introduced here.

(in-theory (disable head-minimal
                    head-minimal-2))






