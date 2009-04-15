#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
;; pick-a-point.lisp
;; Pick a Point Method for Proving Subbagp


;; THE PICK A POINT SUBBAG STRATEGY
;; 
;; I describe the "pick a point subset strategy" in my 2004 ACL2 Workshop
;; Paper, "Finite Set Theory based on Fully Ordered Lists", and you can find a
;; copy of the set theory library in the :osets directory.  Essentially, the
;; idea is to allow you to prove (subset x y) by instead proving forall a, (in
;; a x) implies (in a y).
;;
;; In this file, I develop a "pick a point subbag strategy" which is very
;; similar, and reuses some of the same tools developed in osets.  In the bag
;; world, we cannot prove subbag by membership, but we can prove subbag by
;; multiplicity.  In other words, this file allows you to prove (subbag x y) by
;; instead showing that forall a, (count a x) is less than or equal to (count a
;; y).
;;
;; The reason that the pick a point method is successful in the sets world is
;; that membership, "in", has nice properties.  There are, in fact, beautiful
;; theorems such as:
;;
;;  (in a (insert b x))     = (or (equal a b) (in a x))
;;  (in a (delete b x))     = (and (in a x) (not (equal a b)))
;;  (in a (union x y))      = (or (in a x) (in a y))
;;  (in a (intersect x y))  = (and (in a x) (in a y))
;;  (in a (difference x y)) = (and (in a x) (not (in a y)))
;; 
;; And so forth.  The reason these theorems are so good is that the rewritten
;; term on the right hand sides have NO complicated functions!  For example,
;; the theorem about union completely removes the union term from the goal,
;; which is a "great stride of progress".
;;
;; I am hopeful that the strategy will be useful for bags as well.  After all,
;; it seems like count for bags share many of these same properties, e.g., the
;; count of an append is the sum of the counts, etc.  So, just like subset and
;; membership, proving subbagp by multiplicity may often be more natural then
;; proving subbagp by using some complicated induction scheme.

(in-package "BAG")
(include-book "basic")
(include-book "adviser" :dir :adviser)


(encapsulate
 ()

 (encapsulate
  (((bag-hyps) => *)
   ((subbag) => *)
   ((superbag) => *))
  
  (local (defun bag-hyps () nil))
  (local (defun subbag () nil))
  (local (defun superbag () nil))
  
  (defthm multiplicity-constraint
    (implies (bag-hyps)
             (<= (count arbitrary-element (subbag))
                 (count arbitrary-element (superbag))))
    :rule-classes nil)
  )

 (local (defun badguy (x y)
          (cond ((atom x)
                 nil)
                ((not (<= (count (car x) x)
                          (count (car x) y)))
                 (car x))
                (t (badguy (cdr x) 
                           (remove-1 (car x) y))))))
 
 (local (defthm badguy-witness
          (implies (not (subbagp x y))
                   (not (<= (count (badguy x y) x)
                            (count (badguy x y) y))))))
 
 (defthm subbag-by-multiplicity-driver
   (implies (bag-hyps)
            (subbagp (subbag) (superbag)))
   :rule-classes nil
   :hints(("Goal" 
           :use ((:instance 
                  multiplicity-constraint
                  (arbitrary-element (badguy (subbag) (superbag))))))))

 (ADVISER::defadvice subbag-by-multiplicity
   (implies (bag-hyps)
            (subbagp (subbag) (superbag)))
   :rule-classes (:pick-a-point :driver subbag-by-multiplicity-driver))

 )






;; THE DOUBLE CONTAINMENT PERM STRATEGY
;;
;; A related idea in the set theory library is the notion that, if you want to
;; prove that two sets are equal, you should just prove that they are mutual
;; subsets of one another.  (And, by extension of the pick a point strategy,
;; you should just prove that they have the same elements).
;;
;; We can come up with a similar strategy for perm.  In other words, if we want
;; to prove that two bags are perm, we should just show that they are mutual
;; subbags of one another.  We can then use our multiplicity strategy to reduce
;; the "perm" to a question of membership.
;;
;; In the set theory library, we have a double-containment rule that can be
;; relatively automatic, because we have hypotheses requiring x and y to be
;; sets.  In this case, we have no nice hypotheses that can guide the
;; application of this rule, so we just leave this disabled and expect you to
;; :use it when appropriate.

(defthmd perm-by-double-containment
  (equal (perm x y)
         (and (subbagp x y)
              (subbagp y x)))
  :hints(("Goal" :in-theory (enable perm))))
