#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(defthm equal-booleans-reducton
  (implies
   (and
    (booleanp x)
    (booleanp y))
   (equal (equal x y)
	  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm iff-reduction
  (equal (iff x y)
	 (and (implies x y)
	      (implies y x))))
