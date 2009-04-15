#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

(include-book "memberp")
(local (include-book "iff" :dir :util))
(local (include-book "remove"))

(defun disjoint (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y) 
          nil
	(disjoint (cdr x) y))
    t))

(defthm disjoint-remove-reduction-1
  (implies
   (not (memberp a y))
   (equal (disjoint (remove a x) y)
	  (disjoint x y))))

(defthm open-disjoint-on-memberp
  (implies
   (memberp a x)
   (equal (disjoint x y)
	  (and (not (memberp a y))
	       (disjoint (remove a x) y)))))

(defthm not-consp-disjoint
  (implies
   (not (consp x))
   (equal (disjoint x y) t)))

;; DAG: It's killing me that this is globally enabled ..
(defthm disjoint-remove-definition
  (equal (disjoint x y)
	 (if (consp x)
	     (and (not (memberp (car x) y))
		  (disjoint (remove (car x) x) y))
	   t))
  :rule-classes (:definition))

(defthm memberp-disjoint-non-memberp
  (implies
   (and
    (disjoint x y)
    (memberp a x))
   (not (memberp a y)))
  :rule-classes (:rewrite
		 :forward-chaining))

(defthm mutual-memberp-implies-not-disjoint
  (implies
   (and
    (memberp a x)
    (memberp a y))
   (not (disjoint x y)))
  :rule-classes (:forward-chaining))

(in-theory (disable disjoint-remove-reduction-1))
(in-theory (disable open-disjoint-on-memberp))

(encapsulate
 ()

 (defun mutual-non-membership (a x y)
   (implies
    (memberp a x)
    (not (memberp a y))))

 (encapsulate
  (((disjoint-hyps) => *)
   ((disjoint-lhs) => *)
   ((disjoint-rhs) => *)
   )

  (local (defun disjoint-hyps () nil))
  (local (defun disjoint-lhs () nil))
  (local (defun disjoint-rhs () nil))
  
  (defthm disjoint-multiplicity-constraint
    (implies 
     (disjoint-hyps)
     (mutual-non-membership arbitrary-element (disjoint-lhs) (disjoint-rhs)))
    :rule-classes nil)
  )

 (local (defun badguy-rec (x y)
	  (declare (xargs :measure (len x)))
          (cond ((or (atom x) (atom y)) nil)
                ((memberp (car x) y)
                 (car x))
                (t (badguy-rec (remove (car x) x) y)))))

 (local
  (defthm badguy-rec-membership-property
    (implies
     (and
      (not (disjoint x y))
      (not (memberp a x)))
     (not (equal (badguy-rec x y) a)))))

 (local
  (defthm not-disjoint-membership-reduction
    (implies
     (not (disjoint x y))
     (and (memberp (badguy-rec x y) x)
	  (memberp (badguy-rec x y) y)))))

 (local (defun badguy (x y)
	  (cond ((disjoint x y)
		 (if (consp x) (car x)
		   (if (consp y) (car y)
		     nil)))
		(t
		 (badguy-rec x y)))))

 (local (defthm badguy-witness
          (equal (disjoint x y)
		 (mutual-non-membership (badguy x y) x y))))

 (local (in-theory (disable mutual-non-membership badguy)))
 
 (defthm disjoint-by-multiplicity-driver
   (implies (disjoint-hyps)
            (disjoint (disjoint-lhs) (disjoint-rhs)))
   :rule-classes nil
   :hints(("Goal" 
           :use ((:instance 
                  disjoint-multiplicity-constraint
                  (arbitrary-element (badguy (disjoint-lhs) (disjoint-rhs))))))))

 (ADVISER::defadvice disjoint-by-multiplicity
   (implies (disjoint-hyps)
            (disjoint (disjoint-lhs) (disjoint-rhs)))
   :rule-classes (:pick-a-point :driver disjoint-by-multiplicity-driver))

 )

;; How expensive is this?

(defthm disjoint-commute-forward
  (implies
   (disjoint x y)
   (disjoint y x))
  :rule-classes (:forward-chaining))
