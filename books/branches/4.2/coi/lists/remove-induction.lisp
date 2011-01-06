#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

;; This should be multiple files, one per function

(include-book "remove")

;; Rules that otherwise eliminate removes

(in-theory (disable subset-remove-reduction-2))
(in-theory (disable subset-remove-reduction-1))
(in-theory (disable remove-list-remove-reduction-2))
(in-theory (disable remove-list-remove-reduction-1-alt))
(in-theory (disable remove-list-remove-reduction-1))

(defun remove-induction-1 (x)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-1 (remove (car x) x))
    x))

(defun remove-induction-2 (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-2 (remove (car x) x) (remove (car x) y))
    (list x y)))

(defun remove-induction-3 (x y z)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-3 (remove (car x) x) (remove (car x) y) (remove (car x) z))
    (list x y z)))

(defthm memberp-from-consp-fwd
  (implies
   (consp x)
   (memberp (car x) x))
  :rule-classes (:forward-chaining))

(defthmd open-memberp-on-memberp
  (implies
   (memberp a list)
   (equal (memberp b list)
	  (if (equal b a) t
	    (memberp b (remove a list))))))

(defthm memberp-remove-definition
  (equal (memberp a x)
	 (if (consp x)
	     (or (equal a (car x))
		 (memberp a (remove (car x) x)))
	   nil))
  :hints (("Goal" :in-theory (enable open-memberp-on-memberp)))
  :rule-classes (:definition))


(defthm open-subsetp-on-memberp
  (implies
   (memberp a x)
   (equal (subsetp x y)
	  (and (memberp a y)
	       (subsetp (remove a x) (remove a y))))))

(defthm subsetp-remove-definition
  (equal (subsetp x y)
	 (if (consp x)
	     (and (memberp (car x) y)
		  (subsetp (remove (car x) x) (remove (car x) y)))
	   t))
  :hints (("Goal" :in-theory (disable SUBSET-BY-MULTIPLICITY)))
  :rule-classes (:definition))

(defthm open-remove-list-on-memberp
  (implies
   (memberp a x)
   (equal (remove-list x y)
	  (remove-list (remove a x) (remove a y))))
  :hints (("Goal" :in-theory `(remove-list-remove-reduction-1-ALT
			       REMOVE-LIST-REMOVE-REDUCTION-2
			       MEMBERP-REMOVE 
			       (:TYPE-PRESCRIPTION MEMBERP) 
			       (:TYPE-PRESCRIPTION REMOVE)
			       ))))

(in-theory (enable remove-list-remove-definition))

