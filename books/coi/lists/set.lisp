#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

(include-book "remove")
(include-book "disjoint")
(include-book "defbinding" :dir :util)

(local (include-book "iff" :dir :util))

;; DAG -- it would be nice to push this back ..
(defthm disjoint-remove-list
  (disjoint (remove-list x y) x)
  :rule-classes ((:forward-chaining 
		  :trigger-terms ((remove-list x y)))))

(defun setequiv (x y)
  (declare (type t x y))
  (and (subsetx x y)
       (subsetx y x)))

;; For use in binding hypotheses ..
(def::binding setequiv)

(defcong equiv equal (setequiv x y) 1)
(defcong equiv equal (setequiv x y) 2)

(defequiv setequiv)

(defcong setequiv setequiv (cons a x) 2)

(defcong setequiv equal (memberp a x) 2)

(defcong setequiv equal (subsetp x y) 1)
(defcong setequiv equal (subsetp x y) 2)

(defcong setequiv setequiv (remove a x) 2)

(defcong setequiv setequiv (remove-list x y) 2)

(defthm setequiv-cons-commute
  (setequiv (cons a (cons b x))
	    (cons b (cons a x))))

(defthm setequiv-remove-cons-duplicates
  (setequiv (cons a (cons a b))
	    (cons a b)))

(defthm setequiv-append-commute
  (setequiv (append x (append y z))
	    (append y (append x z))))

(defthm setequiv-remove-append-duplicates
  (setequiv (append x (append x y))
	    (append x y)))

(defthm weak-right-normalization-cons
  (implies
   (memberp a x)
   (setequiv (cons a x) x)))

(defthm weak-right-normalization-append
  (implies
   (subsetp x y)
   (setequiv (append x y) y)))


;; This should move to the "remove" file.
(defthm weak-right-normalization-remove
  (implies
   (not (memberp a x))
   (equiv (remove a x) x)))

(defthmd existential-setequiv-reduction
  (equal (setequiv x y)
	 (and (equal (memberp a x) (memberp a y))
	      (setequiv (remove a x) (remove a y)))))

(defthm open-setequiv-on-not-consp
  (implies
   (not (consp x))
   (equal (setequiv x y)
	  (not (consp y)))))

(in-theory (disable setequiv))

(defthm not-membership-of-setequiv-lhs-fwd
  (implies
   (and
    (not (list::memberp a lhs))
    (list::setequiv lhs rhs))
   (not (list::memberp a rhs)))
  :rule-classes (:forward-chaining))

(defthm membership-of-setequiv-rhs-fwd
  (implies
   (and
    (list::memberp a rhs)
    (list::setequiv lhs rhs))
   (list::memberp a lhs))
  :rule-classes (:forward-chaining))

(defthm membership-of-setequiv-lhs-fwd
  (implies
   (and
    (list::memberp a lhs)
    (list::setequiv lhs rhs))
   (list::memberp a rhs))
  :rule-classes (:forward-chaining))

(defthmd open-setequiv-on-memberp
  (implies
   (memberp a y)
   (equal (setequiv x y)
	  (and (memberp a x)
	       (setequiv (remove a x) (remove a y)))))
  :hints (("Goal" :use existential-setequiv-reduction)))

(defthm setequiv-remove-definition
  (equal (setequiv x y)
	 (if (consp x)
	     (and (memberp (car x) y)
		  (setequiv (remove (car x) x) (remove (car x) y)))
	   (not (consp y))))
  :hints (("Goal" :in-theory (enable open-setequiv-on-memberp)))
  :rule-classes (:definition))

;; We are doing a "remove induction"

(local (in-theory (disable SUBSET-MEMBERSHIP-FREE-MEMBERP)))

(defcong setequiv equal (disjoint x y) 2)

(encapsulate
 ()

 (local (include-book "remove-induction"))
 
 (defcong setequiv equal (disjoint x y) 1
   :hints (("Goal" :in-theory (enable disjoint-remove-reduction-1
				      open-setequiv-on-memberp
				      open-disjoint-on-memberp)
	    :induct (remove-induction-2 x x-equiv))))

 ;;
 ;; We do this here to take advantage of the remove-induction scheme.
 ;;
 (defcong setequiv equal (remove-list x y) 1
   :hints (("Goal" :induct (remove-induction-2 x x-equiv))))

 (defthmd open-setequiv-on-subsetp
   (implies
    (subsetp a x)
    (equal (setequiv x y)
	   (and (subsetp a y)
		(setequiv (remove-list a x) (remove-list a y)))))
   :hints (("Goal" :in-theory (enable open-setequiv-on-memberp)
	    :induct (remove-induction-3 a x y))))

 )

(defthmd setequiv-append-reduction-1
  (equal (setequiv (append x y) z)
	 (and (subsetp x z)
	      (setequiv (remove-list x y) (remove-list x z))))
  :hints (("Goal" :in-theory (enable subsetp-append-2)
	   :use (:instance open-setequiv-on-subsetp
			   (a x)
			   (x (append x y))
			   (y z)))))
	   
(defchoose setfix x (y)
  (setequiv x y)
  :strengthen t)

(defthm setequiv-implies-equal-setfix-1
  (implies (setequiv y y1)
	   (equal (setfix y) (setfix y1)))
  :hints (("Goal" :use (:instance setfix (acl2::y1 y1))))
  :rule-classes (:congruence))

(defthm setfix-fixes
  (setequiv (setfix x) x)
  :hints (("Goal" :use ((:instance setfix (y x))))))

(defund setfixed-p (x)
  (equal x (setfix x)))

(encapsulate
 ()

 ;; anything that fixes to this point is equiv
 
 (local
  (defthm any-fix-is-equiv
    (implies (equal y (setfix x))
	     (setequiv y x))
    :rule-classes nil)
  )

 (local
  (defthmd equal-setfix-implies-setequiv
    (implies (equal (setfix y) (setfix x))
	     (equal (setequiv y x) t))
    :hints (("Goal" :use (:instance any-fix-is-equiv (y (setfix y))))))
  )

 (defthmd setequiv-setfix-reduction
   (equal (setequiv x y)
	  (equal (setfix x) (setfix y)))
   :hints (("Goal" :in-theory (enable equal-setfix-implies-setequiv))))
   
 )

(defthm setfixed-p-setfix
  (setfixed-p (setfix x))
  :hints (("Goal" :in-theory (enable setfixed-p))))

(defthm setfixed-p-setfix-reduction
  (implies
   (setfixed-p x)
   (equal (setfix x) x))
  :hints (("Goal" :in-theory (enable setfixed-p))))

(defthm equal-setfix-to-setequiv
  (equal (equal (setfix x) y)
	 (and (setfixed-p y)
	      (setequiv x y)))
  :hints (("Goal" :in-theory (enable setfixed-p setequiv-setfix-reduction))))

;;
;; Pick-a-point for setequiv
;;

(encapsulate
 ()

 (encapsulate
  (((setequiv-hyps) => *)
   ((setequiv-lhs) => *)
   ((setequiv-rhs) => *)
   )

  (local (defun setequiv-hyps () nil))
  (local (defun setequiv-lhs () nil))
  (local (defun setequiv-rhs () nil))
  
  (defthm setequiv-multiplicity-constraint
    (implies 
     (setequiv-hyps)
     (equal (memberp arbitrary-element (setequiv-lhs))
	    (memberp arbitrary-element (setequiv-rhs))))
    :rule-classes nil)
  )

 (local (defun badguy (x y)
	  (declare (xargs :measure (len x)))
          (cond ((atom x) 
		 (if (consp y) (car y) nil))
                ((not (memberp (car x) y))
                 (car x))
                (t (badguy (remove (car x) x)
			   (remove (car x) y))))))
 
 (local (include-book "remove-induction"))

 (local (defthm badguy-witness
          (equal (setequiv x y)
		 (equal (memberp (badguy x y) x)
			(memberp (badguy x y) y)))))
 
 (defthm setequiv-by-multiplicity-driver
   (implies (setequiv-hyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes nil
   :hints(("Goal" 
           :use ((:instance 
                  setequiv-multiplicity-constraint
                  (arbitrary-element (badguy (setequiv-lhs) (setequiv-rhs))))))))

 (ADVISER::defadvice setequiv-by-multiplicity
   (implies (setequiv-hyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes (:pick-a-point :driver setequiv-by-multiplicity-driver))

 )

(defthm setequiv-append-swap
  (setequiv (append x y)
	    (append y x))
  :hints (("Goal" :in-theory (disable SETEQUIV-APPEND-REDUCTION-1))))

(defthm append-cons-commute
  (list::setequiv (append x (cons a y))
		  (cons a (append x y))))

(defrefinement list::equiv list::setequiv)

;;
;; We could use definition rules for this .. (??)
;;
(defthmd open-setequiv-on-consp-1
  (implies
   (consp x)
   (equal (list::setequiv x y)
	  (and (list::memberp (car x) y)
	       (list::setequiv (remove (car x) x) (remove (car x) y)))))
  :hints (("Goal" :in-theory (enable list::setequiv))))

(defcong list::setequiv list::setequiv (append x y) 1)
(defcong list::setequiv list::setequiv (append x y) 2)


(defun setintersection (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y)
	  (cons (car x) (setintersection (cdr x) y))
	(setintersection (cdr x) y))
    (if (null y) nil x)))

;; (= (setintersection x x) x)
;; (= (setintersection x nil) nil)
;; (= (setintersection nil x) nil)

(defthm true-listp-setintersection
  (implies
   (true-listp x)
   (true-listp (setintersection x y)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((setintersection x y)))))

(defthm memberp-setintersection
  (equal (memberp a (setintersection x y))
	 (and (memberp a x)
	      (memberp a y))))

(defthm dual-membership-implies-membership-setintersection
  (implies
   (and
    (list::memberp a lhs)
    (list::memberp a rhs))
   (list::memberp a (list::setintersection lhs rhs)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((list::setintersection lhs rhs)))))

(defthm membership-setintersection-implies-dual-membership
  (implies
   (list::memberp a (list::setintersection lhs rhs))
   (and
    (list::memberp a lhs)
    (list::memberp a rhs)))
  :rule-classes (:forward-chaining))

(defcong setequiv setequiv (setintersection x y) 1)
(defcong setequiv setequiv (setintersection x y) 2)

(defthm setintersection-commute
  (setequiv (setintersection x y)
	    (setintersection y x)))

(defthmd subsetp-setintersection-helper
  (implies
   (subsetp x y)
   (equal (setintersection x y) 
	  (if (null y) (list::fix x) x))))

(local (in-theory (enable subsetp-setintersection-helper)))

(defthm setintersection-id
  (equal (setintersection x x) x))

(defthm subsetp-setintersection
  (implies
   (subsetp x y)
   (setequiv (setintersection x y) x)))

(defthm setintersection-null-1
  (equal (setintersection nil x) nil))

(defthm setintersection-null-2
  (equal (setintersection x nil) nil))

(defthm disjoint-setintersection
  (implies
   (disjoint x y)
   (equiv (setintersection x y) nil)))

;; What kinds of rules will be useful?  If setequiv appears in the
;; conclusion we should be using pick-a-point.  If it appears in
;; the hypothesis .. what?

(defthm setintersection-append-1
  (setequiv (setintersection (append x y) z)
	    (append (setintersection x z)
		    (setintersection y z))))

(defthm setintersection-append-2
  (setequiv (setintersection x (append y z))
	    (append (setintersection x y)
		    (setintersection x z))))

(defthm subset-intersect-forward
  (and (subsetp (setintersection x y) x)
       (subsetp (setintersection x y) y))
  :rule-classes ((:forward-chaining :trigger-terms ((setintersection x y)))))

(in-theory (disable setintersection))

;;
;; ie: x - y
;; ;; this is just remove-list with the arguments reversed (!)

(defun setdifference (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y)
	  (setdifference (cdr x) y)
	(cons (car x) (setdifference (cdr x) y)))
    (if (null y) x nil)))

;; (= (setdifference x x)   nil)
;; (= (setdifference x nil)   x)

(defthm true-listp-setdifference
  (implies
   (true-listp x)
   (true-listp (setdifference x y)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((setdifference x y)))))

(defthm memberp-setdifference
  (equal (memberp a (setdifference x y))
	 (and (memberp a x)
	      (not (memberp a y)))))

(defthm memberp-setdifference-implies
  (implies
   (memberp a (setdifference x y))
   (and (memberp a x)
	(not (memberp a y))))
  :rule-classes (:forward-chaining))

(defthm not-memberp-setdifference-implies-1
  (implies
   (and
    (not (memberp a (setdifference lhs rhs)))
    (memberp a lhs))
   (memberp a rhs))
  :rule-classes (:forward-chaining))

(defthm not-memberp-setdifference-implies-2
  (implies
   (and
    (not (memberp a (setdifference lhs rhs)))
    (not (memberp a rhs)))
   (not (memberp a lhs)))
  :rule-classes (:forward-chaining))

(defthm implies-not-memberp-setdifference-1
  (implies
   (memberp a sub)
   (not (memberp a (setdifference z sub))))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((setdifference z sub)))))

(defthm implies-not-memberp-setdifference-2
  (implies
   (not (memberp a z))
   (not (memberp a (setdifference z sub))))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((setdifference z sub)))))

(defthm implies-memberp-setdifference
  (implies
   (and (memberp a x)
	(not (memberp a y)))
   (memberp a (setdifference x y)))
  :rule-classes ((:forward-chaining
		  :trigger-terms ((setdifference x y)))))

(defthm subset-diff-forward
  (and (list::subsetp (setdifference x y) x)
       (disjoint (setdifference x y) y))
  :rule-classes ((:forward-chaining :trigger-terms ((setdifference x y)))))

(defcong setequiv setequiv (setdifference x y) 1)
(defcong setequiv setequiv (setdifference x y) 2)

(defthmd subsetp-setdifference-helper
  (implies
   (subsetp x y)
   (equal (setdifference x y)
	  (if (null y) x nil))))

(local (in-theory (enable subsetp-setdifference-helper)))

(defthm setdifference-nil-2
  (equal (setdifference x nil) x))

(defthm setdifference-nil-1
  (equal (setdifference nil y) nil))

(defthm subsetp-setdifference
  (implies
   (subsetp x y)
   (equiv (setdifference x y) nil)))

(defthm setdifference-id
  (equal (setdifference x x) nil))

(defthm disjoint-setdifference
  (implies
   (disjoint x y)
   (equiv (setdifference x y) x)))

(defthm setdifference-append-1
  (setequiv (setdifference (append x y) z)
	    (append (setdifference x z)
		    (setdifference y z))))

(in-theory (disable setdifference))

(defthm setdifference-cons-lhs
  (setequiv (setdifference x (cons a y))
	    (remove a (setdifference x y))))

(defthm setdifference-is-remove-list
  (list::setequiv (setdifference x y)
		  (remove-list y x)))

;; Where should this (and similar rules) go?

(defthm subsetp-remove-by-subset
  (implies
   (subsetp x y)
   (subsetp (remove a x) y))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((remove a x)))))


