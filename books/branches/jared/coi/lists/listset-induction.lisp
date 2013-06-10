#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

(set-enforce-redundancy t)
(include-book "subsetp")
(include-book "remove")

(local (include-book "set"))

;; DAG: Boy .. this is a lot of work just so that "set" can be local .. (?)

(defun setequiv (x y)
  (declare (type t x y))
  (and (subsetx x y)
       (subsetx y x)))

(defequiv setequiv)

(defcong setequiv equal (memberp a x) 2)

(defcong setequiv equal (subsetp x y) 1)
(defcong setequiv equal (subsetp x y) 2)

(defcong setequiv setequiv (remove a x) 2)

(defcong setequiv equal (remove-list x y) 1)
(defcong setequiv setequiv (remove-list x y) 2)

(defthm weak-right-normalization-cons
  (implies
   (memberp a x)
   (setequiv (cons a x) x)))

(defthm weak-right-normalization-append
  (implies
   (subsetp x y)
   (setequiv (append x y) y)))

(defthm weak-right-normalization-remove
  (implies
   (not (memberp a x))
   (equiv (remove a x) x)))

(defthm open-setequiv-on-not-consp
  (implies
   (not (consp x))
   (equal (setequiv x y)
	  (not (consp y)))))

(in-theory (disable setequiv))

(defchoose setfix x (y)
  (setequiv x y)
  :strengthen t)

(defthm setequiv-implies-equal-setfix-1
  (implies (setequiv y y1)
	   (equal (setfix y) (setfix y1)))
  :rule-classes (:congruence))

(defthm setfix-fixes
  (setequiv (setfix x) x))

(defund setfixed-p (x)
  (equal x (setfix x)))

(defthm setfixed-p-setfix
  (setfixed-p (setfix x)))

(defthm equal-setfix-to-setequiv
  (equal (equal (setfix x) y)
	 (and (setfixed-p y)
	      (setequiv x y))))

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

 (defthm setequiv-by-multiplicity-driver
   (implies (setequiv-hyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes nil)
 
 (ADVISER::defadvice setequiv-by-multiplicity
   (implies (setequiv-hyps)
            (setequiv (setequiv-lhs) (setequiv-rhs)))
   :rule-classes (:pick-a-point :driver setequiv-by-multiplicity-driver))

 )
