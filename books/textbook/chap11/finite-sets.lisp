(in-package "ACL2")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

; ---------------------------------------------------------------------------
; Exercise 11.53

(defun in-count (a b)
  (cons (+ (acl2-count a) (acl2-count b) 1) 0))

(defun ==-count (a b)
  (cons (car (in-count a b)) 1))

(mutual-recursion
(defun in (a X)
  (declare (xargs :measure (in-count a X)))
  (if (consp X)
      (if (atom a)
	  (or (equal a (car X))
	      (in a (cdr X)))
	(or (== a (car X))
	    (in a (cdr X))))
    nil))

(defun =< (a b)
  (declare (xargs :measure (in-count a b)))
  (if (consp a)
      (and (in (car a) b)
	   (=< (cdr a) b))
    t))

(defun == (a b)
  (declare (xargs :measure (==-count a b)))
  (and (=< a b)
       (=< b a))))

; ---------------------------------------------------------------------------
; Exercise 11.54

(defthm example-54
  (and (== '((1 2)) '((2 1)))
       (=< '((2 1) (1 2)) '((2 1)))
       (not (in '((1)) '((2 (1)) (1 2))))
       (== '(() (1 2 1) (2 1) x)
           '((1 2) x ()))
       (== 'x 1)
       (=< 'x 1))
  :rule-classes nil)

; ---------------------------------------------------------------------------
; Exercise 11.55

(defun induct-hint1 (x)
  (if (consp x)
      (list (induct-hint1 (car x))
	    (induct-hint1 (cdr x)))
    x))

(defthm cons-preserves-subset
  (implies (=< X Y)
	   (=< X (cons a Y)))
  :hints (("goal" :induct (induct-hint1 x))))

(defthm subset-reflexive
  (=< X X)
  :hints (("Goal" :induct (induct-hint1 x))))

; ---------------------------------------------------------------------------
; Exercise 11.56

(defthm acl2-count-cons
  (implies (consp x)
	   (< 0 (acl2-count x)))
  :rule-classes :linear)

(defun ind-2 (x y z)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y) (acl2-count z))))
  (if (consp x)
      (if (atom (cdr x))
	  (if (atom (cdr y))
	      (if (atom (cdr z))
		  (list (ind-2 (car x) (car y) (car z))
			(ind-2 (car z) (car y) (car x)))
		(list (ind-2 x y (list (car z)))
		      (ind-2 x y (cdr z))))
	    (list (ind-2 x (list (car y)) z)
		  (ind-2 x (cdr y) z)))
	(list (ind-2 (list (car x)) y z)
	      (ind-2 (cdr x) y z)))
    x))

(defthm subset-transitive
  (implies (and (=< X Y)
		(=< Y Z))
	   (=< X Z))
  :hints (("goal"
	   :induct (ind-2 x y z))))

; ---------------------------------------------------------------------------
; Exercise 11.57

(defequiv ==)
