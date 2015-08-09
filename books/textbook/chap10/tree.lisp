; Section 10.4 Tree Manipulation

(in-package "ACL2")

(defun flatten (x)
  (cond ((atom x) (list x))
        (t (append (flatten (car x)) (flatten (cdr x))))))

(defun mc-flatten (x a)
  (cond ((atom x) (cons x a))
        (t (mc-flatten (car x)
                       (mc-flatten (cdr x) a)))))

(defthm associativity-of-append
  (equal (append (append x y) z)
	 (append x (append y z))))

(defthm flatten-mc-flatten-lemma
  (equal (mc-flatten x a)
         (append (flatten x) a)))

(defthm flatten-mc-flatten
  (equal (mc-flatten x nil)
         (flatten x)))

(defun gopher (x)
  (declare (xargs :measure (acl2-count (car x))))
  (if (or (atom x)
          (atom (car x)))
      x
    (gopher (cons (caar x) (cons (cdar x) (cdr x))))))


(defthm gopher-acl2-count-cdr
  (implies (consp x)
	   (< (acl2-count (cdr (gopher x)))
	      (acl2-count x))))

(defun samefringe (x y)
  (if (or (atom x)
	  (atom y))
      (equal x y)
    (and (equal (car (gopher x))
		(car (gopher y)))
	 (samefringe (cdr (gopher x))
		     (cdr (gopher y))))))

(defthm car-gopher-car-flatten
  (implies (consp x)
	   (equal (car (gopher x))
		  (car (flatten x)))))

(defthm cdr-flatten-gopher
  (implies (consp x)
	   (equal (flatten (cdr (gopher x)))
		  (cdr (flatten (gopher x))))))

(defthm flatten-gopher
  (equal (flatten (gopher x))
	 (flatten x)))

#|
(defthm cdr-flatten-gopher
  (implies (consp x)
           (equal (flatten (cdr (gopher x)))
                  (cdr (flatten x)))))
|#

(defthm correctness-of-samefringe
  (equal (samefringe x y)
         (equal (flatten x)
                (flatten y))))

