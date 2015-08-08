(in-package "ACL2")
;;
(include-book "util")
;;
(defun b-p (x)
  (declare (xargs :guard t))
  (or (booleanp x)
      (equal x 'x)
      (equal x 'top)))

(defthm booleanp-is-b-p
  (implies (booleanp b) (b-p b)))

(defthm x-is-b-p   (b-p 'x))
(defthm top-is-b-p (b-p 'top))

;;;
;;;
;;;

(defconst *b-not-table*   '(x   t   nil top) )

(defconst *b-and-table* '( (x   nil x   nil)
			   (nil nil nil nil)
			   (x   nil t   top)
			   (nil nil top top) ))

(defconst *b-or-table*  '( (x   x   t   t  )
			   (x   nil t   top)
			   (t   t   t   t  )
			   (t   top t   top) ))

(defconst *b-lte-table* '( (t   t   t   t  )
			   (nil t   nil t  )
			   (nil nil t   t  )
			   (nil nil nil t  ) ))

(defconst *b-lub-table* '( (x   nil t   top)
			   (nil nil top top)
			   (t   top t   top)
			   (top top top top) ))


(defun b-nth (b lst)
  (declare (xargs :guard (and (b-p b) (true-listp lst))))
  (if (equal b 'x)
      (first lst)
    (if (equal b nil)
	(second lst)
      (if (equal b t)
	  (third lst)
	(if (equal b 'top)
	    (fourth lst)
	  nil)))))
;;;
;;;
;;;
(defuntyped b-not ((b-p b)) t
  b-p nil
  (if (booleanp b)
      (not b)
    b))

(defthm b-not-check
  (equal (b-nth b *b-not-table*)
	 (b-not b))
  :rule-classes nil)
;;;
;;;
;;;
(defuntyped b-and ((b-p b1) (b-p b2)) t
  b-p nil
  (if (equal b1 nil)
      nil
    (if (equal b2 nil)
	nil
      (if (equal b1 t)
	  b2
	(if (equal b2 t)
	    b1
	  (if (equal b1 'x)
	      (if (equal b2 'x)
		  'x
		nil)
	    (if (equal b2 'x)
		nil
	      'top)))))))

(defthm b-and-check
  (equal (b-nth b2 (b-nth b1 *b-and-table*))
	 (b-and b1 b2))
  :rule-classes nil)
;;;
;;;
;;;
(defuntyped b-or ((b-p b1) (b-p b2)) t
  b-p nil
  (if (equal b1 t)
      t
    (if (equal b2 t)
	t
      (if (equal b1 nil)
	  b2
	(if (equal b2 nil)
	    b1
	  (if (equal b1 'x)
	      (if (equal b2 'x)
		  'x
		t)
	    (if (equal b2 'x)
		t
	      'top)))))))

(defthm b-or-check
  (equal (b-nth b2 (b-nth b1 *b-or-table*))
	 (b-or b1 b2))
  :rule-classes nil)
;;;
;;;
;;;



(defuntyped b-lte ((b-p b1) (b-p b2)) t
  b-p nil
  (if (equal b1 'x)
      t
    (if (equal b2 'top)
	t
      (and (booleanp b1) (booleanp b2) (equal b1 b2)))))

(defthm b-lte-check
  (equal (b-nth b2 (b-nth b1 *b-lte-table*))
	 (b-lte b1 b2))
  :rule-classes nil)

(defthm b-lte-reflexive
  (implies (b-p b)
	   (b-lte b b)))

(defthm b-lte-antisymmetric
  (implies (and (b-p a)
		(b-p b)
		(b-lte a b)
		(b-lte b a))
	   (equal a b))
  :rule-classes nil)

(defthm b-lte-transitive
  (implies (and (b-p a)
		(b-p b)
		(b-lte a b)
		(b-lte b c))
	   (b-lte a c)))
;;;
;;;
;;;
(defuntyped b-lub ((b-p b1) (b-p b2)) t
  b-p nil
  (if (equal b1 'x)
      b2
    (if (equal b2 'x)
	b1
      (if (and (booleanp b1) (booleanp b2) (equal b1 b2))
	  b1
	'top))))

(defthm b-lub-check
  (equal (b-nth b2 (b-nth b1 *b-lub-table*))
	 (b-lub b1 b2))
  :rule-classes nil)



(defthm b-not-cases
  (and (equal (b-not 'x)   'x)
       (equal (b-not t)    nil)
       (equal (b-not nil)  t)
       (equal (b-not 'top) 'top)
       ))
;;;
;;;
;;;
(defthm b-lte-cases
  (and
   (b-lte 'x 'x)
   (b-lte 'x t)
   (b-lte 'x nil)
   (b-lte 'x 'top)

   (not (b-lte t 'x))
        (b-lte t t)
   (not (b-lte t nil))
        (b-lte t 'top)

   (not (b-lte nil 'x))
   (not (b-lte nil t))
        (b-lte nil nil)
        (b-lte nil 'top)

   (not (b-lte 'top 'x))
   (not (b-lte 'top t))
   (not (b-lte 'top nil))
        (b-lte 'top 'top)

   (implies (b-p x) (b-lte x x))
   (implies (and (b-lte x y) (b-lte y z)) (b-lte x z))

   ))


;;;
;;;
;;;

(defthm drop-not
  (implies (booleanp x)
	   (equal (b-not x)
		  (not x))))

(defthm b-not-monotone
  (implies (and (b-lte x1 x2)
		)
	   (b-lte (b-not x1)
		  (b-not x2))))

(defthm drop-and
  (implies (and (booleanp x)
		(booleanp y))
	   (equal (b-and x y)
		  (and x y))))

(defthm b-and-monotone
  (implies (and (b-lte x1 x2)
		(b-lte y1 y2)
		)
	   (b-lte (b-and x1 y1)
		  (b-and x2 y2))))

(defthm drop-or
  (implies (and (booleanp x)
		(booleanp y))
	   (equal (b-or x y)
		  (or x y))))

(defthm b-or-monotone
  (implies (and (b-lte x1 x2)
		(b-lte y1 y2)
		)
	   (b-lte (b-or x1 y1)
		  (b-or x2 y2))))
;;;
;;;
;;;

(defuntyped b-if ((b-p x) (b-p y) (b-p z)) t
  b-p nil
  (b-or (b-and x y) (b-and (b-not x) z)))


(defthm drop-if
  (implies (and (booleanp x)
		(booleanp y)
		(booleanp z))
	   (equal (b-if x y z)
		  (if x y z))))
(defthm b-if-monotone
  (implies (and (b-lte x1 x2)
		(b-lte y1 y2)
		(b-lte z1 z2))
	   (b-lte (b-if x1 y1 z1)
		  (b-if x2 y2 z2))))

(defthm b-lte-b1-not-x-b2-is-top
  (implies (and (b-p b1)
		(b-p b2)
		(not (equal b1 b2))
		(not (equal b1 'x))
		(b-lte b1 b2)
		)
	   (equal b2 'top))
  :rule-classes nil)

(in-theory (disable b-p))

