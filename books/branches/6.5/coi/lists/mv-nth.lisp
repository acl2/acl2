#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

;We make our own mv-nth function, so that we can disable it without getting theory warnings
;about how mv-nth cannot be completely disabled (since it is built-in in a deep way).
(defund val (n l)
  (declare (xargs :guard (and (integerp n)
                              (>= n 0)
                              (true-listp l))))
  (mv-nth n l))

(defthm mv-nth-to-val
  (equal (mv-nth n l)
         (val n l))
  :hints (("Goal" :in-theory (enable val))))

(theory-invariant (incompatible (:rewrite mv-nth-to-val)
                                (:definition val)))

(defthm val-of-cons
  (equal (val n (cons a l))
         (if (zp n)
             a
           (val (+ -1 n) l)))
  :hints (("Goal" :in-theory (e/d (val) ( mv-nth-to-val)))))

(defmacro v0 (x)
  `(val 0 ,x))

(defmacro v1 (x)
  `(val 1 ,x))

(defmacro v2 (x)
  `(val 2 ,x))

(defmacro v3 (x)
  `(val 3 ,x))

(defmacro v4 (x)
  `(val 4 ,x))

(defmacro met (binding &rest rst)
  (declare (xargs :guard (and (consp binding)
			      (consp (cdr binding))
			      (null  (cddr binding)))))
  `(mv-let ,(car binding) ,(cadr binding)
	   ,@rst))
