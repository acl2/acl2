#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; Multiappend Function
;;
;; map "append" over a set.

(in-package "SET")
(include-book "multicons")
(local (include-book "../util/iff"))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defund multiappend (list x)
  (if (consp list)
      (set::multicons (car list)
		      (set::multiappend (cdr list) x))
    (set::sfix x)))

(local (in-theory (enable multiappend)))

(defthm multiappend-set
  (setp (multiappend list X)))

(defthm listsetp-of-multiappend
  (equal (listsetp (multiappend a X))
         (all<true-listp> X))
  :hints (("goal" :in-theory (enable listsetp))))


(local
 (include-book "arithmetic/top-with-meta" :dir :system)
 )

(defun multiappend-2-induction (list path x)
  (if (and (consp list)
	   (consp path))
      (set::multicons (car list)
		      (set::multiappend-2-induction (cdr list) (cdr path) x))
    (cons path (set::sfix x))))

(defthm multiappend-in
  (equal (in path (multiappend a X))
         (and (equal (list::firstn (len a) path) (list::fix a))
              (in (list::nthcdr (len a) path) X)))
  :hints(("Goal" :in-theory (enable list::fix)
	  :induct (multiappend-2-induction a path X))))
