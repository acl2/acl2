#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "SYMBOL-FNS")
(include-book "symbol-fns" :dir :symbol-fns)

(defun collect-variables-rec (fn term res)
  (declare (type t fn term res))
  (if (consp term)
      (if (consp (car term))
	  (let ((res (collect-variables-rec t (car term) res)))
	    (collect-variables-rec nil (cdr term) res))
	(if fn (collect-variables-rec nil (cdr term) res)
	  (let ((res (append (if (symbolp (car term)) (list (car term)) nil)
			     res)))
	    (collect-variables-rec nil (cdr term) res))))
    res))

(defthm symbol-listp-collect-variables-rec
  (implies
   (symbol-listp res)
   (symbol-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defthm true-listp-collect-variables-rec
  (implies
   (true-listp res)
   (true-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defmacro collect-variables (term)
  `(remove-duplicates-equal (collect-variables-rec t ,term nil)))

(defun join-lists (list1 list2)
  (declare (type t list1 list2))
  (if (and (consp list1)
	   (consp list2))
      (cons (list (car list1) (car list2))
	    (join-lists (cdr list1) (cdr list2)))
    nil))
