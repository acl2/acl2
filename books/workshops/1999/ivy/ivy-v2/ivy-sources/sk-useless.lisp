(in-package "ACL2")

;; In this book we prove that if a formula lacks a given function
;; symbol, and if an interpretation has a corresponding function
;; at the start of its function list, then we can delete the
;; function from the function list when evaluating the formula.

(include-book "sk-misc-lemmas")

;;------------------------

(defthm eval-term-list-with-useless-function
  (implies (not (member-equal fsym (funcs-in-term-list l)))
	   (equal (eval-term-list l (list* i1 i3
					   (cons (cons fsym n) func)
					   i4))
		  (eval-term-list l (list* i1 i3 i4))))
  :hints (("Goal"
	   :in-theory (enable domain))))

(defthm not-member-funcs-a
  (implies (and (consp l)
		(not (member-equal fsym (funcs-in-term-list l))))
	   (not (member-equal fsym (funcs-in-term-list (list (car l)))))))

(defthm not-member-funcs-b
  (implies (not (member-equal fsym (funcs-in-term-list (cons a l))))
	   (not (member-equal fsym (funcs-in-term-list (list a)))))
  :hints (("Goal"
         :use ((:instance not-member-funcs-a (l (cons a l)))))))

(defthm not-member-union-forward-right
  (implies (not (member-equal x (union-equal a b)))
	   (not (member-equal x b)))
  :rule-classes :forward-chaining)

(defthm not-member-funcs-subst-term-list
  (implies
   (and (domain-term e)
	(not (member-equal fsym (funcs-in-term-list l))))
   (not (member-equal fsym (funcs-in-term-list (subst-term-list l x e))))))

(defthm not-member-funcx-subst
  (implies (and (domain-term e)
		(not (member-equal fsym (funcs-in-formula f))))
	   (not (member-equal fsym (funcs-in-formula (subst-free f x e))))))

;;-----------------------
;; Here are the 3 versions of the main result of this book.
;; Prove it with xeval, then use that to get the versions
;; in terms of feval and feval-d.

(defthm xeval-with-useless-function
  (implies (and (not (member-equal fsym (funcs-in-formula f)))
		(domain-term-list (fringe dom)))
	   (equal (xeval f dom (list* (domain i) (relations i)
				      (cons (cons fsym n) func)
				      (functions i)))
		  (xeval f dom (list* (domain i)
				      (relations i)
				      (functions i)))))
  :hints (("Goal"
	   :do-not generalize
	   :in-theory (enable eval-atomic)
	   :induct (xeval-i f dom i))))

(defthm feval-with-useless-function
  (implies (not (member-equal fsym (funcs-in-formula f)))
	   (equal (feval f (list* (domain i) (relations i)
				  (cons (cons fsym n) func)
				  (functions i)))
		  (feval f (list* (domain i)
				  (relations i)
				  (functions i)))))
  :hints (("Goal"
	   :in-theory (enable xeval-feval))))

(defthm feval-d-with-useless-function
  (implies (and (not (member-equal fsym (funcs-in-formula f)))
		(domain-term-list (fringe dom))
		(wfquant f))
	   (equal (feval-d f dom (list* (domain i) (relations i)
					(cons (cons fsym n) func)
					(functions i)))
		  (feval-d f dom (list* (domain i)
					(relations i)
					(functions i)))))
  :hints (("Goal"
	   :in-theory (enable xeval-feval-d))))
