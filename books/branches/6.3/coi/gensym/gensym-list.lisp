#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "gensym")

(include-book "coi/lists/disjoint" :dir :system)
(include-book "coi/bags/basic" :dir :system)

;;
;; Given a list of bases, construct a new set of symbols
;;

(defun gensym::gensym-list (list omit)
  (declare (type (satisfies true-listp) omit))
  (if (consp list)
      (let ((a (gensym::gensym (car list) omit)))
	(cons a (gensym::gensym-list (cdr list) (cons a omit))))
    nil))

(defthm gensym::len-gensym-list
  (equal (len (gensym::gensym-list list omit))
	 (len list)))

(defthm gensym::memberp-gensym-list-forward-1
  (implies
   (list::memberp a omit)
   (not (list::memberp a (gensym::gensym-list list omit))))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::memberp-gensym-list-forward-2
  (implies
   (list::memberp a (gensym::gensym-list list omit))
   (not (list::memberp a omit)))
  :rule-classes (:rewrite :forward-chaining))

(defthm gensym::unique-gensym-list
  (bag::unique (gensym::gensym-list list omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::disjoint-gensym-list
  (bag::disjoint (gensym::gensym-list list omit) omit)
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::symbol-listp-gensym-list
  (symbol-listp (gensym::gensym-list list omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

;;
;; Given a base and a count, construct n new symbols from base.
;;

(defun gensym::gensym-n (n base omit)
  (declare (type (integer 0 *) n)
	   (type (satisfies true-listp) omit))
  (if (zp n) nil
    (let ((a (gensym::gensym base omit)))
      (cons a (gensym::gensym-n (1- n) base (cons a omit))))))


(defthm gensym::memberp-gensym-n-forward-1
  (implies
   (list::memberp a omit)
   (not (list::memberp a (gensym::gensym-n n base omit))))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::memberp-gensym-n-forward-2
  (implies
   (list::memberp a (gensym::gensym-n n base omit))
   (not (list::memberp a omit)))
  :rule-classes (:rewrite :forward-chaining))

(defthm gensym::len-gensym-n
  (equal (len (gensym::gensym-n n base omit))
	 (nfix n)))

(defthm gensym::unique-gensym-n
  (bag::unique (gensym::gensym-n n base omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::disjoint-gensym-n
  (bag::disjoint (gensym::gensym-n n base omit) omit)
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::symbol-listp-gensym-n
  (symbol-listp (gensym::gensym-n n base omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))
