(in-package "ACL2")

;; The rename books are arranged like this:
;;
;;          rename-top
;;             /  \
;; rename-unique  rename-sound
;;             \  /
;;            rename
;;
;; This book (rename) has the main definitions and some
;; preservation-of-property theorems.  The top definition
;; is (rename-all f), which renames all bound variables
;; (left-to-right, in separate passes) to unique new
;; variable names.

(include-book "wfftype")

;;===================== step-wise rename

;; Function rename-bound (f old new) renames the first bound occurrence
;; of old to new.  Safeness of "new" is not checked.

(defun rename-bound (f old new)
  (declare (xargs :guard (and (wff f)
			      (variable-term old)
			      (variable-term new))))
  (cond ((wfnot f) (list 'not (rename-bound (a1 f) old new)))
	((wfbinary f) (if (bound-occurrence old (a1 f))
			  (list (car f)
				(rename-bound (a1 f) old new)
				(a2 f))
			  (list (car f)
				(a1 f)
				(rename-bound (a2 f) old new))))
	((wfquant f) (if (equal (a1 f) old)
			 (list (car f)
			       new
			       (subst-free (a2 f) (a1 f) new))
		         (list (car f)
			       (a1 f)
			       (rename-bound (a2 f) old new))))
	(t f)))

(defthm rename-bound-wff
  (implies (and (wff f)
		(variable-term new))
	   (wff (rename-bound f old new))))

(defthm rename-bound-preserves-car
  (equal (car (rename-bound f old new)) (car f)))

(defthm rename-bound-preserves-nnfp
  (implies (nnfp f)
	   (nnfp (rename-bound f x y))))

;;===============================================
;; Function rename-bunch (f oldvars newvars) renames the members of oldvars
;; to the corresponding members of newvars.

(defun rename-bunch (f oldvars newvars)
  (declare (xargs :guard (and (wff f) (var-list oldvars) (var-list newvars)
			      (equal (len oldvars) (len newvars)))))
  (if (or (atom oldvars) (atom newvars))
      f
      (rename-bunch (rename-bound f (car oldvars) (car newvars))
		    (cdr oldvars) (cdr newvars))))

(defthm rename-bunch-wff
  (implies (and (wff f)
		(var-list newvars))
	   (wff (rename-bunch f oldvars newvars))))

(defthm rename-bunch-preserves-nnfp
  (implies (nnfp f)
	   (nnfp (rename-bunch f old new))))

;; Function (all-safe vars f) is true if no member of vars has a
;; bound or free occurrence in formula f.

(defun all-safe (vars f)
  (declare (xargs :guard (and (wff f) (var-list vars))))
  (cond ((atom vars) t)
	((bound-occurrence (car vars) f) nil)
	((free-occurrence (car vars) f) nil)
	(t (all-safe (cdr vars) f))))

;;------------------------------------------------
;; Now what should the newvars be?
;;
;; Get the gensym book, define a function to get a list of new
;; symbols, and prove some properties.

(include-book "gensym-e")

(defun gen-symbols (n sym lst)
  (declare (xargs :guard (and (natp n)
			      (symbolp sym)
			      (symbol-listp lst))))
  (if (zp n)
      nil
    (let ((newsym (gen-symbol sym lst)))
      (cons newsym (gen-symbols (1- n) sym (cons newsym lst))))))

(defthm gen-symbols-ok
  (implies (symbolp sym)
	   (disjoint (gen-symbols n sym lst) lst)))

(defthm gen-symbols-len
  (implies (natp n)
	   (equal (len (gen-symbols n sym lst)) n)))

(defthm member-member-not-disjoint
  (implies (and (member-equal x a)
		(member-equal x b))
	   (not (disjoint a b)))
  :rule-classes nil)

(defthm gen-symbols-member
  (implies (symbolp sym)
	   (not (member-equal a (gen-symbols n sym (cons a lst)))))
  :hints (("Goal"
	   :use ((:instance member-member-not-disjoint
			    (x a)
			    (a (gen-symbols n sym (cons a lst)))
			    (b (cons a lst)))))))

(defthm gen-symbols-setp
  (implies (symbolp sym)
	   (setp (gen-symbols n sym lst))))

;;------------------------------------------------

(defthm var-list-symbol-listp
  (implies (var-list lst)
	   (symbol-listp lst)))

(defun safe-list (f)
  (declare (xargs :guard (wff f)))
  (gen-symbols (len (quantified-vars f))
	       'v
	       (append (quantified-vars f) (free-vars f))))

(defthm free-free-append
  (implies (free-occurrence x f)
	   (member-equal x (append (quantified-vars f)
				   (free-vars f))))
  :hints (("Goal"
         :use ((:instance free-free)))))

(defthm bound-bound-append
  (implies (bound-occurrence x f)
	   (member-equal x (append (quantified-vars f)
				   (free-vars f))))
  :hints (("Goal"
         :use ((:instance quantified-iff-bound)))))

(defthm disjoint-all-safe
  (implies (disjoint a (append (quantified-vars f) (free-vars f)))
	   (all-safe a f)))

(defthm safe-list-all-safe
  (all-safe (safe-list f) f))

(defmacro var-set (vars)
  (list 'and (list 'var-list vars) (list 'setp vars)))

(defthm gen-symbols-var-list
  (var-list (gen-symbols n sym lst)))

(defthm safe-list-varset
  (var-set (safe-list f)))

;;---------------------------------
;; Function (rename-all f) renames all bound variables.

(defthm var-list-append
  (implies (and (var-list qvs0)
		(var-list qvs))
	   (var-list (append qvs0 qvs))))

(defun rename-all (f)
  (declare (xargs :guard (wff f)))
  (rename-bunch f (quantified-vars f) (safe-list f)))

(defthm rename-all-wff
  (implies (wff f)
	   (wff (rename-all f))))

(defthm rename-all-preserves-nnfp
  (implies (nnfp f)
	   (nnfp (rename-all f))))

;;------------------------------------------------
;; Prove that the rename functions preserve free-vars

(defthm rename-bound-preserves-free-vars
  (implies (and (variable-term y)
		(not (bound-occurrence y f))
		(not (free-occurrence y f)))
	   (equal (free-vars (rename-bound f x y))
		  (free-vars f))))

(defthm rename-bound-doesnt-introduce-free-vars
  (implies (not (free-occurrence z f))
           (not (free-occurrence z (rename-bound f x y)))))

(defthm rename-bound-still-safe
  (implies (and (all-safe new2 f)
		(not (member-equal new1 new2))
		(not (bound-occurrence new1 f))
		(not (free-occurrence new1 f)))
	   (all-safe new2 (rename-bound f old1 new1))))

(defthm rename-bunch-preserves-free-vars
  (implies (and (all-safe new f)
		(var-set new))
	   (equal (free-vars (rename-bunch f old new))
		  (free-vars f)))
  :hints (("Goal"
	   :induct (rename-bunch f old new))))

(defthm rename-all-preserves-free-vars
  (equal (free-vars (rename-all f))
	 (free-vars f)))
