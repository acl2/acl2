(in-package "ACL2")

;; This book contains yet another evaluation function, keval.
;;
;; This one is for proving that we can permute universally
;; quantified variables.
;;
;; This is ugly.

(include-book "stage")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;; ---------------------------------------------------------
;; Function (keval vars f dom n d2 i) evaluates (alls vars f);; that is,
;; it tacks on vars to f as universally quantified variables.  The arguments
;; dom and i are the same as xeval, with the following exception.
;; Index n says that when the n-th variable is reached, use d2 as the
;; domain instead of dom.  This is used to prove that we can permute
;; universally quantified variables.  (The analogous thing would work for
;; existentially quantified variables.)

(defun keval (vars f dom n d2 i)
  (declare (xargs :measure (cons (cons (+ 1 (acl2-count vars))
				       (acl2-count dom))
				 (acl2-count d2))
		  :guard (and (var-list vars)
			      (setp vars)
			      (wff f)
			      (not (free-vars (alls vars f)))
			      (integerp n)
			      (domain-term-list (fringe dom))
                              (subsetp-equal (fringe dom)
                                             (fringe (domain i)))
			      (domain-term-list (fringe d2))
			      (subsetp-equal (fringe d2)
                                             (fringe (domain i))))))
  (cond ((atom vars)   (xeval f dom i))
	((equal n 1)
	 (if (atom d2) (keval (cdr vars)
			      (subst-free f (car vars) d2)
			      dom
			      (- n 1)
			      (domain i)
			      i)
	   (and (keval vars f dom n (car d2) i)
		(keval vars f dom n (cdr d2) i))))
	(t
	 (if (atom dom) (keval (cdr vars)
			       (subst-free f (car vars) dom)
			       (domain i)
			       (- n 1)
			       d2
			       i)
	   (and (keval vars f (car dom) n d2 i)
		(keval vars f (cdr dom) n d2 i))))))


;;------------------ The relationship of keval to xeval.

;; If n <= 0, d2 is ignored.

(defthm keval-xeval-lt-1
  (implies (and (var-list v)
		(setp v)
		(<= n 0))
	   (equal (keval v f dom n d2 i)
		  (xeval (alls v f) dom i)))
  :hints (("Goal"
	   :induct (keval v f dom n d2 i)
	   :expand ((alls v f))
	   )))

(defthm keval-xeval-i-1
  (implies (and (domain-term-list (fringe dom))
		(var-list v)
		(setp v)
		(consp v))
	   (equal (keval v f (domain i) 1 dom i)
		  (xeval (alls v f) dom i)))
  :hints (("Goal"
	   :induct (var-induct v f dom i)
	   :expand ((alls v f))
	   ))
  :rule-classes nil)

(defthm keval-xeval-i-1a
  (implies (and (var-list v)
		(setp v))
	   (equal (keval v f (domain i) 1 (domain i) i)
		  (xeval (alls v f) (domain i) i)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance keval-xeval-i-1 (dom (domain i)))))))

(defun var-induct-n (vars f dom n i)
  (declare (xargs :measure (cons (+ 1 (acl2-count vars)) (acl2-count dom))
                  :guard (and (var-list vars) (wff f) (integerp n)
                              (domain-term-list (fringe dom)))))
  (if (atom vars)
      nil
      (if (atom dom)
          (var-induct-n (cdr vars) (subst-free f (car vars) dom)
			(domain i) (- n 1) i)
          (cons (var-induct-n vars f (car dom) n i)
                (var-induct-n vars f (cdr dom) n i)))))

(defthm keval-xeval-i-x1
  (implies (and (domain-term-list (fringe dom))
		(var-list v)
		(setp v)
		(not (equal n 1)))
	   (equal (keval v f dom n (domain i) i)
		  (xeval (alls v f) dom i)))
  :hints (("Goal"
	   :induct (var-induct-n v f dom n i)
	   :expand ((alls v f))
	   ))
  :rule-classes nil)

(defthm keval-xeval-i
  (implies (and (var-list v)
		(setp v))
	   (equal (keval v f (domain i) n (domain i) i)
		  (xeval (alls v f) (domain i) i)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance keval-xeval-i-1a)
		 (:instance keval-xeval-i-x1 (dom (domain i))))
	   :in-theory (disable keval-xeval-i-1a))))

;; Function (idx x a) is used for the index argument of keval.
;; It gives the index of the first occurrence of x in a, counting
;; from 1 (or 0 if x is not in a).

(defun idx (x a)
  (declare (xargs :guard (true-listp a)))
  (cond ((atom a) 0)
	((equal (car a) x) 1)
	((equal (idx x (cdr a)) 0) 0)
	(t (+ 1 (idx x (cdr a))))))

(defthm idx-not-zero
  (implies (member-equal x a)
	   (not (equal (idx x a) 0))))

;;---------------
;; An induction scheme for keval.

(defun keval-i (vars f dom n d2 i)
  (declare (xargs :measure (cons (cons (+ 1 (acl2-count vars))
				       (acl2-count dom))
				 (acl2-count d2))
		  :guard (and (var-list vars)
			      (setp vars)
			      (wff f)
			      (not (free-vars (alls vars f)))
			      (integerp n)
			      (domain-term-list (fringe dom))
                              (subsetp-equal (fringe dom)
                                             (fringe (domain i)))
			      (domain-term-list (fringe d2))
			      (subsetp-equal (fringe d2)
                                             (fringe (domain i))))))
  (cond ((atom vars) 'junk)
	((equal n 1)
	 (if (atom d2) (keval-i (cdr vars)
			      (subst-free f (car vars) d2)
			      dom
			      (- n 1)
			      (domain i)
			      i)
	   (cons (keval-i vars f dom n (car d2) i)
		 (keval-i vars f dom n (cdr d2) i))))
	(t
	 (if (atom dom) (keval-i (cdr vars)
			       (subst-free f (car vars) dom)
			       (domain i)
			       (- n 1)
			       d2
			       i)
	   (cons (keval-i vars f (car dom) n d2 i)
		 (keval-i vars f (cdr dom) n d2 i))))))
