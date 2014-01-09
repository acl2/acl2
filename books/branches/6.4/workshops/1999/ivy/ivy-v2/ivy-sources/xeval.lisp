(in-package "ACL2")

;; This little book contains another evaluation function called xeval.
;; Xeval is similar to feval/feval-d, but it does not use explicit mutual
;; recursion.  Also, there is an important difference in the handling
;; of the domain argument.
;;
;; Feval gets a fresh copy of the domain when it STARTS to evaluate
;; a quantified formula, and xeval restores the domain with a fresh
;; copy AFTER evaluating a quantified formula.  This difference is
;; independent of the mutual-nonmutual difference, and I think xeval
;; would be more useful if it handled domains in the same way as feval.
;;
;; As things are, xeval is more convenient for many proofs, because
;; we don't have to prove a separate theorem for the "flg" case,
;; and the proofs are quicker.
;;
;; However, because of the weird way xeval handles domains, we have
;; to use feval in some cases.
;;
;; Historical Note.  The first evaluation function for this project
;; (geval) was essentially the same as xeval.  That's why xeval
;; is so widespread.
;;
;; Feval and xeval are proved equal below.

(include-book "base")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(defun xeval (f dom i)
  (declare (xargs :measure (cons (wff-count f) (acl2-count dom))
		  :guard (and (wff f)
			      (domain-term-list (fringe dom))
			      ;; (not (free-vars f))
			      (subsetp-equal (fringe dom)
					     (fringe (domain i))))))
  (cond ((equal f 'true) t)
	((equal f 'false) nil)
	((wfnot f) (not (xeval (a1 f) dom i)))
	((wfand f) (and (xeval (a1 f) dom i)
			(xeval (a2 f) dom i)))
	((wfor  f) (or  (xeval (a1 f) dom i)
			(xeval (a2 f) dom i)))
	((wfimp f) (implies (xeval (a1 f) dom i)
			    (xeval (a2 f) dom i)))
	((wfiff f) (iff (xeval (a1 f) dom i)
			(xeval (a2 f) dom i)))
	((wfquant f)
	 (cond ((atom dom) (xeval (subst-free (a2 f) (a1 f) dom) (domain i) i))
	       ((wfall f)    (and (xeval f (car dom) i)
				  (xeval f (cdr dom) i)))
	       ((wfexists f) (or  (xeval f (car dom) i)
				  (xeval f (cdr dom) i)))
	       (t nil)))
	(t (eval-atomic f i))))

;; Show that (xeval f (domain i) i) is equal to (feval f dom i)

(defthm xeval-feval-flg
  (if flg
      (equal (feval f i)
	     (xeval f (domain i) i))
    (implies (wfquant f)
	     (equal (feval-d f dom i)
		    (xeval f dom i))))
  :hints (("Goal"
           :do-not generalize
           :induct (feval-i flg f dom i)))
  :rule-classes nil)

(defthm xeval-feval
  (equal (feval f i)
	 (xeval f (domain i) i))
  :hints (("Goal"
	   :by (:instance xeval-feval-flg (flg t)))))

(defthm xeval-feval-d
  (implies (wfquant f)
	   (equal (feval-d f dom i)
		  (xeval f dom i)))
  :hints (("Goal"
	   :by (:instance xeval-feval-flg (flg nil)))))

(in-theory (disable xeval-feval xeval-feval-d))

;; This is the induction scheme to use with xeval.

(defun xeval-i (f dom i)
  (declare (xargs :measure (cons (wff-count f) (acl2-count dom))
		  :guard (and (wff f)
			      (domain-term-list (fringe dom)))))
  (cond ((equal f 'true)   'junk)
	((equal f 'false)  'junk)
	((wfnot f) (xeval-i (a1 f) dom i))

	((wfbinary f) (cons (xeval-i (a1 f) dom i)
			    (xeval-i (a2 f) dom i)))
	((wfquant f) (if (atom dom)
			 (xeval-i (subst-free (a2 f) (a1 f) dom) (domain i) i)
		       (cons (xeval-i f (car dom) i)
			     (xeval-i f (cdr dom) i))))
	(t 'junk)))
