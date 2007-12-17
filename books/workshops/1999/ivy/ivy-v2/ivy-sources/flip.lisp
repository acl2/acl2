(in-package "ACL2")

;; This book is for the proof rule "flip" which swaps the
;; arguments of an equality (positive or negative).  For
;; negated equalities, the position can point to either
;; the 'not node or to the equality.

(include-book "paramod")

(defun flip-eq (f pos)
  (declare (xargs :guard (and (wff f) (integer-listp pos))))
  (cond ((atom pos) (cond ((wfeq f) (list (car f) (a2 f) (a1 f)))
			  ;; also allow pos to point at negated equality
			  ((and (wfnot f)
				(wfeq (a1 f)))
			   (list 'not (list (car (a1 f))
					    (a2 (a1 f))
					    (a1 (a1 f)))))
			  (t f)))

	((wfnot f) (if (equal (car pos) 1)
		       (list 'not (flip-eq (a1 f) (cdr pos)))
		       f))

	((wfbinary f) (cond ((equal (car pos) 1)
			     (list (car f)
				   (flip-eq (a1 f) (cdr pos))
				   (a2 f)))
			    ((equal (car pos) 2)
			     (list (car f)
				   (a1 f)
				   (flip-eq (a2 f) (cdr pos))))
			    (t f)))

	(t f)))

(defthm flip-eq-xsound
  (equal (xeval (flip-eq f pos) dom i)
	 (xeval f dom i))
  :hints (("Goal"
	   :in-theory (enable eval-atomic)
	   :induct (flip-eq f pos))))

(defthm flip-eq-subst-commute
  (equal (subst-free (flip-eq f pos) x tm)
	 (flip-eq (subst-free f x tm) pos)))

(defthm flipeq-xsound-alls
  (implies (var-set vars)
	   (equal (xeval (alls vars (flip-eq f pos)) dom i)
		  (xeval (alls vars f) dom i)))
  :hints (("Goal"
	   :expand ((alls vars f))
	   :induct (var-induct vars f dom i))))


;;-----------------------------
;; Now, get it in terms of universal-closure.

(encapsulate
 nil
 (local (include-book "close"))
 (defthm xeval-alls-subset
   (implies (and (var-set a)
		 (var-set b)
		 (subsetp-equal a b)
		 (not (free-vars (alls a f))))
	    (equal (xeval (alls a f) (domain i) i)
		   (xeval (alls b f) (domain i) i)))
   :rule-classes nil)
 )

(defthm flip-eq-subset-vars
  (subsetp-equal (free-vars (flip-eq f pos)) (free-vars f)))

(defthm flip-eq-xsound-closure
  (equal (xeval (universal-closure (flip-eq f pos)) (domain i) i)
	 (xeval (universal-closure f) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance xeval-alls-subset
			    (f (flip-eq f pos))
			    (a (free-vars (flip-eq f pos)))
			    (b (free-vars f)))
		 ))))
