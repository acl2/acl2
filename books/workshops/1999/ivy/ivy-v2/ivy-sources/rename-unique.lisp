(in-package "ACL2")

;; This book contains the syntactic correctness theorem for
;; (rename-all f):   (setp (quantified-vars (rename-all f))).

(include-book "rename")

;; I think this book could use some cleaning up.  All we need is
;; the last theorem, and I think it can be proved with a lot less work.

;------------------------------------------------

(defthm rename-bound-introduces-new-variable
  (implies (and (bound-occurrence x f)
		(variable-term y))
	   (member-equal y (quantified-vars (rename-bound f x y)))))

(defthm rename-bound-introduces-new-variable-2
  (implies (and (member-equal x (quantified-vars f))
		(variable-term y))
	   (member-equal y (quantified-vars (rename-bound f x y))))
  :hints (("Goal"
	   :use ((:instance quantified-is-bound)))))

(defthm rename-bound-doesnt-change-other-variables
  (implies (and (member-equal v (quantified-vars f))
		(variable-term y)
		(not (equal v x)))
	   (member-equal v (quantified-vars (rename-bound f x y)))))

(defthm rename-bunch-introduces-new-variables
  (implies (and (member-equal x (quantified-vars g))
		(var-list new)
		(not (member-equal x old)))
	   (member-equal x (quantified-vars (rename-bunch g old new))))
  :hints (("Goal"
	   :do-not generalize)))

(defthm bound-is-quantified  ;; disabled below
  (implies (bound-occurrence x f)
	   (member-equal x (quantified-vars f)))
  :hints (("Goal"
           :use ((:instance quantified-iff-bound)))))

(defthm not-bound-is-not-quantified  ;; disabled below
  (implies (not (bound-occurrence x f))
	   (not (member-equal x (quantified-vars f))))
  :hints (("Goal"
           :use ((:instance quantified-iff-bound)))))

;;----------------------------
;; Bring in subbag, because there can be duplicates in the list of
;; original quantified variables.  Also, we will use permutation.

(include-book "permutations")

(defthm subbag-member-remove1-equal-append-lemma
  (implies (and (not (member-equal x f3))
		(subbag (remove1-equal x f5) q))
	   (subbag (remove1-equal x (append f3 f5)) (append f3 q))))

(defthm subbag-remove1-equal-qvars-lemma-1
  (implies (variable-term y)
	   (subbag (remove1-equal x (quantified-vars f))
		   (quantified-vars (rename-bound f x y)))))

(in-theory (disable bound-is-quantified not-bound-is-not-quantified))

(defthm subbag-remove1-equal-qvars-lemma-2
  (implies (and (subbag vars (remove1-equal x (quantified-vars f)))
		(variable-term y))
	   (subbag vars (quantified-vars (rename-bound f x y))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance subbag-trans
			    (a vars)
			    (b (remove1-equal x (quantified-vars f)))
			    (c (quantified-vars (rename-bound f x y))))))))

(defthm disjoint-cons
  (implies (not (disjoint a b))
           (not (disjoint a (cons x b)))))

(defthm new-vars-really-get-there-lemma
  (implies (and (subbag old (quantified-vars f))
		(equal (len old) (len new))
		(disjoint new old)
		(var-list new))
	   (subsetp-equal new (quantified-vars (rename-bunch f old new))))
  :hints (("Goal"
	   :induct (rename-bunch f old new)
	   :expand ((subbag (cons old1 old2) (quantified-vars f)))
	   )))

(defthm all-safe-vars-are-disjoint-from-quantified-vars
  (implies (all-safe vars f)
	   (disjoint vars (quantified-vars f))))

(defthm safe-list-vars-are-disjoint-from-quantified-vars
  (disjoint (safe-list f)
	    (quantified-vars f))
  :hints (("Goal"
           :in-theory (disable safe-list))))

(defthm len-qvars-equal-len-safe-vars
  (equal (len (safe-list f))
	 (len (quantified-vars f))))

(defthm new-vars-really-get-there
  (subsetp-equal (safe-list f)
		 (quantified-vars (rename-all f)))
  :hints (("Goal"
	   :in-theory (disable safe-list))))

; Now, use the fact that the new variables are a setp with the
; same length as the set of variables after the renaming to
; show that the permutation relation holds.  (Actually, it should
; be equal, but I couldn't see how to prove that.)

(defthm setp-subset-equal-length-perm
  (implies (and (setp new)
		(subsetp-equal new q)
		(equal (len new) (len q)))
	   (perm new q))
  :hints (("Goal"
	   :induct (perm new q)))
  :rule-classes nil)

;-----------------------
; When I wrote len-append-left and len-append right positively,
; I got a segmentation fault, I guess because of a rewrite loop.

(defthm len-append-left  ;; disabled below
  (implies (not (equal (len (append b a)) (len (append b c))))
           (not (equal (len a) (len c)))))

(defun double-list-induct (a b)
  (declare (xargs :guard t))
  (if (or (atom a) (atom b))
      nil
      (double-list-induct (cdr a) (cdr b))))

(defthm len-append-right  ;; disabled below
  (implies (not (equal (len (append a b)) (len (append c b))))
           (not (equal (len a) (len c))))
  :hints (("Goal"
           :induct (double-list-induct a c))))

(defthm rename-bound-preserves-len-of-qvars
  (implies (variable-term y)
	   (equal (len (quantified-vars (rename-bound f x y)))
		  (len (quantified-vars f)))))

(in-theory (disable len-append-left len-append-right))

(defthm rename-bunch-preserves-len-of-qvars
  (implies (var-list new)
	   (equal (len (quantified-vars (rename-bunch f old new)))
		  (len (quantified-vars f)))))

;-----------------------

(defthm safe-list-is-perm-of-qvars-rename-all
  (perm (safe-list f)
	(quantified-vars (rename-all f)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance setp-subset-equal-length-perm
			    (new (safe-list f))
			    (q (quantified-vars (rename-all f))))))))

;; The main event.

(defthm rename-all-setp-qvars
  (setp (quantified-vars (rename-all f)))
  :hints (("Goal"
           :in-theory (disable rename-all safe-list perm-implies-iff-setp-1)
	   :use ((:instance perm-setp-setp
			    (a (safe-list f))
			    (b (quantified-vars (rename-all f))))))))

