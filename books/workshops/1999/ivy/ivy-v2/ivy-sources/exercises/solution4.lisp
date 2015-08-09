;; Exercise file to accompany
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Solution for exercise 4.
;;
;; The current proof checker for resolution steps generates all
;; resolvents of the parent clauses and checks whether the clause from the
;; proof object follows from the conjunction of all the resolvents.
;; Define a proof-checking procedure that computes the specified
;; resolvent directly.  Prove that the procedure is sound.

(in-package "ACL2")

;; All neccesary definitions are in:
(include-book "../stage")
(local (include-book "../../../../../../ordinals/e0-ordinal"))

;; Hint: the following lemma might be useful:
(encapsulate
 nil
 (local (include-book "../close"))
 (defthm feval-alls-subset
   (implies (and (var-set a)
                 (var-set b)
                 (subsetp-equal a b)
                 (not (free-vars (alls a f))))
            (equal (feval (alls a f) i)
                   (feval (alls b f) i)))
   :rule-classes nil)
 )

;; -------------- Resolution
;; This is resolution on identical atoms; that is, no unification is
;; involved.  The function (resolve f1 l1 f2 l2) computes the resolvent of
;; f1 and f2 on literals specified in position lists l1 and l2.  If the
;; specified literals (computed by literal-at-position) do not resolve,
;; 'true is returned.
;;
;; We took a shortcut: the resolvent contains 'false literals
;; corresponding to the resolved literals, and the resolvent is not right
;; associated.  If you need nicer resolvents, you can apply functions
;; right-assoc and simplify (defined elsewhere).

(defun exists-literal-at-position (f l)
  (declare (xargs :guard (and (wff f) (integer-listp l))))
  (cond ((atom l) t)
	((wfor f) (cond ((equal (car l) 1)
			 (exists-literal-at-position (a1 f) (cdr l)))
			((equal (car l) 2)
			 (exists-literal-at-position (a2 f) (cdr l)))
			(t nil)))
	(t nil)))

(defun literal-at-position (f l)
  (declare (xargs :guard (and (wff f) (integer-listp l))))
  (cond ((atom l) f)
	((wfor f) (cond ((equal (car l) 1)
			 (literal-at-position (a1 f) (cdr l)))
			((equal (car l) 2)
			 (literal-at-position (a2 f) (cdr l)))
			(t nil)))
	(t nil)))

(defmacro complements (p q)
  (list 'or
	(list 'equal p (list 'list ''not q))
        (list 'equal (list 'list ''not p) q)))

(defun remove-literal (f l)
  (declare (xargs :guard (and (wff f) (integer-listp l))))
  (cond ((atom l) 'false)
	((wfor f) (cond ((equal (car l) 1)
			 (list 'or (remove-literal (a1 f) (cdr l)) (a2 f)))
			((equal (car l) 2)
			 (list 'or (a1 f) (remove-literal (a2 f) (cdr l))))
			(t f)))
	(t f)))

(defthm remove-literal-wff
  (implies (wff f)
           (wff (remove-literal f pos))))

(defun resolve (f1 l1 f2 l2)
  (declare (xargs :guard (and (wff f1) (integer-listp l1)
			      (wff f2) (integer-listp l2))))
  (if (and (exists-literal-at-position f1 l1)
	   (exists-literal-at-position f2 l2)
	   (complements (literal-at-position f1 l1)
			(literal-at-position f2 l2)))
      (list 'or (remove-literal f1 l1) (remove-literal f2 l2))
    'true))

(defthm resolve-wff
  (implies (and (wff par1)
                (wff par2))
           (wff (resolve par1 pos1 par2 pos2))))

;;----------------------------------------------------------------------------
;; Ground soundness of resolve
;;

(defthm remove-false-unit-gsound
  (implies (and (exists-literal-at-position f pos)
		(not (feval (literal-at-position f pos) i)))
	   (equal (feval (remove-literal f pos) i)
		  (feval f i))))

(defthm resolve-ground-fsound-helper
  (implies (and (feval f i)
		(feval g i)
		(exists-literal-at-position f pos1)
		(exists-literal-at-position g pos2)
		(complements (literal-at-position f pos1)
			     (literal-at-position g pos2))
		(not (feval (remove-literal f pos1) i)))
	   (feval (remove-literal g pos2) i))
  :hints (("goal" :induct (remove-literal f pos1))))

(defthm resolve-ground-fsound
  (implies (and (feval f i)
		(feval g i))
	   (feval (resolve f pos1 g pos2) i)))

(in-theory (disable resolve-ground-fsound-helper))

(in-theory (disable resolve))

;;----------------------------------------------------------------------------
;; Soundness of resolve under universal closure

(defthm remove-literal-subst-free-commute
  (equal (remove-literal (subst-free f x tm) l)
	 (subst-free (remove-literal f l) x tm)))

(defthm literal-at-position-subst-free-commute
  (equal (literal-at-position (subst-free f x tm) l)
	 (subst-free (literal-at-position f l) x tm)))

(defthm exists-literal-at-position-subst
  (implies (exists-literal-at-position f pos)
	   (exists-literal-at-position (subst-free f x tm) pos)))

;; Induction scheme for resolve-fsound-alls-aux

(defun alls-i-2 (vars flg f g dom i)
  (declare (xargs :guard (and (implies (not flg)
                                       (domain-term-list (fringe dom)))
                              (var-list vars)
                              (wff f)
			      (wff g))
                  :measure (cons (cons (+ 1 (acl2-count vars))
                                       (if flg 2 1))
				 (acl2-count dom))))
  (if flg
      (if (atom vars)
	  nil
	  (alls-i-2 vars nil f g (domain i) i))
      (if (atom vars)
          nil
	  (if (atom dom)
              (alls-i-2 (cdr vars) t
		      (subst-free f (car vars) dom)
		      (subst-free g (car vars) dom)
		      'junk i)
              (cons (alls-i-2 vars nil f g (car dom) i)
                    (alls-i-2 vars nil f g (cdr dom) i))))))


;; Note: condition (**) below is added in the flg==nil case to avoid the
;; inductive case
;;
;; (implies (and (feval-d f dom i)
;;               (feval-d g dom i))
;;          (feval-d (resolve f posf g posg) dom i))
;;
;; which does not hold.  We only use the feval part of this lemma.

(defthm resolve-fsound-alls-aux
  (implies (var-set vars)
	   (if flg
	       (implies (and (feval (alls vars f) i)
			     (feval (alls vars g) i))
			(feval (alls vars (resolve f posf g posg)) i))
	       (implies (and (domain-term-list (fringe dom))
                             (consp vars) ;; (**)
			     (feval-d (alls vars f) dom i)
			     (feval-d (alls vars g) dom i))
			(feval-d (alls vars (resolve f posf g posg)) dom i))))
  :hints (("Goal"
	   :induct (alls-i-2 vars flg f g dom i))
          ("Subgoal *1/3"
	   :in-theory (enable resolve))
          ("Subgoal *1/2"
	   :in-theory (enable resolve)
	   :expand (alls vars (list 'or
				    (remove-literal f posf)
				    (remove-literal g posg)))))
  :rule-classes nil)

(defthm resolve-fsound-alls
  (implies (and (var-set vars)
 		(feval (alls vars f) i)
		(feval (alls vars g) i))
	   (feval (alls vars (resolve f posf g posg)) i))
  :hints (("Goal" :by (:instance resolve-fsound-alls-aux (flg t)))))

;;-----------------------------------------
;; Main theorem

(defthm resolve-fsound-closure
  (implies (and (feval (universal-closure f) i)
                (feval (universal-closure g) i))
           (feval (universal-closure (resolve f l1 g l2)) i))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance
		  feval-alls-subset
		  (f f)
		  (a (free-vars f))
		  (b (union-equal
		      (free-vars f)
		      (union-equal (free-vars g)
				   (free-vars (resolve f l1 g l2))))))
                 (:instance
		  feval-alls-subset
		  (f g)
		  (a (free-vars g))
		  (b (union-equal
		      (free-vars f)
		      (union-equal (free-vars g)
				   (free-vars (resolve f l1 g l2))))))
                 (:instance
		  feval-alls-subset
		  (f (resolve f l1 g l2))
		  (a (free-vars (resolve f l1 g l2)))
		  (b (union-equal
		      (free-vars f)
		      (union-equal (free-vars g)
				   (free-vars (resolve f l1 g l2))))))
                 ))))


