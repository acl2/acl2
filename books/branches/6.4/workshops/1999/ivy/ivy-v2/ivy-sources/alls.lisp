(in-package "ACL2")

;; This book is mostly about universal closures.  The theorem
;; prover operates on clauses (which contain free variables and
;; no quantifiers, and free variables are understood as being
;; universally quantified), and when proving soundness of various
;; things, we have to frequently add and remove universal quantifiers
;; to the top of a formula.
;;
;; Some of this applies to existential quantifiers as well.

(include-book "variables")
(include-book "../../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;;------------------------------------------
;; Function alls (vars f) tacks on a list of variables as universally
;; quantified variables.

(defun alls (vars f)
  (declare (xargs :guard (and (var-list vars) (wff f))))
  (if (atom vars)
      f
      (list 'all (car vars) (alls (cdr vars) f))))

(defthm alls-vars-f-wff
  (implies (and (var-list vars)
		(wff f))
	   (wff (alls vars f))))

(defthm subst-alls-commute
  (implies (and (not (member-equal x vars))
		(var-list vars))
	   (equal (subst-free (alls vars f) x e)
		  (alls vars (subst-free f x e)))))

(defthm remove-vars-alls
  (implies (and (domain-term e)
                (var-list a)
                (not (member-equal x a))
                (not (remove-equal x (free-vars (alls a f)))))
           (not (free-vars (alls a (subst-free f x e)))))
  :hints (("Goal"
           :use ((:instance vars-alls-free (f (alls a f)))))))

(defthm alls-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (alls v f))))
  :hints (("Goal"
	   :do-not generalize)))

(defthm alls-all
  (implies (and (consp vars)
		(var-list vars))
	   (wfall (alls vars f))))

(defthm alls-quant
  (implies (and (consp vars)
		(var-list vars))
	   (wfquant (alls vars f))))

(defun remove-leading-alls (f)
  (declare (xargs :guard (wff f)))
  (if (wfall f)
      (remove-leading-alls (a2 f))
      f))

(defthm remove-leading-alls-preserves-wff
  (implies (wff f)
	   (wff (remove-leading-alls f))))

(defun leading-alls (f)
  (declare (xargs :guard (wff f)))
  (if (wfall f)
      (cons (a1 f) (leading-alls (a2 f)))
      nil))

(defthm lead-alls-var-list
  (var-list (leading-alls f)))

(defthm alls-lead-remove-f-is-f
  (equal (alls (leading-alls f) (remove-leading-alls f)) f))

(defun remove-leading-quants (f)
  (declare (xargs :guard (wff f)))
  (if (wfquant f)
      (remove-leading-quants (a2 f))
      f))

(defun leading-quants (f)
  (declare (xargs :guard (wff f)))
  (if (wfquant f)
      (cons (a1 f) (leading-quants (a2 f)))
      nil))

;;--------------------

(defthm leading-all-is-quantified-var
  (implies (not (member-equal x (quantified-vars f)))
	   (not (member-equal x (leading-alls f)))))

(defthm setp-qvars-leading-alls
  (implies (setp (quantified-vars f))
	   (setp (leading-alls f))))

(defthm varset-qvars-leading-alls
  (implies (var-set (quantified-vars f))
	   (var-set (leading-alls f))))

;;------------
;; Prove that the universal closure of a formula is closed.
;; First prove thw two key properties, then do a resolution
;; step to get the result in terms of member-equal, then
;; get it in the desired form.

(defthm alls-eliminates-free-vars
  (implies (member-equal x vars)
	   (not (member-equal x (free-vars (alls vars f))))))

(defthm alls-doesnt-introduce-free-vars
  (implies (not (member-equal x (free-vars f)))
	   (not (member-equal x (free-vars (alls vars f))))))

(defthm universal-closure-is-closed-almost-in-final-form
  (not (member-equal x (free-vars (alls (free-vars f) f))))
  :hints (("Goal"
	   :use ((:instance alls-eliminates-free-vars
			    (x x) (f f) (vars (free-vars f)))
		 (:instance alls-doesnt-introduce-free-vars
			    (x x) (f f) (vars (free-vars f))))
	   )))

(defmacro universal-closure (f)
  (list 'alls (list 'free-vars f) f))

(defthm universal-closure-is-closed
  (not (free-vars (universal-closure f)))
  :hints (("Goal"
	   :use ((:instance consp-has-member-equal
			    (x (free-vars (alls (free-vars f) f))))))))

;;-------------------------------------
;; Eval inductions on variables.  These functions give useful induction
;; schemes for proving soundness theorems about universal closures,
;; in particular about formulas (alls vars f), with evaluation function xeval.
;; Think of the two arguments "vars f" as "(alls vars f)".

(defun var-induct (vars f dom i)
  (declare (xargs :measure (cons (+ 1 (acl2-count vars)) (acl2-count dom))
                  :guard (and (var-list vars) (wff f)
                              (domain-term-list (fringe dom)))))
  (if (atom vars)
      nil
      (if (atom dom)
          (var-induct (cdr vars) (subst-free f (car vars) dom) (domain i) i)
          (cons (var-induct vars f (car dom) i)
                (var-induct vars f (cdr dom) i)))))

;; This induction scheme goes through two formulas together.

(defun var-induct-2 (vars f g dom i)
  (declare (xargs :measure (cons (+ 1 (acl2-count vars)) (acl2-count dom))
                  :guard (and (var-list vars) (wff f) (wff g)
                              (domain-term-list (fringe dom)))))
  (if (atom vars)
      nil
      (if (atom dom)
          (var-induct-2 (cdr vars)
                        (subst-free f (car vars) dom)
                        (subst-free g (car vars) dom)
                        (domain i) i)
          (cons (var-induct-2 vars f g (car dom) i)
                (var-induct-2 vars f g (cdr dom) i)))))

;-------------------------

(defthm not-free-feval-same
  (implies (and (variable-term x)
                (not (member-equal x (free-vars f))))
           (equal (feval-d (list 'all x f) dom i)
                  (feval f i)))
  :hints (("Goal"
           :induct (dom-i dom))
	  ("Subgoal *1/1"
           :in-theory (enable not-free-not-change-2))))

(defthm feval-alls-true
  (implies (var-list vars)
	   (feval (alls vars 'true) i)))

(defthm feval-alls-false
  (implies (var-list vars)
	   (not (feval (alls vars 'false) i))))
