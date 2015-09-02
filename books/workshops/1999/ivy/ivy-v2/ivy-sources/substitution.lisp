(in-package "ACL2")

;; Here we define well-formed substitution, then we use
;; the theorem that one "subst-free" is sound
;; (instance-gsound-for-1-substitution) to show that sequentially
;; applying a well-formed substitution is sound.
;;
;; The main theorem in this book is instance-gsound-for-subst:
;;
;; If (1) f is quantifier-free,
;;    (2) (universal-closure f) is true, and
;;    (3) s is a well-formed substitution,
;; then
;;    (universal-closure (sequential-apply s f) is true.
;;
;; Note that this is sequential substitution.

(include-book "instance-closure")

;; A well-formed substitution is a list of (variable . term) pairs.

(defun wfsubst (s)
  (declare (xargs :guard t))
  (if (atom s)
      (equal s nil)
      (and (consp (car s))
	   (variable-term (caar s))
	   (wft (cdar s))
	   (wfsubst (cdr s)))))

(defthm wft-list-strip-cdrs-wfsubst
  (implies (wfsubst s)
	   (wft-list (strip-cdrs s))))

(defthm var-list-strip-cars-wfsubst
  (implies (wfsubst s)
	   (var-list (strip-cars s))))

(defthm cars-of-wfsubst-is-var-list
  (implies (wfsubst s)
	   (var-list (cars s))))

(defthm wfsubst-append
  (implies (and (wfsubst s1)
		(wfsubst s2))
	   (wfsubst (append s1 s2))))

;; To apply a wfsubst to a formula, subst-free is called with each member.
;; Note that this is not simultaneous substitution (the more standard method),
;; which could be done by visiting each subterm and using assoc.

(defun sequential-apply (s f)
  (declare (xargs :guard (and (wfsubst s)
                              (wff f))))
  (if (atom s)
      f
      (sequential-apply (cdr s) (subst-free f (caar s) (cdar s)))))

;;------------------ The main event

(defthm instance-gsound-for-subst
  (implies (and (quantifier-free f)
		(xeval (universal-closure f) (domain i) i)
		(wfsubst s))
           (xeval (universal-closure (sequential-apply s f)) (domain i) i))
  :hints (("Goal"
	   :induct (sequential-apply s f)
	   )
	  ("Subgoal *1/2''"
	   :use ((:instance instance-xsound-for-1-substitution
			    (x (caar s))
			    (tm (cdar s)))))
	  )
  :rule-classes nil)

;;-----------------------
;; Sequential-apply, defined above, is nonstandard.  We use it
;; because it fits with our soundness proof for instantiation
;; (thm instance-xsound-for-1-substitution).
;;
;; Simultaneous substitution is the standard method, and since Otter
;; proof objects assume simultaneous substitution, they won't work
;; with sequential-apply.
;;
;; Function seqify below transforms a substitution intended
;; for simultaneous substitution into one that works for
;; sequential substitution.
;;
;; If we had a function simultaneous-apply, then something like
;;
;;    (simultaneous-apply f s) = (sequential-apply f (seqify s vars))
;;
;; should hold.
;;
;; From a soundness point of view, it is not necessary to prove
;; anything about seqify; it's intended use is to transform Otter
;; proof objects, and if it screws up a substitution, then check-proof
;; will fail.
;;
;; But it would be nice to prove some things about it.

(include-book "gensym-e")

(defun intersect-equal (a b)  ;; move to sets?
  (declare (xargs :guard (and (true-listp a)
			      (true-listp b))))
  (cond ((atom a) nil)
	((member-equal (car a) b) (cons (car a) (intersect-equal (cdr a) b)))
	(t (intersect-equal (cdr a) b))))

(defthm var-list-intersect-equal  ;; move to variables?
  (implies (and (var-list a)
		(var-list b))
	   (var-list (intersect-equal a b))))

;; Apply subst-term to the cdrs of a wfsubst.

(defun subst-cdrs (s x tm)
  (declare (xargs :guard (and (wfsubst s)
			      (variable-term x)
			      (wft tm))))
  (if (atom s)
      s
      (cons (cons (caar s) (subst-term (cdar s) x tm))
	    (subst-cdrs (cdr s) x tm))))

(defthm wfsubst-subst-cdrs
  (implies (and (wft tm)
		(wfsubst s))
	   (wfsubst (subst-cdrs s x tm))))

(defun seqify-helper (s vars-to-fix all-vars)
  (declare (xargs :guard (and (wfsubst s)
			      (var-list vars-to-fix)
			      (var-list all-vars))
		  :verify-guards nil))
  (if (atom vars-to-fix)
      s
     (let ((newvar (gen-symbol 'y all-vars)))
       (append (seqify-helper (subst-cdrs s (car vars-to-fix) newvar)
			      (cdr vars-to-fix)
			      (cons newvar all-vars))
	       (list (cons newvar (car vars-to-fix)))))))

(defthm true-listp-append-2
  (implies (true-listp a)
	   (true-listp (append b a))))

(defthm var-list-is-symbol-listp
  (implies (var-list vars)
	   (symbol-listp vars)))

(defthm seqify-helper-true-listp
  (implies (true-listp s)
	   (true-listp (seqify-helper s x y))))

(verify-guards seqify-helper :otf-flg t)

;; Function seqify transforms a substitution meant for simultaneous
;; application into one that works with sequential application.
;; Parameter other-vars contains all variables in terms to which
;; the substitution will be applied.  (Other-vars helps us to safely
;; generate new variables.)

(defun seqify (s other-vars)
  (declare (xargs :guard (and (wfsubst s)
			      (var-list other-vars))))
  (seqify-helper s
		 (intersect-equal (cars s) (vars-in-term-list (cdrs s)))
		 (union-equal (union-equal (cars s)
					   (vars-in-term-list (cdrs s)))
			      other-vars)))

(defthm wfsubst-seqify-helper
  (implies (and (wfsubst s)
		(var-list a))
	   (wfsubst (seqify-helper s a b))))

