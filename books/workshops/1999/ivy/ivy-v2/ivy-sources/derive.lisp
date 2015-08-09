(in-package "ACL2")

;; This book has the interface to the program (say external-prover) that
;; searches for a refutation of a list of clauses.
;;
;; External-prover receives a list of annotated clauses (the initial proof)
;; and returns a list of annotated clauses (the proof object).
;; The annotations are clause identifiers and justifications.
;; Function check-proof below checks the soundness of each
;; clause in the proof object.  (If we are lucky, one of the clauses
;; in the proof object is 'false.)
;;
;; Function refute-n-check below is at the center of things.  It takes
;; a closed wff in universal-prefix-cnf, strips the universal
;; quantifiers, constructs an initial proof object, calls Otter,
;; checks Otter's answer, then converts Otter's proof object
;; into a wff.  Theorem refute-n-check-sound below shows that refute-n-check
;; returns a formula equivalent to its input.

(include-book "uc-conj")
(include-book "prop-subsume")
(include-book "substitution")
(include-book "resolve")
(include-book "paramod")
(include-book "flip")

;;----------------------
;; Well-formed proof.

(defmacro just (s) ;; Extract the justification from a proof step.
  (list 'cadr s))  ;; second member

(defmacro prf-clause (s)  ;; Extract the clause from a proof step.
  (list 'caddr s))  ;; third member

(defmacro prf-rule (s)  ;; Extract the inference rule name from a proof step.
  (list 'car (list 'just s)))

(defmacro parent-1-id (s)  ;; ID of 1st parent of unary or binary step.
  (list 'cadr (list 'just s)))

(defmacro position-1 (s)   ;; 1st position of a unary or binary step.
  (list 'caddr (list 'just s)))

(defmacro parent-2-id (s)  ;; Get the ID of the 2nd parent from a binary step.
  (list 'cadddr (list 'just s)))

(defmacro position-2 (s)   ;; Get the 2nd position from a binary step.
  (list 'car (list 'cddddr (list 'just s))))

(defmacro prf-subst (s)  ;; Get the substitution from an 'instantiate step.
  (list 'caddr (list 'just s)))

;; Well-formed justification.

(defun wfjust (j)
  (declare (xargs :guard t))
  (cond ((atom j) nil)
	((equal (car j) 'input)         (equal (len j) 1))
	((equal (car j) 'resolve)       (equal (len j) 5))
	((equal (car j) 'paramod)       (equal (len j) 5))
	((equal (car j) 'flip)          (equal (len j) 3))
	((equal (car j) 'propositional) (equal (len j) 2))
	((equal (car j) 'instantiate)   (and (equal (len j) 3)
					     (wfsubst (caddr j))))
	(t nil)))

;; Well-formed proof step.

(defun wfproof-step (s)
  (declare (xargs :guard t))
  (and (>= (len s) 3)
       (wff (prf-clause s))
       (quantifier-free (prf-clause s))
       (wfjust (just s))))

;; Well-formed proof.

(defun wfproof (prf)
  (declare (xargs :guard t))
  (and (alistp prf)
       (if (atom prf) t
	   (and (wfproof-step (car prf))
		(wfproof (cdr prf))))))

;;------------------------
;; Extract all steps from a wfproof, conjoin them, and return a wff.

(defun extract-all-steps (prf)
  (declare (xargs :guard (wfproof prf)))
  (if (atom prf)
      'true
      (list 'and
	    (prf-clause (car prf))
	    (extract-all-steps (cdr prf)))))

;; Extract the input steps from a wfproof, conjoin them, and return a wff.

(defun extract-input-steps (prf)
  (declare (xargs :guard (wfproof prf)))
  (cond ((atom prf) 'true)
	((equal (prf-rule (car prf)) 'input)
	 (list 'and
	       (prf-clause (car prf))
	       (extract-input-steps (cdr prf))))
	(t (extract-input-steps (cdr prf)))))

;; Extract a particular step from a wfproof (wff or nil returned).

(defun extract-step (id prf)
  (declare (xargs :guard (wfproof prf)))
  (if (assoc-equal id prf)
      (prf-clause (assoc-equal id prf))
      nil))

(defthm extract-all-wff
  (implies (wfproof prf)
	   (wff (extract-all-steps prf))))

(defthm extract-input-wff
  (implies (wfproof prf)
	   (wff (extract-input-steps prf))))

(defthm extract-step-wff
  (implies (and (wfproof prf)
		(extract-step id prf))
	   (wff (prf-clause (assoc-equal id prf)))))

(defthm quantifier-free-extract-step
  (implies (and (wfproof prf)
		(extract-step id prf))
	   (quantifier-free (prf-clause (assoc-equal id prf)))))

;;---------  check one step of a proof

;; Function check-resolve checks if the conjunction of all resolvents
;; propositionally subsumes the claimed resolvent.

(defun check-resolve (par1 pos1 par2 pos2 resolvent)
  (declare (xargs :guard (and (or (not par1) (wff par1))
			      (or (not par2) (wff par2))
			      (wff resolvent))))
  (and par1
       par2
       (integer-listp pos1)
       (integer-listp pos2)
       ;; We use prop-subsume instead of equal, in case the
       ;; clauses are associated differently.  Also, resolve
       ;; is allowed to leave some extraneous 'false literals.
       (prop-subsume (resolve par1 pos1 par2 pos2) resolvent)))

(defun check-paramod (par1 pos1 par2 pos2 paramodulant)
  (declare (xargs :guard (and (or (not par1) (wff par1))
			      (or (not par2) (wff par2))
			      (wff paramodulant))))
  (and par1
       par2
       (integer-listp pos1)
       (integer-listp pos2)
       ;; We use prop-subsume instead of equal, in case the
       ;; clauses are associated differently.
       (prop-subsume (paramod par1 pos1 par2 pos2) paramodulant)))

(defun check-propositional (parent child)
  (declare (xargs :guard (and (or (not parent) (wff parent))
			      (wff child))))
  (and parent
       (prop-subsume parent child)))

;; Function check-instantiate.

(defun check-instantiate (parent subst child)
  (declare (xargs :guard (and (or (not parent) (wff parent))
			      (wfsubst subst)
			      (wff child))))
  (and parent
       (equal (sequential-apply subst parent) child)))

;; Function check-flip.

(defun check-flip (parent pos child)
  (declare (xargs :guard (and (or (not parent) (wff parent))
			      (wff child))))
  (and parent
       (integer-listp pos)
       (equal (flip-eq parent pos) child)))

(defun check-step (checked s)
  (declare (xargs :guard (and (wfproof checked)
			      (wfproof-step s))))
  (and (wff (prf-clause s))
       (cond ((equal (prf-rule s) 'input) t)
	     ((equal (prf-rule s) 'resolve)
	      ;; Note that check-resolve does not use positions.
	      (check-resolve (extract-step (parent-1-id s) checked)
			     (position-1 s)
			     (extract-step (parent-2-id s) checked)
			     (position-2 s)
			     (prf-clause s)))
	     ((equal (prf-rule s) 'paramod)
	      (check-paramod (extract-step (parent-1-id s) checked)
			     (position-1 s)
			     (extract-step (parent-2-id s) checked)
			     (position-2 s)
			     (prf-clause s)))
	     ((equal (prf-rule s) 'flip)
	      (check-flip (extract-step (parent-1-id s) checked)
			  (position-1 s)
			  (prf-clause s)))
	     ((equal (prf-rule s) 'propositional)
	      (check-propositional (extract-step (parent-1-id s) checked)
			   (prf-clause s)))
	     ((equal (prf-rule s) 'instantiate)
	      (check-instantiate (extract-step (parent-1-id s) checked)
				 (prf-subst s)
				 (prf-clause s)))
	     (t nil))))

;; ---------- check all steps of a proof.

(defun check-proof (done todo)
  (declare (xargs :guard (and (wfproof done) (wfproof todo))
		  :measure (acl2-count todo)))
  (if (atom todo) t
      (and (check-step done (car todo))
	   (check-proof (cons (car todo) done) (cdr todo)))))

;;------------------------------------------
;; Now, prove that if check-proof succeeds, the proof is sound.

(defthm step-extract-xsound-closure
  (implies (and
	    (xeval (universal-closure (extract-all-steps prf)) (domain i) i)
	    (assoc-equal id prf))
	   (xeval (universal-closure (prf-clause (assoc-equal id prf)))
		  (domain i) i))
  :hints (("Goal"
	   :induct (assoc-equal id prf)
           :in-theory (disable xeval alls))
	  ("Subgoal *1/2''"
	   :expand ((extract-all-steps prf))
	   :use ((:instance uc-conj-left
			    (f (caddar prf))
			    (g (extract-all-steps (cdr prf))))))

	  ("Subgoal *1/3'"
	   :use ((:instance uc-conj-right
			    (f (caddar prf))
			    (g (extract-all-steps (cdr prf)))))))
  :rule-classes nil)

(defthm instantiate-step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(equal (prf-rule s) 'instantiate)
		(xeval (universal-closure (extract-all-steps prf))
		       (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance step-extract-xsound-closure (id (parent-1-id s)))))
	  ("Subgoal 4.1'" ; subgoal number changed by Matt K. for v2-9
                          ; (probably caused by call-stack change)
	   :use ((:instance instance-gsound-for-subst
			    (f (caddr (assoc-equal s7 prf)))
			    (s s9)))))
  :rule-classes nil)

(defthm propositional-step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(equal (prf-rule s) 'propositional)
		(xeval (universal-closure (extract-all-steps prf))
		       (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance step-extract-xsound-closure (id (parent-1-id s)))))
	  ("Subgoal 4'"  ;; I don't know why this is necessary.
	   :use ((:instance prop-subsume-xsound
			    (c (caddr (assoc-equal (cadadr s) prf)))
			    (d (caddr s)))))
	  )
  :rule-classes nil)

(defthm check-resolve-xsound
  (implies (and (check-resolve par1 pos1 par2 pos2 res)
		(xeval (universal-closure par1) (domain i) i)
		(xeval (universal-closure par2) (domain i) i))
	   (xeval (universal-closure res) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t))
  :rule-classes nil)

(defthm resolve-step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(equal (prf-rule s) 'resolve)
		(xeval (universal-closure (extract-all-steps prf))
			      (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance step-extract-xsound-closure (id (parent-1-id s)))
		 (:instance step-extract-xsound-closure (id (parent-2-id s)))
		 (:instance check-resolve-xsound
			    (par1 (extract-step (parent-1-id s) prf))
			    (par2 (extract-step (parent-2-id s) prf))
			    (res (prf-clause s))))))
  :rule-classes nil)

(defthm check-paramod-xsound
  (implies (and (check-paramod par1 pos1 par2 pos2 paramodulant)
		(xeval (universal-closure par1) (domain i) i)
		(xeval (universal-closure par2) (domain i) i))
	   (xeval (universal-closure paramodulant) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t))
  :rule-classes nil)

(defthm paramod-step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(equal (prf-rule s) 'paramod)
		(xeval (universal-closure (extract-all-steps prf))
		       (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance step-extract-xsound-closure (id (parent-1-id s)))
		 (:instance step-extract-xsound-closure (id (parent-2-id s)))
		 (:instance check-paramod-xsound
			    (par1 (extract-step (parent-1-id s) prf))
			    (par2 (extract-step (parent-2-id s) prf))
			    (paramodulant (prf-clause s))))))
  :rule-classes nil)

(defthm flip-step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(equal (prf-rule s) 'flip)
		(xeval (universal-closure (extract-all-steps prf))
		       (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance step-extract-xsound-closure (id (parent-1-id s)))))
	  )
  :rule-classes nil)

;;--------------

(defthm step-xsound
  (implies (and (wfproof prf)
		(wfproof-step s)
		(check-step prf s)
		(not (equal (prf-rule s) 'input))
		(xeval (universal-closure (extract-all-steps prf))
			      (domain i) i))
	   (xeval (universal-closure (prf-clause s)) (domain i) i))
  :hints (("Goal"
	   :in-theory (disable xeval free-vars alls)
	   :do-not-induct t
	   )

; Subgoal numbers changed by Matt K. for v2-9 (probably caused by call-stack
; change)

; fcd/Satriani v3.7 Moore - used to be Subgoal 20
	  ("Subgoal 12"
	   :use ((:instance resolve-step-xsound)))
	  ("Subgoal 16"
	   :use ((:instance flip-step-xsound)))
; fcd/Satriani v3.7 Moore - used to be Subgoal 14
	  ("Subgoal 8"
	   :use ((:instance instantiate-step-xsound)))
; fcd/Satriani v3.7 Moore - used to be Subgoal 10
	  ("Subgoal 20"
	   :use ((:instance propositional-step-xsound)))
	  ("Subgoal 4"
	   :use ((:instance paramod-step-xsound)))
	  )
  :rule-classes nil)

;;--------------

(defthm check-proof-xsound-almost
  (implies (and (wfproof done)
		(wfproof todo)
		(xeval (universal-closure (extract-all-steps done))
		       (domain i) i)
		(xeval (universal-closure (extract-input-steps todo))
		       (domain i) i)
		(check-proof done todo))
	   (xeval (universal-closure (extract-all-steps todo)) (domain i) i))
  :hints (("Goal"
	   :in-theory (disable xeval free-vars alls check-step)
	   :induct (check-proof done todo))
	  ("Subgoal *1/2"
	   :use ((:instance step-xsound
			    (prf done)
			    (s (car todo)))
		 (:instance uc-conj-left
			    (f (caddar todo))
			    (g (extract-input-steps (cdr todo))))
		 (:instance uc-conj-right
			    (f (caddar todo))
			    (g (extract-input-steps (cdr todo))))
		 )))
  :rule-classes nil)

(defthm xeval-true
  (xeval 'true dom i))

(defthm check-proof-xsound
  (implies (and (wfproof prf)
		(xeval (universal-closure (extract-input-steps prf))
			      (domain i) i)
		(check-proof nil prf))
	   (xeval (universal-closure (extract-all-steps prf)) (domain i) i))
  :hints (("Goal"
	   :in-theory (disable xeval free-vars alls)
	   :do-not-induct t
	   :use ((:instance check-proof-xsound-almost
			    (todo prf)
			    (done nil)))))
  :rule-classes nil)

;;-------------

(defthm quant-free-remove-alls
  (implies (universal-prefix-cnf f)
	   (quantifier-free (remove-leading-alls f))))

(defun initial-proof (f)
  (declare (xargs :guard (and (wff f) (quantifier-free f))
		  :verify-guards nil))
  (if (wfand f)
      (append (initial-proof (a1 f))
	      (initial-proof (a2 f)))
      (list (list 0 (list 'input) f))))

(defthm initial-proof-true-listp
  (true-listp (initial-proof f)))

(verify-guards initial-proof)

(defthm wfproof-append
  (implies (and (wfproof a)
		(wfproof b))
	   (wfproof (append a b))))

(defthm initial-proof-wf
  (implies (and (wff f)
		(quantifier-free f))
	   (wfproof (initial-proof f))))

(defun assign-ids-to-prf (prf i)
  (declare (xargs :guard (and (wfproof prf) (natp i))))
  (if (atom prf)
      prf
      (cons (cons i (cdr (car prf)))
	    (assign-ids-to-prf (cdr prf) (+ 1 i)))))

(defthm assign-ids-to-prf-preserves-wfproof
  (implies (wfproof prf)
	   (wfproof (assign-ids-to-prf prf i)))
  :hints (("Goal"
           :in-theory (disable wfjust))))

(defstub external-prover (prf) t)  ;; This is the theorem prover!!

(defthm assign-ids-to-prf-preserves-formula
  (equal (extract-all-steps (assign-ids-to-prf prf i))
	 (extract-all-steps prf)))

(defthm assign-ids-to-prf-preserves-input-formula
  (equal (extract-input-steps (assign-ids-to-prf prf i))
	 (extract-input-steps prf)))

;;-----------------------------
;; Function fix-substs-in-prf fixes an incompatibility between
;; Otter proof objects and IVY proof objects.  Otter proof objects
;; have simultaneous substitutions (the conventional type),
;; and IVY expects sequential substitutions.

(defun fix-subst-in-step (step all-vars)
  (declare (xargs :guard (and (wfproof-step step)
			      (var-list all-vars))))
  (if (equal (prf-rule step) 'instantiate)
      (list* (car step)
	     (list (car (cadr step))
		   (cadr (cadr step))
		   (seqify (caddr (cadr step))
			   all-vars
			   ))
	     (cddr step))
    step))

(defun fix-substs-in-prf (prf all-vars)
  (declare (xargs :guard (and (wfproof prf)
			      (var-list all-vars))))
  (if (atom prf)
      prf
      (cons (fix-subst-in-step (car prf) all-vars)
	    (fix-substs-in-prf (cdr prf) all-vars))))

(defthm fix-substs-in-prf-preserves-wfproof
  (implies (wfproof prf)
	   (wfproof (fix-substs-in-prf prf all-vars))))

;;---------------------------------------------------------------
;; Function (refute-n-check f) takes a closed universal-prefix-cnf formula
;; (that is, a conjunction of clauses with universal quants on top),
;; and adds derivable clauses to the conjunction.  (If we are lucky,
;; one of the new clauses is 'false.)   Some untrusted program (say
;; Otter) may be called to make the inferences.  If anything goes
;; wrong, the formula f is returned unchanged.
;;
;; The (right-assoc-p f) guard is there because of a deficiency
;; in Otter.  We need the clauses (disjunctions) to be right associated,
;; because Otter always right associates clauses in its proof objects,
;; and we have the equality condition on extract-input-steps below.

(defun refute-n-check (f)
  (declare (xargs :guard (and (wff f)
			      (not (free-vars f))
			      (universal-prefix-cnf f)
			      (var-set (leading-alls f))
			      (right-assoc-p f))))

  ;; Put these checks here instead of on the soundness theorem.

  (if (or (free-vars f) (not (var-set (leading-alls f))))
      f
    (let* ((clauses (remove-leading-alls f))
	   (otter-input (assign-ids-to-prf (initial-proof clauses) 1))
	   (otter-result (external-prover otter-input)))
      (if (not (wfproof otter-result))
	  f
	(let ((fixed-result (fix-substs-in-prf
			     otter-result
			     (free-vars (extract-all-steps otter-result)))))
	  (if (and (equal (extract-input-steps fixed-result)
			  (extract-input-steps otter-input))
		   (check-proof nil fixed-result))
	      (universal-closure (extract-all-steps fixed-result))
	    f))))))

;;------------

(defthm extract-input-append-xsound-1
  (implies (xeval (extract-input-steps prf1) dom i)
	   (equal (xeval (extract-input-steps (append prf1 prf2)) dom i)
		  (xeval (extract-input-steps prf2) dom i))))

(defthm extract-input-append-xsound-2
  (implies (not (xeval (extract-input-steps prf1) dom i))
	   (not (xeval (extract-input-steps (append prf1 prf2)) dom i))))

(defthm extract-initial-xsound-ground
  (equal (xeval (extract-input-steps (initial-proof f)) dom i)
	 (xeval f dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

(defun and-append (f g)
  (declare (xargs :guard (and (wff f) (wff g))))
  (cond ((wfand f) (list 'and (a1 f) (and-append (a2 f) g)))
	((equal f 'true) g)
	(t (list 'and f g))))

(defthm extract-append-and-append
  (equal (extract-input-steps (append a b))
	 (and-append (extract-input-steps a)
		     (extract-input-steps b))))

(defthm subst-free-distributes-over-and-append
  (equal (subst-free (and-append a b) x tm)
	 (and-append (subst-free a x tm)
		     (subst-free b x tm)))
  :hints (("Subgoal *1/6"
	   :in-theory (disable wfatomtop))))

(defthm subst-free-across-extract-initial
  (equal (subst-free (extract-input-steps (initial-proof f)) x tm)
	 (extract-input-steps (initial-proof (subst-free f x tm))))
  :hints (("goal"
	   :do-not generalize)))

(in-theory (disable extract-append-and-append))

(defthm extract-initial-xsound-alls
  (implies (var-set vars)
	   (equal (xeval (alls vars (extract-input-steps (initial-proof f)))
			 dom i)
		  (xeval (alls vars f) dom i)))
  :hints (("Goal"
	   :induct (var-induct vars f dom i)
           :in-theory (disable extract-input-steps))
	  ))

(defthm extract-initial-preserves-free-vars
  (equal (free-vars (extract-input-steps (initial-proof f)))
	 (free-vars f)))

;;-------------------

(defthm vars-strip-minus-leads-is-vars
  (equal (set-difference-equal (free-vars (remove-leading-alls f))
			       (leading-alls f))
	 (free-vars f)))

(defthm set-diff-nil-subset  ;; move to set book?
  (implies (equal (set-difference-equal a b) nil)
	   (subsetp-equal a b))
  :rule-classes nil)

(defthm subst-vars-remove-lead
  (implies (not (free-vars f))
	   (subsetp-equal (free-vars (remove-leading-alls f))
			  (leading-alls f)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance set-diff-nil-subset
			    (a (free-vars (remove-leading-alls f)))
			    (b (leading-alls f)))))))
;;-------------------

(defthm extract-initial-xsound
  (implies (and (var-set (leading-alls f))
		(not (free-vars f))
		(xeval (alls (leading-alls f) (remove-leading-alls f))
			      (domain i) i))
	   (xeval (universal-closure
			  (extract-input-steps
			   (initial-proof
			    (remove-leading-alls f))))
			 (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance xeval-alls-subset
			    (f (remove-leading-alls f))
			    (a (free-vars (extract-input-steps
					   (initial-proof
					    (remove-leading-alls f)))))
			    (b (leading-alls f)))))
	  )
  :rule-classes nil)

(defthm refute-n-check-xsound-1
  (implies (xeval f (domain i) i)
	   (xeval (refute-n-check f) (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance check-proof-xsound
			    (prf (fix-substs-in-prf
				  (external-prover
				   (assign-ids-to-prf
				    (initial-proof
				     (remove-leading-alls f))
				    1))
				  (free-vars
				   (extract-all-steps
				    (external-prover
				     (assign-ids-to-prf
				      (initial-proof
				       (remove-leading-alls f))
				      1)))))))
		 (:instance extract-initial-xsound)
		 )
	   ))
  :otf-flg t
  :rule-classes nil)

;;------------------
;; Now prove the other direction.  First, two preliminary theorems.

(defthm uc-extract-all-extract-input-xsound
  (implies (and (wfproof prf)
		(xeval (universal-closure (extract-all-steps prf))
		       (domain i) i))
	   (xeval (universal-closure (extract-input-steps prf)) (domain i) i))
  :hints (("Goal"
	   :do-not generalize
	   :hands-off (free-vars)
	   :induct (extract-all-steps prf))
	  ("Subgoal *1/2"
	   :in-theory (disable uc-conj)
	   :use ((:instance uc-conj-left
			    (f (caddar prf))
			    (g (extract-all-steps (cdr prf))))
		 (:instance uc-conj
			    (f (caddar prf))
			    (g (extract-input-steps (cdr prf))))
		 (:instance uc-conj-right
			    (f (caddar prf))
			    (g (extract-all-steps (cdr prf))))))))

(defthm xeval-uc-lead-strip
  (implies (and (var-set (leading-alls f))
		(not (free-vars f)))
	   (equal (xeval (universal-closure (remove-leading-alls f))
			 (domain i) i)
		  (xeval (alls (leading-alls f) (remove-leading-alls f))
			 (domain i) i)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xeval-alls-subset
                            (f (remove-leading-alls f))
                            (a (free-vars (remove-leading-alls f)))
                            (b (leading-alls f)))))))

(defthm refute-n-check-xsound-2
  (implies (xeval (refute-n-check f) (domain i) i)
	   (xeval f (domain i) i))
  :hints (("Goal"
	   :do-not-induct t
           :in-theory (disable xeval))
	  ("Goal'"
	   :use ((:instance uc-extract-all-extract-input-xsound
			    (prf (fix-substs-in-prf
				  (external-prover
				   (assign-ids-to-prf
				    (initial-proof
				     (remove-leading-alls f))
				    1))
				  (free-vars
				   (extract-all-steps
				    (external-prover
				     (assign-ids-to-prf
				      (initial-proof
				       (remove-leading-alls f))
				      1)))))))))
	  )
  :rule-classes nil)

;; Now put the two sides together.

(defthm refute-n-check-xsound
  (equal (xeval (refute-n-check f) (domain i) i)
	 (xeval f (domain i) i))
  :hints (("Goal"
	   :in-theory (disable refute-n-check)
	   :use ((:instance refute-n-check-xsound-1)
		 (:instance refute-n-check-xsound-2)))))

;;------------------
;; In this section, show that (refute-n-check f) preserves wff and closedness.

(defthm otter-check-wff
  (implies (check-proof done prf)
	   (wff (extract-all-steps prf))))

(defthm refute-n-check-preserves-wff
  (implies (wff f)
	   (wff (refute-n-check f)))
  :hints (("Goal"
         :do-not-induct t)))

(defthm refute-n-check-preserves-closedness
  (implies (not (free-vars f)) (not (free-vars (refute-n-check f)))))

(in-theory (disable refute-n-check))  ;; Because it is nonrecursive.

(defthm refute-n-check-fsound
  (equal (feval (refute-n-check f) i)
	 (feval f i))
  :hints (("Goal"
           :in-theory (enable xeval-feval)
           :do-not-induct t)))

