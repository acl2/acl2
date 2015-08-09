(in-package "ACL2")

;; We already have the "step" versions step-sk and step-ex,
;; which operate on the leftmost existential quantifier.
;; Here, we define the top versions (which call the step
;; versions) to handle all existential quantifiers.

(include-book "sk-step-sound")

(include-book "permutations")

;;----------------
;; Therorems to verify skolem guard.

(defthm step-sk-qvars-subbag
  (subbag (quantified-vars (step-sk f vars fsym))
	  (quantified-vars f)))

(defthm setp-member-remove1-equal
  (implies (setp b)
	   (not (member-equal x (remove1-equal x b)))))

(defthm setp-remove1-equal
  (implies (setp b)
	   (setp (remove1-equal x b))))

(defthm setp-not-subbag
  (implies (and (setp b)
		(not (setp a)))
	   (not (subbag a b))))

(defthm step-sk-preserves-setp-qvars
  (implies (setp (quantified-vars f))
	   (setp (quantified-vars (step-sk f vars fsym))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance setp-not-subbag
			    (a (quantified-vars (step-sk f vars fsym)))
			    (b (quantified-vars f)))))))

(defthm step-sk-reduces-exists-count
  (implies (and n (step-sk-arity f n))
	   (< (exists-count (step-sk f vars fsym))
	      (exists-count f)))
  :hints (("Goal"
	   :induct (step-sk-sym-i2 f vars n))))

(defthm step-sk-reduces-exists-count-2
  (implies (step-sk-arity f 0)
	   (< (exists-count (step-sk f vars fsym))
	      (exists-count f)))
  :hints (("Goal"
         :use ((:instance step-sk-reduces-exists-count (n 0))))))

;;----------------------------
;; Full skolemization and extension, unprotected versions.

(include-book "gensym-e")

(defthm union-symbol-listp
  (implies (and (symbol-listp a)
		(symbol-listp b))
	   (symbol-listp (union-equal a b))))

(defthm funcs-in-formula-symbol-listp
  (symbol-listp (funcs-in-formula f)))

(defun skolem (f)
  (declare (xargs :measure (exists-count f)
		  :guard (and (wff f) (ok-for-skolem f))))
  (if (step-sk-arity f 0)
      (skolem (step-sk f nil (gen-symbol 'sk (funcs-in-formula f))))
      f))

(defun skolem-extend (f i)
  (declare (xargs :measure (exists-count f)
		  :guard (and (wff f) (ok-for-skolem f))))
  (if (step-sk-arity f 0)
      (skolem-extend (step-sk f nil (gen-symbol 'sk (funcs-in-formula f)))
		     (step-ex f (gen-symbol 'sk (funcs-in-formula f)) nil i))
      i))

(defthm skolem-fsound
  (implies (setp (quantified-vars f))
	   (equal (feval (skolem f) (skolem-extend f i))
		  (feval f i))))

;;---------------------
;; Now, the final, protected versions.

(defun skolemize (f)
  (declare (xargs :guard (and (wff f) (ok-for-skolem f))))
  (if (ok-for-skolem f)
      (skolem f)
      f))

(defun skolemize-extend (f i)
  (declare (xargs :guard (and (wff f) (ok-for-skolem f))))
  (if (ok-for-skolem f)
      (skolem-extend f i)
      i))

(defthm skolemize-fsound
  (equal (feval (skolemize f) (skolemize-extend f i))
	 (feval f i)))

;;---------------------
;; A few additional properties of the skolemization functions.

(defthm skolemize-preserves-nnfp
  (implies (nnfp f)
	   (nnfp (skolemize f))))

(defthm skolemize-preserves-wff
  (implies (wff f)
	   (wff (skolemize f))))

(defthm skolemize-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (skolemize f)))))

(defthm skolemize-preserves-setp-qvars
  (implies (setp (quantified-vars f))
	   (setp (quantified-vars (skolemize f)))))

(defthm skolemize-extend-with-free-vars
  (implies (free-vars f)
	   (equal (skolemize-extend f i) i)))

(defthm not-step-sk-arity-exists-count-0
  (implies (and (nnfp f)
		n
		(not (step-sk-arity f n)))
	   (equal (exists-count f) 0))
  :hints (("Goal"
	   :induct (exists-count f)))
  :rule-classes nil)

(defthm not-step-sk-arity-exists-count-0-2
  (implies (and (not (step-sk-arity f 0))
		(nnfp f))
	   (equal (exists-count f) 0))
  :hints (("Goal"
	   :use ((:instance not-step-sk-arity-exists-count-0 (n 0))))))

(defthm skolemize-exists-free
  (implies (ok-for-skolem f)
           (equal (exists-count (skolemize f)) 0)))

;;----------------------------------------------------------------
;; Disable the top skolemization functions, because they are not recursive.

(in-theory (disable skolemize skolemize-extend))
