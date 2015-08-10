(in-package "ACL2")

;; This book contains the definitions of the "step" functions
;; for Skolemization.  Instead of Skolemizing all existential
;; quantifiers in one pass, we repeatedly ("step-by-step")
;; Skolemize the leftmost existential until done.
;;
;; Function step-sk Skolemizes the leftmost existential quantifier.
;; To prove soundness of step-sk, we use a companion function
;; step-ex, which extends an interpretaion with a Skolem function.
;; The guts of step-ex are the mutually recursive pair build-sk/build-sk-d,
;; which have recursion similar to the evaluation function feval/feval-d.
;;
;; Also, we also prove some preservation-of-property lemmas for step-sk.

(include-book "stage")
(include-book "sk-misc-lemmas")
(local (include-book "../../../../../ordinals/e0-ordinal"))

;;---------------------------------------------------------------
;; (step-sk f vars fsym) tries to skolemize the left-most
;; existential quantifier.

(defun step-sk (f vars fsym)
  (declare (xargs :guard (and (wff f)
			      (nnfp f)
			      (var-list vars)
			      (function-symbol fsym))))
  (cond ((or (wfand f) (wfor f))
	 (if (> (exists-count (a1 f)) 0)
	     (list (car f) (step-sk (a1 f) vars fsym) (a2 f))
	     (list (car f) (a1 f) (step-sk (a2 f) vars fsym))))

	((wfall f) (list 'all (a1 f) (step-sk (a2 f)
					      (append vars (list (a1 f)))
					      fsym)))
	((wfexists f)
	 (subst-free (a2 f) (a1 f) (cons fsym vars)))
	(t f)))

;;---------------

(defthm step-sk-preserves-wff
  (implies (and (wff f)
		(var-list vars)
		(function-symbol fsym))
	   (wff (step-sk f vars fsym))))

(defthm step-sk-preserves-nnfp
  (implies (nnfp f)
	   (nnfp (step-sk f vars fsym))))

;;---------------
;; (step-sk-arity f n):  Get the arity for the Skolem function for
;; the leftmost existential quantifier.  Parameter n counts
;; universals along the way.  Return nil if there are no existentials.

(defun step-sk-arity (f n)
  (declare (xargs :guard (and (wff f)
			      (nnfp f)
			      (natp n))))
  (cond ((or (wfand f) (wfor f))
	 (if (> (exists-count (a1 f)) 0)
	     (step-sk-arity (a1 f) n)
	     (step-sk-arity (a2 f) n)))
	((wfall f) (step-sk-arity (a2 f) (+ 1 n)))
	((wfexists f) n)
	(t nil)))

;;---------------------------------------------------------------
;; (val-or-0 p x dom i) is the first member of dom that makes p
;; true when substituted for x.  If there is none, 0 is returned.

(defun validator (p x dom i)  ;; return a domain element or nil
  (declare (xargs :guard (and (wff p)
			      (variable-term x)
			      (domain-term-list (fringe dom)))))
  (if (atom dom)
      (if (feval (subst-free p x dom) i)
	  dom
	nil)
    (if (validator p x (car dom) i)
	(validator p x (car dom) i)
      (validator p x (cdr dom) i))))

(defmacro val-or-0 (p x dom i)
  (list 'if (list 'validator p x dom i)
	(list 'validator p x dom i)
	'0))

;;--------------------
;; (build-sk f vals i) builds a Skolem function (that is, an alist of
;; tuple-value pairs) for the left-most existential quantifier.

(mutual-recursion

 (defun build-sk (f vals i)
   (declare (xargs :measure (cons (cons (wff-count f) 2) 0)
		   :guard (and (wff f)
			       (nnfp f)
			       (domain-term-list vals))
		   :verify-guards nil))
   (cond
    ((or (wfand f) (wfor f))
     (if (> (exists-count (a1 f)) 0)
	 (build-sk (a1 f) vals i)
       (build-sk (a2 f) vals i)))
    ((wfexists f) (list (cons vals (val-or-0 (a2 f) (a1 f) (domain i) i))))
    ((wfall f) (build-sk-d f vals (domain i) i)) ;; recurse-on-domain
    (t nil)))

 (defun build-sk-d (f vals dom i)
   (declare (xargs :measure (cons (cons (wff-count f) 1) (acl2-count dom))
		   :guard (and (wff f)
			       (nnfp f)
			       (domain-term-list vals)
			       (domain-term-list (fringe dom))
			       (subsetp-equal (fringe dom)
					      (fringe (domain i))))))
   (cond ((wfall f)
	  (if (atom dom)
	      (build-sk (subst-free (a2 f) (a1 f) dom)
			(append vals (list dom)) i)
	      (append (build-sk-d f vals (car dom) i)
		      (build-sk-d f vals (cdr dom) i))))
	 (t nil)))

 )  ;; end of mutual recursion

;;------------------
;; build-sk-i is an induction scheme corresponding to build-sk.

(defun build-sk-i (flg f vals dom i)
  (declare (xargs :measure (cons (cons (wff-count f)
				       (if flg 2 1))
				 (acl2-count dom))
		  :guard (and (wff f)
			      (domain-term-list vals)
			      (implies (not flg)
				       (domain-term-list (fringe dom))))
		  :verify-guards nil))
  (if flg
      (cond ((or (wfand f) (wfor f))
	     (if (> (exists-count (a1 f)) 0)
		 (build-sk-i t (a1 f) vals 'junk i)
	         (build-sk-i t (a2 f) vals 'junk i)))
	    ((wfexists f) nil)
	    ((wfall f) (build-sk-i nil f vals (domain i) I))
	    (t nil))
    (cond ((wfall f) (if (atom dom)
			 (build-sk-i t
				    (subst-free (a2 f) (a1 f) dom)
				    (append vals (list dom))
				    'junk
				    i)
		       (append (build-sk-i nil f vals (car dom) i)
			       (build-sk-i nil f vals (cdr dom) i))))
	  (t nil))))

;;---------------------
;; Verify the guard for build-sk and build-sk-i.

(defthm build-sk-true-listp-flg
  (if flg
      (true-listp (build-sk f vals i))
      (true-listp (build-sk-d f vals dom i)))
  :hints (("Goal"
	   :induct (build-sk-i flg f vals dom i)))
  :rule-classes nil)

(defthm build-sk-d-true-listp
  (true-listp (build-sk-d f vals dom i))
  :hints (("Goal"
	   :by (:instance build-sk-true-listp-flg (flg nil)))))

(defthm build-sk-i-true-listp
  (true-listp (build-sk-i flg f vals dom i)))

(verify-guards build-sk)

(verify-guards build-sk-i)

;;---------------------
;; After we build the skolem function, we have to be able to insert it
;; into an interpretation.  It is useful to have two versions, step-ex
;; and step-ex-d, corresponding to the two mutually recursive build
;; functions.

(defun insert-func-into-interp (fsym-arity func i)
  (declare (xargs :guard (alistp func)))
  (if (consp fsym-arity)
      (cons (domain i)
	    (cons (relations i)
		  (cons (cons fsym-arity func) (functions i))))
    i))

(defthm build-sk-alistp-flg  ;; for step-sk guard
  (if flg
      (alistp (build-sk f vals i))
      (alistp (build-sk-d f vals dom i)))
  :hints (("Goal"
	   :induct (build-sk-i flg f vals dom i)))
  :rule-classes nil)

(defthm build-sk-alistp  ;; for step-sk guard
  (alistp (build-sk f vals i))
  :hints (("Goal"
	   :by (:instance build-sk-alistp-flg (flg t)))))

(defthm build-sk-d-alistp  ;; for step-sk guard
  (alistp (build-sk-d f vals dom i))
  :hints (("Goal"
	   :by (:instance build-sk-alistp-flg (flg nil)))))

(defun step-ex (f fsym vals i)
  (declare (xargs :guard (and (wff f) (nnfp f) (function-symbol fsym)
			      (domain-term-list vals))))
  (insert-func-into-interp (cons fsym (step-sk-arity f (len vals)))
			   (build-sk f vals i) i))

(defun step-ex-d (f fsym vals dom i)
  (declare (xargs :guard (and (wff f) (nnfp f) (function-symbol fsym)
			      (domain-term-list vals)
			      (domain-term-list (fringe dom))
			      (subsetp-equal (fringe dom)
					     (fringe (domain i))))))
  (insert-func-into-interp (cons fsym (step-sk-arity f (len vals)))
			   (build-sk-d f vals dom i) i))

;;---------
;; The following induction scheme is useful when proving things
;; involving both step-sk and step-sk-sym.  The recursion on f
;; is similar to both; the vars argument is like step-sk, and the n
;; argument is like step-sk-sym.

(defun step-sk-sym-i2 (f vars n)
  (declare (xargs :guard (and (wff f)
			      (nnfp f)
			      (var-list vars)
			      (natp n))))
  (cond ((or (wfand f) (wfor f))
	 (if (> (exists-count (a1 f)) 0)
	     (step-sk-sym-i2 (a1 f) vars n)
	     (step-sk-sym-i2 (a2 f) vars n)))
	((wfall f) (step-sk-sym-i2 (a2 f)
				   (append vars (list (a1 f)))
				   (+ 1 n)))
	(t nil)))

(defthm step-sk-without-exists
  (implies (equal (exists-count f) 0)
	   (equal (step-sk f vars fsym) f)))

;;---------------------------------------------------------
;; step-sk-preserves-closedness

(defthm not-var-occurrence-append-list
  (implies (and (not (var-occurrence-term-list x vars))
		(variable-term y)
		(not (equal x y)))
	   (not (var-occurrence-term-list x (append vars (list y))))))

(defthm not-var-occurrence-subst-term-list
  (implies (and (variable-term y)
		(var-list vars)
		(not (var-occurrence-term-list x l))
		(not (var-occurrence-term-list x vars)))
	   (not (var-occurrence-term-list
		 x
		 (subst-term-list l y (cons fsym vars))))))

(defthm not-free-occurrence-subst-free
  (implies (and (variable-term y)
		(var-list vars)
		(not (free-occurrence x f))
		(not (var-occurrence-term-list x vars)))
	   (not (free-occurrence x (subst-free f y (cons fsym vars)))))
  :hints (("Goal"
	   :induct (free-occurrence x f))))

(defthm not-var-ococurrence-list-tm
  (implies (and (var-list vars)
		(not (var-occurrence-term-list x vars)))
	   (not (var-occurrence-term-list x (list (cons fsym vars))))))

(defthm not-free-occurrence-list-tm
  (implies (and (var-list vars)
		(not (var-occurrence-term-list x vars)))
	   (not (free-occurrence x (subst-free f x (cons fsym vars)))))
  :hints (("Goal"
	   :induct (free-occurrence x (subst-free f x (cons fsym vars))))))

(defthm step-sk-preserves-closedness-h1
  (implies (and (not (free-occurrence x f))
		(var-list vars)
		(not (var-occurrence-term-list x vars)))
	   (not (free-occurrence x (step-sk f vars fsym)))))

(defthm step-sk-preserves-closedness-h2
  (implies (not (free-occurrence x f))
	   (not (free-occurrence x (step-sk f nil fsym)))))

(defthm step-sk-preserves-closedness-h3
  (implies (not (member-equal x (free-vars f)))
	   (not (member-equal x (free-vars (step-sk f nil fsym)))))
  :hints (("Goal"
           :use ((:instance free-free)
		 (:instance free-free (f (step-sk f nil fsym)))))))

(defthm step-sk-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (step-sk f nil fsym))))
  :hints (("Goal"
	   :do-not-induct t
           :use ((:instance consp-has-member-equal
			    (x (free-vars (step-sk f nil fsym))))))))

