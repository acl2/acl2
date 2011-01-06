(in-package "ACL2")

;; Define a function to right-associate conjunctions and disjunctions.
;; Just like the other normal-form operations, we prove a syntactic
;; correctness theorem, a soundness theorem, and several perservation of
;; property theorems.
;;
;; The need for right-assoc arises from the interface to external-prover
;; (i.e., Otter).  The external-prover isn't supposed to alter the
;; inital proof object, but Otter always right associates it, so
;; we have to make sure the initial proof object is right associated.

(include-book "stage")

(defun rat (op f g)
  (declare (xargs :guard (and (or (equal op 'and)
				  (equal op 'or))
			      (wff f)
			      (wff g))))
  (cond ((and (equal op 'and) (wfand f)) (list op (a1 f) (rat op (a2 f) g)))
	((and (equal op 'or)  (wfor f))  (list op (a1 f) (rat op (a2 f) g)))
	(t (list op f g))))

(defthm rat-wff
  (implies (and (or (equal op 'and)
		    (equal op 'or))
		(wff f)
		(wff g))
	   (wff (rat op f g))))

(defun right-assoc (f)  ;; I think this algorithm is unnecessarily slow
  (declare (xargs :guard (wff f)))
  (cond ((wfand f) (rat 'and (right-assoc (a1 f)) (right-assoc (a2 f))))
	((wfor f) (rat 'or  (right-assoc (a1 f)) (right-assoc (a2 f))))
	((wfbinary f) (list (car f) (right-assoc (a1 f)) (right-assoc (a2 f))))
	((wfnot f) (list 'not (right-assoc (a1 f))))
	((wfquant f) (list (car f) (a1 f) (right-assoc (a2 f))))
	(t f)))

(defthm right-assoc-wff
  (implies (wff f)
	   (wff (right-assoc f))))
	
(defthm rat-xsound
  (implies (or (equal op 'and)
	       (equal op 'or))
	   (equal (xeval (rat op f g) dom i)
		  (xeval (list op f g) dom i))))

(defthm right-assoc-subst-free-commute
  (equal (subst-free (right-assoc f) x tm)
	 (right-assoc (subst-free f x tm))))

(defthm right-assoc-xsound
  (equal (xeval (right-assoc f) dom i)
	 (xeval f dom i))
  :hints (("Goal"
	   :induct (xeval-i f dom i))))

(defthm right-assoc-fsound
  (equal (feval (right-assoc f) i)
	 (feval f i))
  :hints (("Goal"
	   :in-theory (enable xeval-feval))))

(defun right-assoc-p (f)  ;; no 'and has and 'and as left child; same for 'or.
  (declare (xargs :guard (and (wff f))))
  (cond ((wfand f) (and (not (wfand (a1 f)))
			(right-assoc-p (a1 f))
			(right-assoc-p (a2 f))))
	((wfor f) (and (not (wfor (a1 f)))
		       (right-assoc-p (a1 f))
		       (right-assoc-p (a2 f))))
	((wfbinary f) (and (right-assoc-p (a1 f))
			   (right-assoc-p (a2 f))))
	((wfnot f) (right-assoc-p (a1 f)))
	((wfquant f) (right-assoc-p (a2 f)))
	(t t)))

(defthm rat-ok
  (implies (and (right-assoc-p f)
		(right-assoc-p g)
		(or (equal op 'and)
		    (equal op 'or)))
	   (right-assoc-p (rat op f g))))

(defthm right-assoc-ok
  (right-assoc-p (right-assoc f)))

;------------------------------------
; Now, we have to prove that right-assoc preserves a bunch of properties.

;; Prove that right-assoc preserves closedness.

(defthm right-assoc-doesnt-introduce-free-vars
  (implies (not (free-occurrence x f))
	   (not (free-occurrence x (right-assoc f)))))

(defthm right-assoc-preserves-closedness-almost
  (implies (not (member-equal x (free-vars f)))
	   (not (member-equal x (free-vars (right-assoc f)))))
  :hints (("Goal"
	   :use ((:instance free-free)
		 (:instance free-free (f (right-assoc f)))))))

(defthm right-assoc-preserves-closedness
  (implies (not (free-vars f))
	   (not (free-vars (right-assoc f))))
  :hints (("Goal"
	   :use ((:instance member-equal
			    (x (car (free-vars (right-assoc f))))
			    (lst (free-vars (right-assoc f))))
		 (:instance member-equal
			    (x (car (free-vars f)))
			    (lst (free-vars f)))))))

;;----------------------
;; right-assoc preserves quantifier-free

(defthm ratp-preserves-quantifier-free
  (implies (and (quantifier-free f)
		(quantifier-free g)
		(or (equal op 'and)
		    (equal op 'or)))
	   (quantifier-free (rat op f g))))

(defthm right-assoc-preserves-quantifier-free
  (implies (quantifier-free f)
	   (quantifier-free (right-assoc f))))

;;--------------------
;; right-assoc preserves leading-alls

(defthm leading-alls-right-assoc
  (equal (leading-alls (right-assoc f)) (leading-alls f)))

;;----------------------
;; right-assoc preserves cnfp

(defthm cnfp-rat-and
  (implies (and (cnfp f)
		(cnfp g))
	   (cnfp (rat 'and f g))))

(defthm rat-preserves-op
  (equal (car (rat op f g)) op))

(defthm right-assoc-preserves-car
  (equal (car (right-assoc f)) (car f)))

(defthm cnfp-rat-or
  (implies (and (not (wfand f))
		(not (wfand g))
		(cnfp f)
		(cnfp g))
	   (cnfp (rat 'or f g))))

(defthm right-assoc-consp
  (equal (consp (right-assoc f)) (consp f)))

(defthm right-assoc-preserves-cnfp-helper  ;; why is this necessary??
  (implies (and (wfor f)
		(not (consp (cddadr f)))
		(cnfp (right-assoc (cadr f)))
		(cnfp (right-assoc (caddr f)))
		(not (consp (cddadr (cdr f)))))
	   (cnfp (rat 'or
		      (right-assoc (cadr f))
		      (right-assoc (caddr f)))))
  :hints (("Goal"
	   :use ((:instance cnfp-rat-or
			    (f (right-assoc (cadr f)))
			    (g (right-assoc (caddr f))))))))

(defthm right-assoc-preserves-cnfp
  (implies (cnfp f)
	   (cnfp (right-assoc f)))
  :hints (("Goal"
	   :induct (cnfp f))))

;;----------------------
;; right-assoc preserves universal-prefix-cnf

(defthm right-assoc-preserves-universal-prefix-cnf
  (implies (universal-prefix-cnf f)
	   (universal-prefix-cnf (right-assoc f)))
  :hints (("Goal"
	   :induct (universal-prefix-cnf f))))
