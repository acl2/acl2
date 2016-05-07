;;;============================================================================
;;;
;;; Molecular computation models in ACL2: a simulation of Lipton's experiment
;;;   solving SAT.
;;;
;;;============================================================================

#| Certification code:

(certify-book "Adleman")

|#

(in-package "ACL2")

#||
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]

;;; Logical relation between member/assoc-equal and member/equal:

(defthm equal-member-equal-member
  (equal (member-equal e l) (member e l)))

(defthm equal-assoc-equal-assoc
  (equal (assoc-equal e l) (assoc e l)))
||#

;;;----------------------------------------------------------------------------
;;;
;;; Adleman's restricted model
;;;
;;;----------------------------------------------------------------------------

;;; Definitions:

(encapsulate
 (((separate+ * *) => *)
  ((separate- * *) => *)
  ((tube-merge * *) => *)
  ((detect *) => *))

 (local
  (defun separate+ (tube X)
    (cond ((endp tube) nil)
	  ((member X (car tube))
	   (cons (car tube) (separate+ (cdr tube) X)))
	  (t (separate+ (cdr tube) X)))))

 (local
  (defun separate- (tube X)
    (cond ((endp tube) nil)
	  ((not (member X (car tube)))
	   (cons (car tube) (separate- (cdr tube) X)))
	  (t (separate- (cdr tube) X)))))

 (local
  (defun tube-merge (tube1 tube2)
    (append tube1 tube2)))

 (local
  (defun detect (tube)
    (not (endp tube))))

;;; Properties:

 (defthm member-tube-merge
   (iff (member aggr (tube-merge tube1 tube2))
	(or (member aggr tube1)
	    (member aggr tube2))))

 (defthm member-separate+
   (iff (member aggr (separate+ tube X))
	(and (member X aggr)
	     (member aggr tube)))
   :hints (("Goal"
	    :induct (separate+ tube X))))

 (defthm member-separate-
   (iff (member aggr (separate- tube X))
	(and (not (member X aggr))
	     (member aggr tube)))
   :hints (("Goal"
	    :induct (separate- tube X))))

 (defthm member-detect
   (and (implies (member e tube)
		 (detect tube))
	(implies (detect tube)
		 (member (car tube) tube))))

 )

;;;----------------------------------------------------------------------------
;;;
;;; Propositional logic
;;;
;;;----------------------------------------------------------------------------

(defun prop-variable-p (X)
  (and (symbolp X) (not (equal X nil))))

(defun truth-value-p (V)
  (or (equal V 1)
      (equal V 0)))

(defun opposite-value (V)
  (cond ((equal V 1) 0)
	(t 1)))

(defun prop-variable-value (X assig)
  (cond ((prop-variable-p X)
	 (let ((value (cdr (assoc X assig))))
	   (if (truth-value-p value)
	       value
	       0)))
	(t 0)))

;;; CNF syntax

(defun positive-literal-p (L)
  (prop-variable-p L))

(defun negative-literal-p (L)
  (and (= (len L) 2)
       (equal (first L) '-)
       (prop-variable-p (second L))
       (null (cddr L))))

(defun literal-p (L)
  (or (positive-literal-p L)
      (negative-literal-p L)))

(defun clause-p (C)
  (cond ((endp C) t)
	((literal-p (car C))
	 (clause-p (cdr C)))
	(t nil)))

(defun cnf-formula-p (F)
  (cond ((endp F) t)
	((clause-p (car F))
	 (cnf-formula-p (cdr F)))
	(t nil)))

;;; CNF semantic

(defun literal-value (L assig)
  (cond ((positive-literal-p L)
	 (prop-variable-value L assig))
	((negative-literal-p L)
	 (opposite-value (prop-variable-value (second L) assig)))
	(t 0)))

(defun clause-value (C assig)
  (cond ((endp C) 0)
	((equal (literal-value (car C) assig) 1) 1)
	(t (clause-value (cdr C) assig))))

(defun cnf-formula-value (F assig)
  (cond ((endp F) 1)
	((equal (clause-value (car F) assig) 0) 0)
	(t (cnf-formula-value (cdr F) assig))))

; Matt K. mod 5/2016 (type-set bit for {1}): This is harmless but is no longer
; needed.
;(defthm clause-value-not-0-is-1
;  (implies (not (equal (clause-value C assig) 0))
;	    (equal (clause-value C assig) 1)))

;;; Variable set of a formula

(defun literal-variable (L)
  (if (negative-literal-p L)
      (second L)
      L))

(defun clause-variables (C)
  (if (endp C)
      nil
      (union-equal (list (literal-variable (car C)))
		   (clause-variables (cdr C)))))

(defun cnf-formula-variables (F)
  (if (endp F)
      nil
      (union-equal (clause-variables (car F))
		   (cnf-formula-variables (cdr F)))))

;;;----------------------------------------------------------------------------
;;;
;;; Lipton's experiment solving SAT
;;;
;;;----------------------------------------------------------------------------

(defun l-element (label L)
  (cond ((negative-literal-p L)
	 (cons (second L) (opposite-value label)))
	(t (cons L label))))

(defun sat-lipton-clause (C tube tube-res)
  (cond ((endp C) tube-res)
	(t (let* ((tube+ (separate+ tube (l-element 1 (car C))))
		  (tube- (separate- tube (l-element 1 (car C))))
		  (n-tube-res (tube-merge tube-res tube+)))
	     (sat-lipton-clause (cdr C) tube- n-tube-res)))))

(defun sat-lipton-cnf-formula (F tube)
  (cond ((endp F) tube)
	(t (let ((n-tube (sat-lipton-clause (car F) tube nil)))
	     (sat-lipton-cnf-formula (cdr F) n-tube)))))

;;; Aggregates

(defun variable-aggregate-p (aggr X)
  (cond ((endp aggr) nil)
	((and (consp (car aggr))
	      (equal (car (car aggr)) X))
	 (and (truth-value-p (cdr (car aggr)))
	      (not (assoc X (cdr aggr)))))
	(t (variable-aggregate-p (cdr aggr) X))))

(defun clause-aggregate-p (aggr C)
  (or (endp C)
      (and (variable-aggregate-p aggr (literal-variable (car C)))
	   (clause-aggregate-p aggr (cdr C)))))

(defun cnf-formula-aggregate-p (aggr F)
  (or (endp F)
      (and (clause-aggregate-p aggr (car F))
	   (cnf-formula-aggregate-p aggr (cdr F)))))

(defthm variable-aggregate-p-valor-member
  (implies (and (prop-variable-p X)
		(variable-aggregate-p aggr X))
	   (iff (member (cons X V) aggr)
		(equal (prop-variable-value X aggr) V)))
  :hints (("Goal"
	   :in-theory (enable prop-variable-p truth-value-p))))

(in-theory (disable variable-aggregate-p))

;;; Some properties

(defthm member-clause-accumulator
  (implies (member aggr acc)
	   (member aggr (sat-lipton-clause C tube acc))))

(defthm member-clause
  (implies (member aggr (sat-lipton-clause C tube acc))
	   (or (member aggr tube)
	       (member aggr acc)))
  :rule-classes nil)

(defthm member-clause-accumulator-nil
  (implies (member aggr (sat-lipton-clause C tube nil))
	   (member aggr tube))
  :hints (("Goal"
	   :use (:instance member-clause
			   (acc nil)))))

(defthm member-cnf-formula
  (implies (member aggr (sat-lipton-cnf-formula F tube))
	   (member aggr tube))
  :rule-classes :forward-chaining)

;;; Completeness property

(defthm completeness-separate+
  (implies (and (member aggr tube)
		(literal-p L)
		(variable-aggregate-p aggr (literal-variable L))
		(equal (literal-value L aggr) 1))
	   (member aggr (separate+ tube (l-element 1 L)))))

(defthm completeness-sat-lipton-clause
  (implies (and (member aggr tube)
		(clause-p C)
		(clause-aggregate-p aggr C)
		(equal (clause-value C aggr) 1))
	   (member aggr (sat-lipton-clause C tube acc)))
  :hints (("Goal"
	   :in-theory (disable l-element literal-value)
	   :induct (sat-lipton-clause C tube acc))))

(defthm completeness-sat-lipton-cnf-formula
  (implies (and (member aggr tube)
		(cnf-formula-p F)
		(cnf-formula-aggregate-p aggr F)
		(equal (cnf-formula-value F aggr) 1))
	   (member aggr (sat-lipton-cnf-formula F tube)))
  :hints (("Goal"
	   :induct (sat-lipton-cnf-formula F tube))))

;;; Soundness property

(defthm soundness-separate+
  (implies (and (literal-p L)
		(variable-aggregate-p aggr (literal-variable L))
		(member aggr (separate+ tube (l-element 1 L))))
	   (equal (literal-value L aggr) 1)))

(defthm soundness-sat-lipton-clause
  (implies (and (clause-p C)
		(clause-aggregate-p aggr C)
		(not (member aggr acc))
		(member aggr (sat-lipton-clause C tube acc)))
	   (equal (clause-value C aggr) 1))
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable l-element member-separate+
; Matt K. mod May 2016 for addition of type-set bit for {1}:
                               (:t clause-value))
	   :induct (sat-lipton-clause C tube acc))))

(defthm soundness-sat-lipton-clause-acc-nil
  (implies (and (clause-p C)
		(clause-aggregate-p aggr C)
		(member aggr (sat-lipton-clause C tube nil)))
	   (equal (clause-value C aggr) 1))
  :hints (("Goal"
	   :use (:instance soundness-sat-lipton-clause
			   (acc nil)))))

(defthm soundness-sat-lipton-cnf-formula
  (implies (and (cnf-formula-p F)
		(cnf-formula-aggregate-p aggr F)
		(member aggr (sat-lipton-cnf-formula F tube)))
	   (equal (cnf-formula-value F aggr) 1))
  :hints (("Goal"
	   :induct (sat-lipton-cnf-formula F tube))))

;;;----------------------------------------------------------------------------
;;;
;;; Building a initial test tube
;;;
;;;----------------------------------------------------------------------------

(defun add-labeled-symbol (i X label aggr)
  (acons '(a) i (acons X label aggr)))

(defun add-labeled-symbol-lst (i X label aggrs)
  (cond ((endp aggrs) nil)
	(t (cons (add-labeled-symbol i X label (car aggrs))
		 (add-labeled-symbol-lst i X label (cdr aggrs))))))

(defun build-tube (Xs i)
  (if (endp Xs)
      (list (list (cons '(a) i)))
      (let ((rest (build-tube (cdr Xs) (+ 1 i))))
	(append (add-labeled-symbol-lst i (car Xs) 0 rest)
		(add-labeled-symbol-lst i (car Xs) 1 rest)))))

(defun build-initial-tube (F)
  (build-tube (cnf-formula-variables F) 1))

(defun sat-lipton (F)
  (sat-lipton-cnf-formula F (build-initial-tube F)))

;;; Completeness and soundness properties

(defthm subsetp-cons
  (implies (subsetp set1 set2)
	   (subsetp set1 (cons elt set2))))

(defthm subsetp-reflexive
  (subsetp set set))

(defthm member-union
  (iff (member elt (union-equal set1 set2))
       (or (member elt set1)
	   (member elt set2))))

(defthm no-duplicatesp-union
  (implies (and (no-duplicatesp set1)
		(no-duplicatesp set2))
	   (no-duplicatesp (union-equal set1 set2))))

(defthm no-duplicatesp-clause-variables
  (no-duplicatesp (clause-variables C)))

(defthm no-duplicatesp-cnf-formula-variables
  (no-duplicatesp (cnf-formula-variables F)))

(defthm clause-has-not-marks
  (implies (clause-p C)
	   (not (member '(a) (clause-variables C)))))

(defthm cnf-formula-has-not-marks
  (implies (cnf-formula-p F)
	   (not (member '(a) (cnf-formula-variables F)))))

(defun build-tube-aggregates-induction (aggr X Xs i)
  (cond ((endp Xs) (endp aggr))
	((equal (car Xs) X) (list i X))
	(t (build-tube-aggregates-induction
	    (cddr aggr) X (cdr Xs) (+ 1 i)))))

(encapsulate
 ()

 (local
  (defthm member-cddr-add-labeled-symbol-lst
    (implies (member aggr (add-labeled-symbol-lst i X label lst))
	     (member (cddr aggr) lst))))

 (local
  (defthm add-labeled-symbol-lst-properties
    (implies (member aggr (add-labeled-symbol-lst i X label lst))
	     (and (consp (car aggr))
		  (equal (car aggr) (cons '(a) i))
		  (consp (cadr aggr))
		  (equal (cadr aggr) (cons X label))))))

 (local
  (defthm member-append
    (iff (member el (append l1 l2))
	 (or (member el l1)
	     (member el l2)))))

 (defthm member-build-tube-properties
   (implies (and (consp Xs)
		 (member aggr (build-tube Xs i)))
     (and (consp aggr)
	  (consp (car aggr))
	  (equal (caar aggr) '(a))
	  (consp (cadr aggr))
	  (equal (caadr aggr) (car Xs))
	  (truth-value-p (cdadr aggr))
	  (member (cddr aggr) (build-tube (cdr Xs) (+ 1 i)))))
   :rule-classes ((:forward-chaining
		   :trigger-terms
		   ((member aggr (build-tube Xs i))))))

 )

(encapsulate
 ()

 (local
  (defthm not-assoc-build-tube
    (implies (and (consp Xs)
		  (not (equal '(a) X))
		  (not (member X Xs))

; Matt K.: Swapped the last hypothesis and the conclusion (negating both) for
; v2-9, necessary because otherwise :forward-chaining rule
; member-build-tube-properties didn't seem to fire in as many cases as it used
; to, because of the change to rewrite-clause that avoids using
; forward-chaining facts derived from a literal that has been rewritten.

		  (assoc X aggr))
	     (not (member aggr (build-tube Xs i))))
    :hints (("Goal"
	     :induct (build-tube-aggregates-induction aggr X Xs i)))
    :rule-classes nil))

 (local
  (defthm not-assoc-build-tube-one-element
    (implies (and (not (consp (cdr Xs)))
		  (consp Xs)
		  (not (equal '(a) (car Xs)))
		  (member aggr (build-tube Xs i)))
	     (not (assoc (car Xs) (cddr aggr))))))

 (local
  (in-theory (enable variable-aggregate-p)))

 (local
  (defthm build-tube-aggregates-aux
    (implies (and (consp Xs)
		  (not (member '(a) Xs))
		  (no-duplicatesp Xs)
		  (member aggr (build-tube Xs i)))
	     (variable-aggregate-p aggr (car Xs)))
    :hints (("Goal"
	     :in-theory (disable truth-value-p build-tube)
	     :use (:instance not-assoc-build-tube
			     (Xs (cdr Xs))
			     (X (car Xs))
			     (aggr (cddr aggr))
			     (i (+ 1 i)))))))

 (defthm build-tube-aggregates
   (implies (and (member X Xs)
		 (not (equal '(a) X))
		 (not (member '(a) Xs))
		 (no-duplicatesp Xs)
		 (member aggr (build-tube Xs i)))
	    (variable-aggregate-p aggr X))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable truth-value-p build-tube)
	    :induct (build-tube-aggregates-induction aggr X Xs i))
;	   ("Subgoal *1/2"
;	    :in-theory (disable build-tube-aggregates-aux)
;	    :use (:instance not-assoc-build-tube
;			    (Xs (cdr Xs))
;			    (X (car Xs))
;			    (aggr (cddr aggr))
;			    (i (+ 1 i))))
	   ))

 )

(encapsulate
 ()

 (local
  (defthm member-subset
    (implies (and (member elt set1)
		  (subsetp set1 set2))
	     (member elt set2))))

 (local
  (defthm build-tube-clause-aggregates-aux
    (implies (and (consp C)
		  (member aggr (build-tube Xs i))
		  (no-duplicatesp Xs)
		  (not (member '(a) Xs))
		  (subsetp (clause-variables C) Xs)
		  (clause-p C))
	     (variable-aggregate-p aggr (literal-variable (car C))))
    :hints (("Goal"
	     :in-theory (disable literal-variable clause-p
				 literal-p prop-variable-p)
	     :use (:instance build-tube-aggregates
			     (X (literal-variable (car C)))))))
  )

 (defthm build-tube-clause-aggregates
   (implies (and (subsetp (clause-variables C) Xs)
		 (no-duplicatesp Xs)
		 (not (member '(a) Xs))
		 (clause-p C)
		 (member aggr (build-tube Xs i)))
	    (clause-aggregate-p aggr C))
   :rule-classes nil
   :hints (("Goal"
	    :induct (clause-aggregate-p aggr C)
	    :in-theory (disable literal-variable))
;	   ("Subgoal *1/3"
;	    :in-theory (disable build-tube-clause-aggregates-aux)
;	    :use (:instance build-tube-aggregates
;			    (X (literal-variable (car C)))))
	   ))

 )

(encapsulate
 ()

 (local
  (defthm subsetp-union
    (implies (subsetp (union-equal set1 set2) set3)
	     (and (subsetp set1 set3)
		  (subsetp set2 set3)))
    :hints (("Goal"
	     :induct (union-equal set1 set2)))))

 (local
  (defthm build-tube-cnf-formula-aggregates-aux
    (implies (and (consp F)
		  (member aggr (build-tube Xs i))
		  (no-duplicatesp Xs)
		  (not (member '(a) Xs))
		  (subsetp (cnf-formula-variables F) Xs)
		  (cnf-formula-p F))
	     (clause-aggregate-p aggr (car F)))
    :hints (("Goal"
	     :use (:instance build-tube-clause-aggregates
			     (C (car F)))))))

 (defthm build-tube-cnf-formula-aggregates
   (implies (and (subsetp (cnf-formula-variables F) Xs)
		 (no-duplicatesp Xs)
		 (not (member '(a) Xs))
		 (cnf-formula-p F)
		 (member aggr (build-tube Xs i)))
	    (cnf-formula-aggregate-p aggr F))
   :rule-classes nil
   :hints (("Goal"
	    :induct (cnf-formula-aggregate-p aggr F))
;	   ("Subgoal *1/3"
;	    :in-theory (disable build-tube-cnf-formula-aggregates-aux)
;	    :use (:instance build-tube-clause-aggregates
;			    (C (car F))))
	   ))

 )

(defthm build-initial-tube-cnf-formula-aggregates
  (implies (and (cnf-formula-p F)
		(member aggr (build-initial-tube F)))
	   (cnf-formula-aggregate-p aggr F))
  :hints (("Goal"
	   :use (:instance build-tube-cnf-formula-aggregates
			   (i 1)
			   (Xs (cnf-formula-variables F))))))

(defthm completeness-sat-lipton
  (implies (and (cnf-formula-p F)
		(member aggr (build-initial-tube F))
		(equal (cnf-formula-value F aggr) 1))
	   (member aggr (sat-lipton F))))

(defthm soundness-sat-lipton
  (implies (and (cnf-formula-p F)
		(member aggr (sat-lipton F)))
	   (equal (cnf-formula-value F aggr) 1)))

;;;----------------------------------------------------------------------------
;;;
;;; Satisfiability checker
;;;
;;;----------------------------------------------------------------------------

(defun sat-lipton-p (F)
  (detect (sat-lipton F)))

(defthm soundness-sat-lipton-p
  (implies (and (cnf-formula-p F)
		(sat-lipton-p F))
	   (equal (cnf-formula-value F (car (sat-lipton F))) 1))
  :hints (("Goal"
	   :in-theory (disable sat-lipton))))

(defun build-aggregate-assig (Xs assig i)
  (if (endp Xs)
      (list (cons '(a) i))
      (let ((rest (build-aggregate-assig (cdr Xs) assig (+ 1 i))))
	(add-labeled-symbol
	 i (car Xs) (prop-variable-value (car Xs) assig) rest))))

(defthm aggregate-assig-equal-prop-variable-value
  (implies (member X Xs)
	   (equal (prop-variable-value X (build-aggregate-assig Xs assig i))
		  (prop-variable-value X assig))))

(defthm aggregate-assig-equal-literal-value
  (implies (member (literal-variable L) Xs)
	   (equal (literal-value L (build-aggregate-assig Xs assig i))
		  (literal-value L assig))))

(defthm member-subset
  (implies (and (member elt set1)
		(subsetp set1 set2))
	   (member elt set2)))

(in-theory (disable literal-variable literal-p literal-value))

(defthm aggregate-assig-equal-clause-value
  (implies (subsetp (clause-variables C) Xs)
	   (equal (clause-value C (build-aggregate-assig Xs assig i))
		  (clause-value C assig)))
  :hints (("Goal"
	   :induct (clause-variables C))))

(defthm subsetp-cnf-formula-variables-cdr
  (implies (subsetp (cnf-formula-variables F) Xs)
	   (subsetp (cnf-formula-variables (cdr F)) Xs)))

(defthm subsetp-union-equal
  (iff (subsetp (union-equal set1 set2) set3)
       (and (subsetp set1 set3)
	    (subsetp set2 set3)))
  :hints (("Goal"
	   :induct (union-equal set1 set2))))

(defthm aggregate-assig-equal-cnf-formula-value
  (implies (subsetp (cnf-formula-variables F) Xs)
	   (equal (cnf-formula-value F (build-aggregate-assig Xs assig i))
		  (cnf-formula-value F assig)))
  :hints (("Goal"
	   :induct (cnf-formula-variables F))))

(defthm member-add-labeled-symbol-lst
  (implies (member aggr aggrs)
	   (member (add-labeled-symbol i x v aggr)
		   (add-labeled-symbol-lst i x v aggrs))))

(defthm member-append
  (iff (member elt (append lst1 lst2))
       (or (member elt lst1)
	   (member elt lst2))))

(defthm aggregate-assig-member-tube
  (member (build-aggregate-assig Xs assig i) (build-tube Xs i))
  :hints (("Goal"
	   :in-theory (disable add-labeled-symbol))))

(defthm completeness-sat-lipton-p-aux
  (implies (and (cnf-formula-p F)
		(equal (cnf-formula-value F assig) 1))
	   (member (build-aggregate-assig (cnf-formula-variables F) assig 1)
		   (sat-lipton F)))
  :rule-classes :forward-chaining)

(defthm completeness-sat-lipton-p
  (implies (and (cnf-formula-p F)
		(equal (cnf-formula-value F assig) 1))
	   (sat-lipton-p F))
  :hints (("Goal" :in-theory (disable sat-lipton))))

;;;----------------------------------------------------------------------------
;;;
;;; Examples
;;;
;;;----------------------------------------------------------------------------

#|

(include-book
 "Adleman")

(set-ld-redefinition-action '(:warn . :overwrite) state)

(defun separate+ (tube X)
  (cond ((endp tube) nil)
	((member-equal X (car tube))
	 (cons (car tube) (separate+ (cdr tube) X)))
	(t (separate+ (cdr tube) X))))

(defun separate- (tube X)
  (cond ((endp tube) nil)
	((not (member-equal X (car tube)))
	 (cons (car tube) (separate- (cdr tube) X)))
	(t (separate- (cdr tube) X))))

(defun tube-merge (tube1 tube2)
  (append tube1 tube2))

(defun detect (tube)
  (not (endp tube)))

(defconst *example* '((p q) ((- q) p)))

(build-initial-tube *example*)

;;; ((((A) . 1) (Q . 0) ((A) . 2) (P . 0) ((A) . 3))
;;;  (((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;;  (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3))
;;;  (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3)))

(value :q)

(sat-lipton *example*)

;;; (SAT-LIPTON-CNF-FORMULA
;;;  '((P Q) ((- Q) P))
;;;  '((((A) . 1) (Q . 0) ((A) . 2) (P . 0) ((A) . 3))
;;;    (((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;;    (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3))
;;;    (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))))
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   '(P Q)
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 0) ((A) . 3))
;;; 	     (((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3)))
;;; 	   ())
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   '(Q)
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 0) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3)))
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))))
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   ()
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 0) ((A) . 3)))
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3))))
;;;
;;; (SAT-LIPTON-CNF-FORMULA
;;;  '(((- Q) P))
;;;  '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;;    (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))
;;;    (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3))))
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   '((- Q) P)
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3)))
;;; 	   ())
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   '(P)
;;; 	   '((((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3)))
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))))
;;;
;;;    => (SAT-LIPTON-CLAUSE
;;; 	   ()
;;; 	   '((((A) . 1) (Q . 1) ((A) . 2) (P . 0) ((A) . 3)))
;;; 	   '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;; 	     (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))))
;;;
;;; (SAT-LIPTON-CNF-FORMULA
;;;  ()
;;;  '((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;;    (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3))))
;;;
;;; ((((A) . 1) (Q . 0) ((A) . 2) (P . 1) ((A) . 3))
;;;  (((A) . 1) (Q . 1) ((A) . 2) (P . 1) ((A) . 3)))

|#

;;;============================================================================
