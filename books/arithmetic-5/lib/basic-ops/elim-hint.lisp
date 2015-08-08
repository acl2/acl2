; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; elim-hint.lisp
;;;
;;; When there is more than one destructor-elimination to choose from,
;;; we want to be able to try all of them.  This file implements a
;;; clause-processor/computed-hint combination to allow us to do so.
;;;
;;; We use the computed hint to
;;; 1. Collect a list of clause sets, each of which represents the
;;; affects of a destructor-elimination choice.
;;; 2. Generate an :or hint for this list, each branch of which
;;; uses the-ultimate-clause-processor.
;;;
;;; The-ultimate-clause-processor is a trivial clause processor, which
;;; takes a clause (which is ignored) and a clause list which is
;;; returned as the new set of clauses to be proven.
;;;
;;; Given a fixed set of elim rules, one could probably wrap both
;;; parts up into a verified clause processor, except for the use of
;;; type-alist-clause.  I don't think the type-alist is used for
;;; anything but heuristic purposes, so it may be possible to drop,
;;; but I haven't looked very closely.  There may be other issues as
;;; well, and I do not feel like undertaking the task now.
;;;
;;; Here is the theorem that led me to try this.  Depending on the
;;; ordering of the LHS and RHS of the concl, different choices are
;;; made about what to eliminate.  One is good, and one is bad.
#||
(thm
 (IMPLIES (AND (INTEGERP I)
	       (INTEGERP J)
	       (RATIONALP X)
	       (< J 0)
	       (NOT (INTEGERP (* (/ I) (/ J) X)))
	       (INTEGERP (* (/ J) (FLOOR X I))))
	  (EQUAL (+ (* I J) (MOD X I))
		 (MOD X (* I J)))))
||#
;;; It is now obvious, but I was surprised at first that reordering an
;;; equality in the concl of a thm could affect the proof.
;;;
;;; Something else to consider if one is feeling adventurous, is
;;; combining generalization and destructor-elimination, so that
;;; (mod (* x y) z), for example, would be a candidate.  But this
;;; is probably daft.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "default-hint")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(table acl2-defaults-table :state-ok t)

(defun nominate-destructor-candidate-hint
  (term eliminables type-alist clause fns-to-elim ens wrld votes nominations)
  (declare (xargs :mode :program))
  (cond
   ((flambda-applicationp term)
    nominations)
   ((not (member-equal (ffn-symb term) fns-to-elim))
    nominations)
   (t (let ((rule (getprop (ffn-symb term) 'eliminate-destructors-rule
                           nil 'current-acl2-world wrld)))
        (cond
         ;;((or (null rule)
         ;;     (not (enabled-numep (access elim-rule rule :nume) ens)))
         ;; nominations)
	 ((null rule)
	  nominations)
         (t (let ((crucial-arg (nth (access elim-rule rule :crucial-position)
                                    (fargs term))))
              (cond
               ((variablep crucial-arg)
                (let* ((alist (pairlis$
                               (fargs
                                (access elim-rule rule :destructor-term))
                               (fargs term)))
                       (inst-destructors
                        (sublis-var-lst
                         alist
                         (cons (access elim-rule rule :destructor-term)
                               (access elim-rule rule :destructor-terms))))
                       (pseudo-clause (sublis-expr-lst
                                       (pairlis$ inst-destructors nil)
                                       clause)))
                  (cond
                   ((not (every-occurrence-equiv-hittablep-in-clausep
                          (access elim-rule rule :equiv)
                          crucial-arg
                          pseudo-clause ens wrld))
                    nominations)
                   ((assoc-equal term nominations)
                    (second-nomination term votes nominations))
                   ((member crucial-arg eliminables)
                    (cond
                     ((occurs-nowhere-else crucial-arg
                                           (fargs term)
                                           (access elim-rule rule
                                                   :crucial-position)
                                           0)
                      (let* ((inst-hyps
                              (sublis-var-lst alist
                                              (access elim-rule rule :hyps))))
                        (cond
                         ((some-hyp-probably-nilp inst-hyps
                                                  type-alist ens wrld)
                          nominations)
                         (t (first-nomination term votes nominations)))))
                     (t nominations)))
                   (t nominations))))
               (t (nominate-destructor-candidate-hint crucial-arg
						      eliminables
						      type-alist
						      clause
						      fns-to-elim
						      ens
						      wrld
						      (cons term votes)
						      nominations))))))))))

(mutual-recursion

 (defun nominate-destructor-candidates-hint
  (term eliminables type-alist clause fns-to-elim ens wrld nominations)
   (declare (xargs :mode :program))
   (cond ((variablep term) nominations)
	 ((fquotep term) nominations)
	 (t (nominate-destructor-candidates-lst-hint
	     (fargs term)
	     eliminables
	     type-alist
	     clause
	     fns-to-elim
	     ens
	     wrld
	     (nominate-destructor-candidate-hint term
						 eliminables
						 type-alist
						 clause
						 fns-to-elim
						 ens
						 wrld
						 nil
						 nominations)))))

 (defun nominate-destructor-candidates-lst-hint
   (terms eliminables type-alist clause fns-to-elim ens wrld nominations)
  (declare (xargs :mode :program))
   (cond ((null terms) nominations)
	 (t (nominate-destructor-candidates-lst-hint
	     (cdr terms)
	     eliminables
	     type-alist
	     clause
	     fns-to-elim
	     ens
	     wrld
	     (nominate-destructor-candidates-hint (car terms)
						  eliminables
						  type-alist
						  clause
						  fns-to-elim
						  ens
						  wrld
						  nominations)))))

 )

(defun select-instantiated-elim-rule-hint (clause type-alist eliminables fns-to-elim ens wrld)
  (declare (xargs :mode :program))
  (let ((nominations
         (nominate-destructor-candidates-lst-hint clause
						  eliminables
						  type-alist
						  clause
						  fns-to-elim
						  ens
						  wrld
						  nil)))
    (cond
     ((null nominations) nil)
     (t
      (let* ((dterm (pick-highest-sum-level-nos nominations wrld nil -1))
             (rule (getprop (ffn-symb dterm) 'eliminate-destructors-rule
                            nil 'current-acl2-world wrld))
             (alist (pairlis$ (fargs (access elim-rule rule :destructor-term))
                              (fargs dterm))))
        (change elim-rule rule
                :hyps (sublis-var-lst alist (access elim-rule rule :hyps))
                :lhs  (sublis-var alist (access elim-rule rule :lhs))
                :rhs  (sublis-var alist (access elim-rule rule :rhs))
                :destructor-term
                (sublis-var alist (access elim-rule rule :destructor-term))
                :destructor-terms
                (sublis-var-lst
                 alist
                 (access elim-rule rule :destructor-terms))))))))

(defun pick-highest-sum-level-nos-hint (nominations wrld ans max-score)
  (declare (xargs :mode :program))
  (cond
   ((null nominations) ans)
   (t (let ((score (sum-level-nos (cdr (car nominations)) wrld)))
        (cond
         ((> score max-score)
          (pick-highest-sum-level-nos-hint (cdr nominations) wrld
					   (list (caar nominations)) score))
	 ((equal score max-score)
	  (pick-highest-sum-level-nos-hint (cdr nominations)
					   wrld
					   (cons (caar nominations) ans)
					   score))
         (t
          (pick-highest-sum-level-nos-hint (cdr nominations) wrld
					   ans max-score)))))))

(defun duplicate-inst-rule (inst-rule inst-rule-list)
  (declare (xargs :mode :program))
  (cond ((null inst-rule-list)
	 nil)
	((equal (access elim-rule inst-rule :destructor-terms)
		(access elim-rule (car inst-rule-list) :destructor-terms))
	 t)
	(t
	 (duplicate-inst-rule inst-rule (cdr inst-rule-list)))))

(defun select-instantiated-elim-rules-hint1 (dterms wrld ans)
  (declare (xargs :mode :program))
    (cond
     ((null dterms) ans)
     (t
      (let* ((dterm (car dterms))
             (rule (getprop (ffn-symb dterm) 'eliminate-destructors-rule
                            nil 'current-acl2-world wrld))
             (alist (pairlis$ (fargs (access elim-rule rule :destructor-term))
                              (fargs dterm)))
	     (inst-rule (change elim-rule rule
				:hyps (sublis-var-lst alist (access elim-rule rule :hyps))
				:lhs  (sublis-var alist (access elim-rule rule :lhs))
				:rhs  (sublis-var alist (access elim-rule rule :rhs))
				:destructor-term
				(sublis-var alist (access elim-rule rule :destructor-term))
				:destructor-terms
				(sublis-var-lst
				 alist
				 (access elim-rule rule :destructor-terms)))))
	  (if (duplicate-inst-rule inst-rule ans)
	      (select-instantiated-elim-rules-hint1 (cdr dterms) wrld ans)
	    (select-instantiated-elim-rules-hint1 (cdr dterms) wrld
						 (cons inst-rule ans)))))))

(defun select-instantiated-elim-rules-hint (clause type-alist eliminables fns-to-elim ens wrld ans)
  (declare (xargs :mode :program))
  (let ((nominations
         (nominate-destructor-candidates-lst-hint clause
						  eliminables
						  type-alist
						  clause
						  fns-to-elim
						  ens
						  wrld
						  nil)))
    (cond
     ((null nominations) nil)
     (t
      (let ((dterms (pick-highest-sum-level-nos-hint nominations wrld nil -1)))
	(select-instantiated-elim-rules-hint1 dterms wrld ans))))))

(defun eliminate-destructors-hint2 (cl eliminables avoid-vars fns-to-elim ens wrld)
  (declare (xargs :mode :program))
  (mv-let
    (contradictionp type-alist ttree)
    (type-alist-clause cl nil t nil ens wrld
                       nil nil)
    (declare (ignore ttree))
    (cond
     (contradictionp
      (mv (list cl) nil nil))
     (t
      (let ((rule (select-instantiated-elim-rule-hint cl type-alist eliminables
						      fns-to-elim ens wrld)))
        (cond ((null rule) (mv (list cl) nil nil))
              (t (mv-let (new-clause elim-vars1 ele)
                   (apply-instantiated-elim-rule rule cl type-alist
                                                 avoid-vars ens wrld)
                   (let ((clauses1 (split-on-assumptions
                                    (access elim-rule rule :hyps)
                                    cl nil)))
                     (cond
                      ((equal new-clause *true-clause*)
                       (mv clauses1 elim-vars1 (list ele)))
                      (t
                       (mv-let (clauses2 elim-vars2 elim-seq)
                         (eliminate-destructors-hint2
                          new-clause
			  (union-eq elim-vars1
				    (remove1-eq
				     (access elim-rule rule :rhs)
				     eliminables))
                          avoid-vars
			  fns-to-elim
                          ens
                          wrld)
                         (mv (conjoin-clause-sets clauses1 clauses2)
                             (union-eq elim-vars1 elim-vars2)
                             (cons ele elim-seq))))))))))))))

(defun eliminate-destructors-hint11 (cl avoid-vars rules type-alist fns-to-elim ens wrld)
  (declare (xargs :mode :program))
  (cond ((null rules) (mv nil nil nil))
              (t (mv-let (clauses-list elim-vars-list elim-seq-list)
		   ;; We gather the clause sets from the rest of the instantiated
		   ;; elim rules.
		   (eliminate-destructors-hint11 cl
						       avoid-vars
						       (cdr rules) type-alist
						       fns-to-elim ens wrld)
		   (let ((rule (car rules)))
		   ;; The first clause set
		   (mv-let (clauses0 elim-vars0 elim-seq0)
		     ;; On with the original show.
		     ;; We are assuming that any choices to be made occur
		     ;; at the very beginning.
		     (mv-let (new-clause elim-vars1 ele)
		       (apply-instantiated-elim-rule rule cl type-alist
						     avoid-vars ens wrld)
		       (let ((clauses1 (split-on-assumptions
                                        (access elim-rule rule :hyps)
                                        cl nil)))
			 (cond
			  ((equal new-clause *true-clause*)
			   (mv clauses1 elim-vars1 (list ele)))
			  (t
			   (mv-let (clauses2 elim-vars2 elim-seq)
			      (eliminate-destructors-hint2
			       new-clause
			       elim-vars1
			       avoid-vars
			       fns-to-elim
			       ens
			       wrld)
			      (mv (conjoin-clause-sets clauses1 clauses2)
				  (union-eq elim-vars1 elim-vars2)
				  (cons ele elim-seq)))))))
		     ;; And we shove the whole mess together into one package.
		     (mv (cons clauses0 clauses-list)
			 (cons elim-vars0 elim-vars-list)
			 (cons elim-seq0 elim-seq-list))))))))

(defun eliminate-destructors-hint1 (cl eliminables avoid-vars fns-to-elim ens wrld)
  (declare (xargs :mode :program))
  (mv-let
    (contradictionp type-alist ttree)
    (type-alist-clause cl nil t nil ens wrld
                       nil nil)
    (declare (ignore ttree))
    (cond
     (contradictionp
      (mv (list cl) nil nil))
     (t
      (let ((rules (select-instantiated-elim-rules-hint cl type-alist eliminables
							fns-to-elim ens wrld nil)))
        (eliminate-destructors-hint11 cl avoid-vars rules type-alist fns-to-elim ens wrld))))))

(defun eliminate-destructors-hint (clause elim-vars fns-to-elim pspv wrld)
  (declare (xargs :mode :program))
  (mv-let (clauses-list elim-vars-list elim-seq-list)
    (eliminate-destructors-hint1 clause
				 ;; Should be:
				 ;;(owned-vars 'eliminate-destructors-clause t
				 ;;            hist)))
				 ;; but we can't modify hist from a computed hint
				 ;; to record this information to later look up.
				 ;; Thus, if one of these (elim-vars) variables
				 ;; gets written away, generalize will not know
				 ;; not to regenerate them and we will think we
				 ;; did and so avoid them.
				 (set-difference-eq
				  (all-vars1-lst clause nil)
				  elim-vars)
				 ;; Similarly, we can confuse generalize.
				 ;;(owned-vars 'eliminate-destructors-clause nil
				 ;;            hist)
				 nil
				 fns-to-elim
				 (access rewrite-constant
					 (access prove-spec-var
						 pspv
						 :rewrite-constant)
					 :current-enabled-structure)
				 wrld)
    (cond (elim-seq-list
           (mv clauses-list elim-vars-list))
          (t
           (mv nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag the-ultimate-clause-processor-ttag)

(defun the-ultimate-clause-processor (cl cl-list)
  (declare (ignore cl)
	   (xargs :guard t))
  cl-list)

(define-trusted-clause-processor
  the-ultimate-clause-processor
  nil
  :ttag the-ultimate-clause-processor-ttag)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(defun crush-elim-vars (elim-vars-list)
  (declare (xargs :guard (true-list-listp elim-vars-list)))
  (if (endp elim-vars-list)
      nil
    (prog2$
     (if (and (consp (car elim-vars-list))
	      (consp (cadr elim-vars-list))
	      (not (equal (car elim-vars-list)
			  (cadr elim-vars-list))))
	 (cw
          "This is bad.  Differing elim-vars found. ~%~x0 and ~x1~%~%"
          (car elim-vars-list)
          (cadr elim-vars-list))
       nil)
     (union-equal (car elim-vars-list)
		  (crush-elim-vars (cdr elim-vars-list))))))

(defun generate-elim-hint (clauses-list)
  (declare (xargs :guard t))
  (if (atom clauses-list)
      nil
    (cons `(:clause-processor
	    (the-ultimate-clause-processor
	     clause
	     ',(car clauses-list)))
	  (generate-elim-hint (cdr clauses-list)))))

(defun arithmetic-default-hint-11 (id clause stable-under-simplificationp
				      hist pspv world last-hint-used elim-vars)
  (declare (xargs :guard (and (consp id)
			      (consp (cdr id))
			      (true-listp (cadr id))
			      (consp pspv)
			      (consp (car pspv))
			      (consp (caar pspv))
			      (consp (cdaar pspv))
			      (consp (car (cdaar pspv)))
			      (consp (caar (cdaar pspv)))
			      (consp (cdaar (cdaar pspv)))
			      (alistp (cddaar (cdaar pspv))))
		  :mode :program))
  (cond	 ;;(first-inductive-subgoal-p id)
   ;;...)
   ((< 10 (len (cadr id)))
    `(:use (:theorem nil)))
   (stable-under-simplificationp
    (cond ((equal last-hint-used nil)
	   (prog2$
	    (observation-cw
             'arithmetic-default-hint-11
             "Branch.")
	    (let ((e/d '(((:REWRITE normalize-factors-gather-exponents)
			(:REWRITE simplify-products-gather-exponents-equal)
			(:REWRITE simplify-products-gather-exponents-<))
		       ((:REWRITE prefer-positive-exponents-scatter-exponents-equal)
			(:REWRITE prefer-positive-exponents-scatter-exponents-<)
			(:rewrite PREFER-POSITIVE-EXPONENTS-SCATTER-EXPONENTS-<-2)
			(:REWRITE |(expt x (+ m n))|)
			(:REWRITE |(expt x (+ m n)) non-zero (+ m n)|)
			(:REWRITE |(expt x (+ m n)) non-zero x|)
			;;(:REWRITE |(expt x (+ m n)) non-pos m and n|)
			;;(:REWRITE |(expt x (+ m n))) non-neg m and n|)
			(:REWRITE normalize-factors-scatter-exponents)
			(:REWRITE simplify-products-scatter-exponents-equal)
			(:REWRITE simplify-products-scatter-exponents-<)))))
	    `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
								     stable-under-simplificationp
								     hist pspv
								     world
								     'check-branch-taken
								     ',elim-vars))
					 :or ((:dynamic-e/d ,e/d
							  :nonlinearp nil)
					      (:nonlinearp t))))))
	  ((equal last-hint-used 'prefer-positive-exponents)
	   (prog2$
	    (observation-cw
             'arithmetic-default-hint-11
             "Prefer-positive-exponents.")
	    `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
								     stable-under-simplificationp
								     hist pspv
								     world
								     'non-linear-arithmetic
								     ',elim-vars))
					 :nonlinearp t)))
	  ((equal last-hint-used 'recycle)
	   (prog2$
	    (observation-cw
             'arithmetic-default-hint-11
             "Recycle.")
	    `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
								     stable-under-simplificationp
								     hist pspv
								     world
								     'non-linear-arithmetic
								     ',elim-vars))
					 :nonlinearp t)))
	  ((equal last-hint-used 'non-linear-arithmetic)
	   (prog2$
	    (observation-cw
             'arithmetic-default-hint-11
             "Settled-down-clause.")
	    (mv-let (clauses-list elim-vars-list)
		    (eliminate-destructors-hint clause elim-vars '(floor mod) pspv world)
		    (if clauses-list
			`(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
										  stable-under-simplificationp
										  hist pspv
										  world
										  'recycle
										  ;; It would be better
										  ;; if we could provide
										  ;; the proper list on
										  ;; each branch, but this
										  ;; is probably good
										  ;; enough.  Do they even
										  ;; differ?
										  ',(union-equal
										     elim-vars
										     (crush-elim-vars
										      elim-vars-list))))
						     :or ,(generate-elim-hint clauses-list))
		      nil))))
	  (t
	   nil)))
   ((equal last-hint-used 'check-branch-taken)
    (let ((branch-taken (branch-taken id)))
      (cond ((equal branch-taken 2)
	     (prog2$
	      (observation-cw
               'arithmetic-default-hint-11
               "Check-branch-taken prefer-positive-exponents.")
	      `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
								       stable-under-simplificationp
								       hist pspv
								       world
								       'prefer-positive-exponents
								       ',elim-vars))
					   :no-op t)))
	    ((equal branch-taken 1)
	     (prog2$
	      (observation-cw
               'arithmetic-default-hint-11
               "Check-branch-taken non-linear-arithmetic.")
	      `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
								       stable-under-simplificationp
								       hist pspv
								       world
								       'recycle
								       ',elim-vars))
					   :nonlinearp nil)))
	    (t
	     (cw "~%~%~ [Note: Computed hint error --- seemingly impossible ~
                  case reached in arithmetic-default-hint-11.  Perhaps there ~
                  are two or more :OR hints interacting in unexpected ways.  ~
                  We do not know what to do here, and so are defaulting to ~
                  doing nothing.~%~%")))))
   ((and (equal last-hint-used 'non-linear-arithmetic)
	 (consp hist)
	 (consp (car hist))
	 (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
    (prog2$
     (observation-cw
      'arithmetic-default-hint-11
      "Non-linear-arithmetic.")
     `(:computed-hint-replacement ((arithmetic-default-hint-11 id clause
							      stable-under-simplificationp
							      hist pspv
							      world
							      'recycle
							      ',elim-vars))
				  :nonlinearp nil)))
   (t
    nil)))
