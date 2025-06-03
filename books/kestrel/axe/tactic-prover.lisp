; The tactic-based prover
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Experimental tool to prove a theorem by applying a series of tactics.

;; See tests in tactic-prover-tests.lisp

;; TODO: Add support for :axe-prover option to call the Axe prover

;; TODO: Add support for embedded DAGs in the inputs (without using the legacy rewriter)

;; See also the provers created by make-prover-simple (they are more
;; lightweight and do not depend on skip-proofs).

(include-book "make-equality-dag-gen")
(include-book "prune-term")
(include-book "rewriter") ; for simp-dag and simplify-terms-repeatedly
;(include-book "dag-size")
(include-book "make-term-into-dag-basic")
;(include-book "equivalent-dags")
(include-book "sweep-and-merge-support")
(include-book "find-probable-facts-simple")
(include-book "tools/prove-dollar" :dir :system)
(include-book "kestrel/arithmetic-light/minus" :dir :system) ; for INTEGERP-OF--
(include-book "kestrel/arithmetic-light/plus" :dir :system) ; for INTEGERP-OF-+
(include-book "kestrel/utilities/system/fresh-names" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/ensure-rules-known" :dir :system)
;(include-book "kestrel/utilities/progn" :dir :system) ; for extend-progn
;(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
;(include-book "kestrel/utilities/real-time-since" :dir :system)
;(include-book "kestrel/bv/bvashr" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced-rules" :dir :system)
(include-book "bv-rules-axe0")
(include-book "bv-rules-axe")
(include-book "bv-array-rules-axe") ; not all are needed, but we need integerp-of-bv-array-read
(include-book "bv-intro-rules")
(include-book "kestrel/bv-lists/bv-array-read-rules" :dir :system) ; for UNSIGNED-BYTE-P-FORCED-OF-BV-ARRAY-READ
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/sbvrem" :dir :system)
(include-book "kestrel/bv/rules" :dir :system) ; for UNSIGNED-BYTE-P-FORCED-OF-BVCHOP, etc?
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/utilities/get-real-time" :dir :system))

(local (in-theory (enable rationalp-when-natp)))

;(local (in-theory (enable member-equal-becomes-memberp))) ;todo

(local (in-theory (disable symbol-listp w)))

;; (defthm pseudo-termp-when-memberp
;;   (implies (and (memberp a y)
;;                 (pseudo-term-listp y))
;;            (pseudo-termp a))
;;   :hints (("Goal" :in-theory (enable pseudo-term-listp MEMBERP))))

;; Returns nil.  May print a warning.
;; could perhaps check someting about the vars, but assumptions might be used to replace terms with new vars.
(defund check-assumption (assumption)
  (declare (xargs :guard (pseudo-termp assumption)))
  (if (variablep assumption)
      (cw "WARNING: Assumption ~x0 is a variable.~%" assumption)
    (if (quotep assumption)
        (cw "WARNING: Assumption ~x0 is a constant.~%" assumption)
      (if (not (all-vars assumption))
          (cw "WARNING: Assumption ~x0 is a ground term.~%" assumption)
        nil))))

;; Returns nil.  May print some warnings.
;; TODO: Can we do others checks to catch the case where the user gives a term instead of a list of terms for the :assumptions?
(defund check-assumptions (assumptions)
  (declare (xargs :guard (pseudo-term-listp assumptions)))
  (if (endp assumptions)
      nil
    (prog2$ (check-assumption (first assumptions))
            (check-assumptions (rest assumptions)))))

;; Returns (mv erp dag-or-quotep assumptions) where dag-or-quotep is boolean-valued.
;todo: redo this to first convert to a dag, then extract hyps and conc from the dag (may blow up but unlikely in practice?)
; TODO: Consider IF when getting assumptions.
;; TODO: Do more type checking between TYPE and the type of the term / top dag node.
;; todo: extract assumptions from dags?
(defun dag-or-term-to-dag-and-assumptions (item wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program ; because this calls translate-term
                  ))
  (if (eq nil item) ;we interpret nil as a term (not an empty dag)
      (mv (erp-nil) *nil* nil)
    (if (weak-dagp item)
        ;; TODO: Add support for getting assumptions out of a DAG that is an
        ;; IMPLIES (but what if they are huge?), in both the :boolean and :bit
        ;; cases.
        (mv (erp-nil) item nil)
      (b* ((term (translate-term item 'dag-or-term-to-dag-and-assumptions wrld))
           ;; TODO: Consider extracting hyps from bit-valued terms:
           ((mv assumptions term)
            (term-hyps-and-conc term))
           ;; Create the DAG for the conclusion:
           ((mv erp dag) (dagify-term term))
           ((when erp) (mv erp nil nil)))
        (mv (erp-nil) dag assumptions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; Proof tactics
;;

;; TODO: Add a tactic for the Axe prover
;; TODO: Add a bit-blasting tactic?
;; TODO: Add case-splitting
;; TODO: What about increasing the timeout and trying again?
(defun tacticp (tac)
  (declare (xargs :guard t))
  (or (member-eq tac '(:rewrite
                       :rewrite-with-precise-contexts
                       :prune
                       :prune-with-rules
                       :acl2
                       :stp
                       :sweep-and-merge))
      (and (consp tac)
           (eq :cases (car tac)))))

(defun tacticsp (tacs)
  (declare (xargs :guard t))
  (if (atom tacs)
      (null tacs)
    (and (tacticp (first tacs))
         (tacticsp (rest tacs)))))

;;
;; Proof Problems
;;

;; A "proof problem" is a DAG to be shown true (non-nil) and a list of assumptions
;; (terms) that can be assumed true (non-nil).
;; TODO: Consider requiring (<= (LEN (CAR PROBLEM)) *max-1d-array-length*).
(defun proof-problemp (prob)
  (declare (xargs :guard t))
  (and (true-listp prob)
       (eql 2 (len prob))
       (pseudo-dag-or-quotep (first prob)) ; TODO: or don't even create a problem if it's a constant
       (pseudo-term-listp (second prob)) ;; todo: disallow constant assumptions? ; todo: do we somewhere handle ground terms and resolvable IFs in assumptions?
       ))

(defthm proof-problemp-forward-to-true-listp
  (implies (proof-problemp prob)
           (true-listp prob))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable proof-problemp))))

(defthm proof-problemp-forward-to-pseudo-dag-or-quotep-of-car
  (implies (proof-problemp prob)
           (pseudo-dag-or-quotep (car prob)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable proof-problemp))))

(defthm proof-problemp-forward-to-pseudo-term-listp-of-cadr
  (implies (proof-problemp prob)
           (pseudo-term-listp (second prob)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable proof-problemp))))

(defun make-problem (dag assumptions)
  (declare (xargs :guard (and (weak-dag-or-quotep dag)
                              (pseudo-term-listp assumptions))))
  (list dag assumptions))

;; Recognize a list of proof problems
(defun proof-problemsp (probs)
  (declare (xargs :guard t))
  (if (atom probs)
      (null probs)
    (and (proof-problemp (first probs))
         (proof-problemsp (rest probs)))))

;; TODO: Where should this go?
(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;;
;; Tactic Results
;;

;; These constants ensure we don't mis-type the keywords:
;(defconst *valid* :valid) ; already defined
;(defconst *invalid* :invalid) ; already defined
;(defconst *error* :error) ; already defined
(defconst *no-change* :no-change)
(defconst *problems* :problems)

;; The result of applying a tactic (a separate piece of "info" may also be returned)
(defund tactic-resultp (x)
  (or (eq x *valid*)
      (eq x *invalid*)
      (eq x *no-change*)
      (eq x *error*)
      (and (consp x)
           (eq *problems* (car x))
           (proof-problemsp (rest x)) ;todo: require non-empty?
           )))

;; A common helper function.  Returns (mv result info state).
(defund make-tactic-result (new-dag old-dag assumptions state)
  (declare (xargs :stobjs state
                  :guard (and (pseudo-dag-or-quotep new-dag)
                              (pseudo-dag-or-quotep old-dag)
                              (pseudo-term-listp assumptions)
                              ;; So we can call equivalent-dags-or-quoteps (todo: relax this?):
                              (< (+ (len new-dag) (len old-dag))
                                 *max-1d-array-length*))))
  (if (quotep new-dag)
      (if (unquote new-dag)
          ;; Rewrote/pruned to a non-nil constant:
          (mv *valid* nil state)
        ;; Rewrote/pruned to nil:
        (mv *invalid*
            :simplified-to-nil ;todo: customize this for each caller?
            state))
    (if (equivalent-dags-or-quoteps old-dag new-dag)
        (mv *no-change* nil state)
      ;; The DAG was changed, so we return one new problem
      (mv `(,*problems* ,(make-problem new-dag assumptions))
          nil
          state))))

(defthm tactic-resultp-of-mv-nth-0-of-make-tactic-result
  (implies (and (pseudo-dag-or-quotep new-dag)
                (pseudo-dag-or-quotep old-dag)
                (pseudo-term-listp assumptions)
                ;; So we can call equivalent-dags-or-quoteps (todo: relax this?):
                (< (+ (len new-dag) (len old-dag))
                   *max-1d-array-length*))
           (tactic-resultp (mv-nth 0 (make-tactic-result new-dag old-dag assumptions state))))
  :hints (("Goal" :in-theory (enable tactic-resultp make-tactic-result))))

;;
;; The :rewrite tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; Could return the rules used as the INFO return value.
(defun apply-tactic-rewrite (problem rule-alist interpreted-function-alist monitor normalize-xors print state)
  (declare (xargs :stobjs state
                  :mode :program ;todo ;because of simp-dag
                  :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (booleanp normalize-xors))))
  (b* ((dag (first problem))
       (assumptions (second problem))
       (- (and print (cw "(Applying the Axe rewriter~%")))
       ((mv erp new-dag state)
        (simp-dag dag ; TODO: Use the basic rewriter (see below) but it will need to support embedded dags (e.g., in popcount-loop)
                  ;; todo: consider :exhaustivep t
                  :rule-alist rule-alist
                  :interpreted-function-alist interpreted-function-alist
                  :monitor monitor
                  :assumptions assumptions
                  :use-internal-contextsp t
                  :normalize-xors normalize-xors
                  :print print
                  :check-inputs nil))
       ;; ((mv erp new-dag limits)
       ;;  (simplify-dag-basic dag
       ;;                      assumptions
       ;;                      rule-alist
       ;;                      interpreted-function-alist
       ;;                      (known-booleans (w state))
       ;;                      normalize-xors
       ;;                      nil ; limits
       ;;                      t ; memoize
       ;;                      nil ; count-hits
       ;;                      print
       ;;                      monitor
       ;;                      nil ; fns-to-elide
       ;;                      ))
       ((when erp) (mv *error* nil state))
       (- (and print (cw "Done applying the Axe rewriter (term size: ~x0, DAG size: ~x1))~%"
                         (dag-or-quotep-size new-dag)
                         (if (quotep new-dag)
                             1
                           (len new-dag))))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :rewrite-with-precise-contexts tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; Could return the rules used as the INFO return value.
;; WARNING: This can blow up for large DAGs, as it (currently) turns the DAG into a term.
(defun apply-tactic-rewrite-with-precise-contexts (problem rule-alist interpreted-function-alist monitor normalize-xors print state)
  (declare (xargs :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitor)
                              (booleanp normalize-xors)
                              (print-levelp print))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (disable myquotep)))))
  (b* ((dag (first problem))
       ((when (quotep dag))
        (if (unquote dag)
            ;; Non-nil constant:
            (prog2$ (cw "Note: The DAG is the constant ~x0.~%" (unquote dag))
                    (mv *valid* nil state))
          ;; The dag is the constant nil:
          (prog2$ (cw "Note: The DAG is the constant NIL.~%")
                  (mv *invalid* nil state))))
       ((when (not (<= (len dag) *max-1d-array-length*)))
        (mv *error* nil state))
       (assumptions (second problem))
       (- (and print (cw "(Applying the Axe rewriter with precise contexts~%")))
       ;; Converting to a term ensures that precise contexts are used.
       ;; WARNING: This can blow up:
       (term (dag-to-term dag))
       ;; Call the rewriter:
       ((mv erp dag-or-quotep)
        (simplify-term-basic term
                             assumptions
                             rule-alist
                             interpreted-function-alist
                             (known-booleans (w state))
                             normalize-xors
                             nil ; limits
                             nil ; memoizep
                             t ; count-hits ; todo: pass in
                             print
                             monitor
                             nil ; fns-to-elide
                             ))
       ((when erp) (mv *error* nil state))
       ((when (quotep dag-or-quotep))
        ;; todo: factor out:
        (let ((val (unquote dag-or-quotep)))
          (if val
              ;; Non-nil constant:
              (prog2$ (cw "Note: The DAG is the non-nil constant ~x0.~%" val)
                      (mv *valid* nil state))
            ;; The dag is the constant nil:
            (prog2$ (cw "Note: The DAG is the constant NIL.~%")
                    (mv *invalid* nil state)))))
       ;; dag-or-quotep is a dag:
       ((when (not (< (+ (len dag-or-quotep) (len dag)) ; so we can check for equivalence later
                      *max-1d-array-length*)))
        (cw "ERROR: Dags too large.")
        (mv *error* nil state))
       (- (and print (cw "Done applying the Axe rewriter wiith contexts (term size: ~x0, DAG size: ~x1))~%"
                         (dag-or-quotep-size dag-or-quotep)
                         (if (quotep dag-or-quotep)
                             1
                           (len dag-or-quotep))))))
    (make-tactic-result dag-or-quotep dag assumptions state)))

;; Sanity check
(local
  (defthm tactic-resultp-of-mv-nth-0-of-apply-tactic-rewrite-with-precise-contexts
    (implies (and (proof-problemp problem)
                  (rule-alistp rule-alist)
                  (interpreted-function-alistp interpreted-function-alist))
             (tactic-resultp (mv-nth 0 (apply-tactic-rewrite-with-precise-contexts problem rule-alist interpreted-function-alist monitor normalize-xors print state))))))

;;
;; The :prune tactic
;;

;; TODO: Deprecate in favor of apply-tactic-prune-with-rules?
;; Prune with no rules.
;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-prune (problem print call-stp-when-pruning state)
  (declare (xargs :guard (and (proof-problemp problem)
                              (print-levelp print)
                              (booleanp call-stp-when-pruning))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (disable pseudo-dag-or-quotep quotep)))))
  (b* ((dag (first problem))
       ((when (quotep dag))
        (if (unquote dag)
            ;; Non-nil constant:
            (prog2$ (cw "Note: The DAG is the constant ~x0.~%" (unquote dag))
                    (mv *valid* nil state))
          ;; The dag is the constant nil:
          (prog2$
           (cw "Note: The DAG is the constant NIL.~%")
           (mv *invalid* nil state))))
       ((when (not (<= (LEN dag) *max-1d-array-length*)))
        (mv *error* nil state))
       (assumptions (second problem))
       (- (and print (cw "(Pruning branches without rules (DAG size: ~x0)~%" (dag-or-quotep-size dag))))
       (term (dag-to-term dag))
       ((mv erp changep term state)
        (prune-term term ; todo: consider calling prune-dag-precisely-with-rule-alist here
                    assumptions
                    (empty-rule-alist) ;no rules (but see :prune-with-rules below)
                    nil                ;no interpreted-fns (todo)
                    nil                ;no point in monitoring anything
                    call-stp-when-pruning ;todo: does it make sense for this to be nil, since we are not rewriting?
                    print
                    state))
       ((when erp) (mv *error* nil state)) ;todo: perhaps add erp to the return signature of this and similar functions (and remove the *error* case from tactic-resultp)
       ((mv erp new-dag)
        (if (not changep)
            (mv (erp-nil) dag)
          (make-term-into-dag-basic term nil)))
       ((when erp) (mv *error* nil state))
       ((when (not (< (+ (len new-dag) (len dag)) ; todo: think about this in the no changep case
                      *max-1d-array-length*)))
        (cw "ERROR: Dags too large.")
        (mv *error* nil state))
       (- (and print (cw "Done pruning branches)~%"))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :prune-with-rules tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-prune-with-rules (problem rule-alist interpreted-function-alist monitor print call-stp-when-pruning state)
  (declare (xargs :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitor)
                              (print-levelp print)
                              (booleanp call-stp-when-pruning))
                  :stobjs state))
  (b* ((dag (first problem))
       ((when (quotep dag))
        (if (unquote dag)
            ;; Non-nil constant:
            (prog2$ (cw "Note: The DAG is the constant ~x0.~%" (unquote dag))
                    (mv *valid* nil state))
          ;; The dag is the constant nil:
          (prog2$ (cw "Note: The DAG is the constant NIL.~%")
                  (mv *invalid* nil state))))
       ((when (not (<= (len dag) *max-1d-array-length*)))
        (mv *error* nil state))
       (assumptions (second problem))
       (- (and print (cw "(Pruning branches with rules (DAG size: ~x0)~%" (dag-or-quotep-size dag))))
       (term (dag-to-term dag))
       ((mv erp changep term state) ; todo: consider calling prune-dag-precisely-with-rule-alist here
        (prune-term term assumptions rule-alist interpreted-function-alist
                    monitor
                    call-stp-when-pruning
                    print
                    state))
       ((when erp) (mv *error* nil state))
       ((mv erp new-dag)
        (if (not changep)
            (mv (erp-nil) dag)
          (make-term-into-dag-basic term nil)))
       ((when erp) (mv *error* nil state))
       ((when (not (< (+ (len new-dag) (len dag))
                      *max-1d-array-length*)))
        (cw "ERROR: Dags too large.")
        (mv *error* nil state))
       (- (and print (cw "Done pruning branches)~%"))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :acl2 tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-acl2 (problem print state)
  (declare (xargs :guard (proof-problemp problem)
                  :stobjs state
                  :mode :program ;; because this calls prove$-fn
                  ))
  (b* ((dag (first problem))
       (assumptions (second problem))
       (term (dag-to-term dag))
       (- (and print (cw "(Calling ACL2 on term ~x0.~%" term)))
       ((mv & provedp state)
        (prove$ ;TODO: Add support for hints
         `(implies (and ,@assumptions) ,term)
         :with-output nil ;confusingly, this turns on output
         )))
    ;; this tactic has to prove the whole term (it can't return a residual DAG)
    (if provedp
        (b* ((- (and print (cw "ACL2 proved the goal.)"))))
          (mv *valid* nil state))
      (b* ((- (and print (cw "ACL2 failed to prove the goal.)"))))
        (mv *no-change* nil state)))))

;;
;; The :stp tactic
;;

;move?
;; Change a counterexample to map variables (not nodenums) to values.
(defund lookup-nodes-in-counterexample (cex dag-array-name dag-array
                                            dag-len ; only used in the guard
                                            )
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (bounded-counterexamplep cex dag-len) ;; all nodenums in the cex should be nodenums of variables
                              )
                  :verify-guards nil ;done below
                  ))
  (if (endp cex)
      nil
    (b* ((entry (first cex))
         (nodenum (car entry))
         (value (cdr entry))
         ;;(expr (aref1 dag-array-name dag-array nodenum))
         (expr (dag-to-term-aux-array dag-array-name dag-array nodenum)) ;; TODO: These should all be vars!
         ((when (not (symbolp expr)))
          (er hard? 'lookup-nodes-in-counterexample "A non-variable, ~x0, is bound in the counterexample." expr)))
      (acons expr value (lookup-nodes-in-counterexample (rest cex) dag-array-name dag-array dag-len)))))

(defthm alistp-of-lookup-nodes-in-counterexample
  (alistp (lookup-nodes-in-counterexample cex dag-array-name dag-array dag-len))
  :hints (("Goal" :in-theory (enable lookup-nodes-in-counterexample))))

(verify-guards lookup-nodes-in-counterexample :hints (("Goal" :in-theory (enable bounded-counterexamplep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ensure-rules-known (pre-stp-rules))

;; so we can get the top nodenum
(local
  (defthm not-<-of-len-and-1-when-pseudo-dagp
    (implies (pseudo-dagp x) (not (< (len x) 1)))))

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; A true counterexample returned in the info is fixed up to bind vars, not nodenums
(defun apply-tactic-stp (problem
                         rule-alist ; do we want this?  it may apply unrelated rules
                         interpreted-function-alist ; do we want this?  maybe it can't hurt
                         monitor normalize-xors print max-conflicts
                         counterexamplep
                         print-cex-as-signedp
                         state)
  (declare (xargs :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitor)
                              (booleanp normalize-xors)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (ilks-plist-worldp (w state)))
                  :guard-hints (("Goal" :in-theory (e/d (symbol-listp-of-pre-stp-rules
                                                         len-when-stp-resultp
                                                         true-listp-when-stp-resultp
                                                         cdr-when-stp-resultp-iff
                                                         <-of-+-of-1-when-integers
                                                         integerp-when-natp
                                                         myquotep-when-pseudo-dag-or-quotep-cheap
                                                         ;; pseudo-dagp-when-pseudo-dag-or-quotep-cheap
                                                         )
                                                        (myquotep quotep ilks-plist-worldp))
                                 :do-not '(generalize eliminate-destructors)))
                  :stobjs state))
  (b* ((dag-or-quotep (first problem))
       (assumptions (second problem))
       ((when (quotep dag-or-quotep))
        (let ((val (unquote dag-or-quotep)))
          (prog2$ (cw "Note: The goal is the constant ~x0.~%" val)
                  (if val
                      ;; Non-nil constant:
                      (mv *valid* nil state)
                  ;; Nil constant:
                  (mv *invalid* nil state)))))
       (dag dag-or-quotep) ; it is in fact a dag
       ;; todo: drop this check (simplify-dag-basic should do it):
       ;; ((when (not (< (car (car dag)) *max-1d-array-length*)))
       ;;  (er hard? 'apply-tactic-stp "DAG too big.")
       ;;  (mv *error* nil state))
       ;; Replace stuff that STP can't handle (todo: push this into the STP translation)?:
       ((mv erp rule-alist) (add-to-rule-alist (pre-stp-rules) rule-alist (w state)))
       ((when erp)
        (er hard? 'apply-tactic-stp "ERROR making pre-stp rule-alist.~%")
        (mv *error* nil state))
       ((mv erp dag-or-quotep & ;limits
            )
        (simplify-dag-basic dag
                            assumptions
                            rule-alist
                            interpreted-function-alist
                            (known-booleans (w state))
                            normalize-xors
                            nil ; limits
                            nil ; memoize
                            nil ; count-hits
                            print
                            monitor ; monitored-symbols
                            nil ; fns-to-elide
                            ))
       ((when erp) (mv *error* nil state))
       ((when (quotep dag-or-quotep))
        (let ((val (unquote dag-or-quotep)))
          (prog2$ (cw "Note: The goal (after applying pre-STP rules) is the constant ~x0.~%" val)
                  (if val
                      ;; Non-nil constant:
                      (mv *valid* nil state)
                    ;; Nil constant:
                    (mv *invalid* nil state)))))
       (dag dag-or-quotep) ; it is in fact a dag
       ;; Prepare to call STP:
       (dag-size (dag-size dag))
       (- (and print (cw "(Applying STP tactic to prove: ~X01.~%" (if (< dag-size 100) (dag-to-term dag) dag) nil)))
       (- (and print (cw "(Using ~x0 assumptions: ~X12.)~%" (len assumptions) assumptions nil)))
       ;; todo: pull out some of this machinery (given a dag and assumptions, set up a disjunction in a dag-array):
       (dag-array-name 'dag-array)
       (dag-array (make-dag-into-array dag-array-name dag 0))
       (top-nodenum (top-nodenum-of-dag dag))
       (dag-len (+ 1 top-nodenum))
       (dag-parent-array-name 'dag-parent-array)
       ((mv dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len))
       ;; Add the assumptions to the DAG (todo: negating these may not be necessary now that prove-disjunction-with-stp can take negated nodenums):
       ((mv erp negated-assumption-nodenum-or-quoteps dag-array dag-len dag-parent-array & &)
        (merge-terms-into-dag-array-simple
         (negate-terms assumptions)
         nil
         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
       ((when erp) (mv *error* nil state))
       ;; Handle any disjuncts that are constants:
       ((mv provedp negated-assumption-nodenums) ; todo: can there really be constants in negated-assumption-nodenum-or-quoteps?
        (handle-constant-disjuncts negated-assumption-nodenum-or-quoteps nil))
       ((when provedp)
        (cw "NOTE: STP tactic proved it due to a assumption of false.)~%") ; balances "(Applying STP tactic"
        (mv *valid* nil state))
       ;; We'll try prove that either the conclusion is true or one of the assumptions is false:
       (disjunct-nodenums (cons top-nodenum negated-assumption-nodenums))
       ((mv result state)
        (prove-disjunction-with-stp disjunct-nodenums ; Disjuncts that represent disjunctions are flattened
                                    dag-array ;must be named 'dag-array (todo generalize?)
                                    dag-len
                                    dag-parent-array ;must be named 'dag-parent-array (todo generalize?)
                                    "TACTIC-QUERY"
                                    print
                                    max-conflicts
                                    counterexamplep
                                    print-cex-as-signedp
                                    state)))
    ;; this tactic has to prove the whole problem (it can't return a residual DAG)
    (if (eq *error* result)
        (prog2$ (er hard? 'apply-tactic-stp "Error applying STP tactic.)~%") ; balances "(Applying STP tactic"
                (mv *error* nil state))
      (if (eq *valid* result)
          (prog2$ (and print (cw "STP tactic proved the goal.)~%")) ; balances "(Applying STP tactic"
                  (mv *valid* nil state))
        (if (eq *invalid* result) ;TODO: Can't happen if we ask for counterexamples?
            (prog2$ (and print (cw "STP tactic said the goal is invalid.)~%")) ; balances "(Applying STP tactic"
                    (mv *no-change* nil state))
          (if (eq *timedout* result)
              (prog2$ (and print (cw "STP tactic timed out.)~%")) ; balances "(Applying STP tactic"
                      (mv *no-change* nil state))
            (if (call-of *counterexample* result)
                (prog2$ (and print (cw "STP tactic returned a counterexample.)~%")) ; balances "(Applying STP tactic"
                        (mv *invalid* ;this is a true counterexample, so give up
                            `(:var-counterexample ,(lookup-nodes-in-counterexample (farg1 result) dag-array-name dag-array dag-len)) ;; return the counterexample in the info
                            state))
              (if (call-of *possible-counterexample* result)
                  (prog2$ (and print (cw "STP tactic returned a possible counterexample.)~%")) ; balances "(Applying STP tactic"
                          (mv *no-change*
                              (append result ;; return the counterexample in the info
                                      (list :dag dag-array :disjuncts disjunct-nodenums))
                              state))
                (prog2$ (er hard? 'apply-tactic-stp "Bad result: ~x0." result)
                        (mv *error* nil state))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;
;; The :cases tactic
;;

;; Returns (mv exhaustivep state)
;; Tries to show that the given CASES are exhaustive, given the ASSUMPTIONS.
(defun prove-cases-exhaustivep (cases assumptions state)
  (declare (xargs :stobjs state
                  :mode :program ; because this calls prove$-fn
                  :guard (and (pseudo-term-listp cases)
                              (pseudo-term-listp assumptions))))
  (b* (((mv & provedp state)
        (prove$ `(implies ,(make-conjunction-from-list assumptions)
                          (or ,@cases))
                :with-output nil ;confusingly, this turns on output
                )))
    (if provedp
        (mv t state)
      (mv nil state))))

(defun split-problem-into-cases-aux (dag assumptions cases)
  (declare (xargs :guard (and (weak-dag-or-quotep dag)
                              (pseudo-term-listp assumptions)
                              (pseudo-term-listp cases))))
  (if (endp cases)
      nil
    (cons (let* ((this-case (first cases))
                 (conjuncts (get-conjuncts-of-term2 this-case)))
            (make-problem dag (union-equal assumptions conjuncts)))
          (split-problem-into-cases-aux dag assumptions (rest cases)))))

(defun split-problem-into-cases (problem cases)
  (declare (xargs :guard (and (proof-problemp problem)
                              (pseudo-term-listp cases))))
  (let* ((dag (first problem))
         (assumptions (second problem)))
    (split-problem-into-cases-aux dag assumptions cases)))

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; TODO: Spawn the exhaustivity obligation as just another thing to prove?
(defun apply-tactic-cases (problem cases print state)
  (declare (xargs :guard (proof-problemp problem)
                  :stobjs state
                  :mode :program ; because this calls translate-terms on the user-supplied CASES
                  ))
  (b* ( ;(dag (first problem))
       (assumptions (second problem))
       (cases (translate-terms cases 'apply-tactic-cases (w state)))
       ((mv exhaustivep state)
        (prove-cases-exhaustivep cases assumptions state))
       ((when (not exhaustivep))
        (prog2$ (cw "Failed to prove that the given cases, ~&0, are exhaustive.)" cases)
                (mv :error ;; todo: think about this
                    nil
                    state)))
       (- (and print (cw "Splitting into ~x0 cases.~%" (len cases))))
       (problems (split-problem-into-cases problem cases)))
    (mv `(,*problems* ,@problems)
        nil
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The :sweep-and-merge-tactic

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; FIXME: Do more than just print them!
(defun apply-tactic-sweep-and-merge (problem
                                     ;;  rule-alist
                                     interpreted-function-alist
                                     ;; monitor
                                     ;; normalize-xors
                                     print state)
  (declare (xargs :guard (and (proof-problemp problem)
                              ;; (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              ;; (booleanp normalize-xors)
                              (print-levelp print))
                  :stobjs state))
  (b* ((dag (first problem))
       ;; Nothing can be done for a constant (TODO: Where should we check for a proof goal of T ?):
       ((when (quotep dag)) (mv *no-change* nil state))
       ((when (< *max-1d-array-length* (len dag))) (er hard? 'apply-tactic-sweep-and-merge "DAG too big.") (mv *no-change* nil state))
       (assumptions (second problem))
       (- (and print (cw "(Applying sweeping and merging~%")))
       ;; Types for the vars in the dag come from the assumptions:
       ;; TODO: Add support for inferred types.
       ;; TODO: Maybe add support for further limiting the values used for testing (e.g., the length of lists):
       (test-case-type-alist (make-var-type-alist-from-hyps assumptions))
       (- (print-probable-facts-for-dag-simple dag :auto test-case-type-alist interpreted-function-alist print))
       ;; ;; Find the probable facts
       ;; ((mv erp & ;; all-passedp ; todo:
       ;;      probably-equal-node-sets
       ;;      & ;; never-used-nodes ; todo: use somehow?
       ;;      probably-constant-node-alist)
       ;;  (find-probable-facts-for-dag-simple dag :auto test-case-type-alist interpreted-function-alist print))
       ;;       ((when erp) (mv *error* nil state))
       ;; (- (and print (cw "Done sweeping and merging (term size: ~x0, DAG size: ~x1))~%"
       ;;                   (dag-or-quotep-size new-dag)
       ;;                   (if (quotep new-dag)
       ;;                       1
       ;;                     (len new-dag)))))
       (- (cw "Done.)")))
    (mv *no-change* nil state) ;(make-tactic-result new-dag dag assumptions state)
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Apply a single tactic, possibly returning a list of remaining problems
;; which, if proved, guarantee that the given problem can be proved.  Returns
;; (mv result info state) where RESULT is a tactic-resultp.
;todo: add more printing
;todo: print message if a tactic has no effect
;todo: print an error if :cases is given followed by no more tactics?
;; We could require the dag-or-quotep in PROBLEM to not be a constant, but I
;; suppose a tactic might complete the proof by finding a contradiction among
;; the assumptions.
(defun apply-proof-tactic (problem tactic rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp state)
  (declare (xargs :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (tacticp tactic)
                              (booleanp call-stp-when-pruning)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (print-levelp print)
                              (booleanp normalize-xors))
                   :stobjs state
                   :mode :program ;; several tactics are in :program mode
                   ))
  (if (eq :rewrite tactic)
      (apply-tactic-rewrite problem rule-alist interpreted-function-alist monitor normalize-xors print state)
    (if (eq :rewrite-with-precise-contexts tactic)
        (apply-tactic-rewrite-with-precise-contexts problem rule-alist interpreted-function-alist monitor normalize-xors print state)
      (if (eq :prune tactic) ;todo: deprecate in favor of :prune-with-rules?
          (apply-tactic-prune problem print call-stp-when-pruning state)
        (if (eq :prune-with-rules tactic)
            (apply-tactic-prune-with-rules problem rule-alist interpreted-function-alist monitor print call-stp-when-pruning state)
          (if (eq :acl2 tactic)
              (apply-tactic-acl2 problem print state)
            (if (eq :stp tactic)
                (apply-tactic-stp problem rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts counterexamplep print-cex-as-signedp state)
              (if (and (consp tactic)
                       (eq :cases (car tactic)))
                  (apply-tactic-cases problem (fargs tactic) print state)
                (if (eq :sweep-and-merge tactic)
                    (apply-tactic-sweep-and-merge problem interpreted-function-alist print state)
                  (prog2$ (er hard 'apply-proof-tactic "Unknown tactic: ~x0." tactic)
                        (mv :error nil state)))))))))))

(defconst *unknown* :unknown)

;; TODO: add an option to make an error in a tactic non-fatal (just try the remaining tactics)?

(mutual-recursion
 ;; Apply the given TACTICS in order, to try to prove the PROBLEM
 ;; (mv result info-acc state), where result is *valid*, *invalid*, *error*, or *unknown*.
 (defun apply-proof-tactics-to-problem (problem tactics rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp info-acc state)
   (declare (xargs :guard (and (proof-problemp problem)
                               (tacticsp tactics)
                               (or (null max-conflicts)
                                   (natp max-conflicts))
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (booleanp call-stp-when-pruning)
                               (booleanp counterexamplep)
                               (booleanp print-cex-as-signedp)
                               (print-levelp print)
                               (booleanp normalize-xors))
                   :stobjs state
                   :mode :program))
   ;; TODO: What if the DAG is a constant?
   (if (endp tactics)
       (let ((dag (first problem)))
         (progn$ (cw "~%FAILED: No more tactics!~%~%")
                 (cw "The DAG is:~%")
                 (print-dag-or-quotep dag)
                 (if (< (dag-or-quotep-size dag) 10000)
                     (cw "~%(Term: ~X01)~%" (dag-to-term dag) nil)
                   nil)
                 (mv *unknown* info-acc state)))
     (b* ((tactic (first tactics))
          ((mv result info state)
           (apply-proof-tactic problem tactic rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp state))
          (info-acc (add-to-end info info-acc)))
       (if (eq *valid* result)
           (prog2$ (and (rest tactics) (cw "(Tactics not used: ~x0)~%" (rest tactics)))
                   (mv *valid* info-acc state))
         (if (eq *invalid* result)
             (mv *invalid* info-acc state)
           (if (eq *error* result)
               (mv *error* info-acc state)
             (if (eq *no-change* result)
                 ;; This tactic did nothing, so try the remaining tactics:
                 (prog2$ (cw "(No change: ~x0.)~%" tactic)
                         (apply-proof-tactics-to-problem problem (rest tactics) rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp info-acc state)
                         )
               ;; This tactic returned one or more subproblems to solve (TODO: What if there are zero subproblems returned -- should return :valid instead..)?
               (if (and (consp result)
                        (eq *problems* (car result)))
                   ;; Apply the rest of the tactics to all the residual problems:
                   (apply-proof-tactics-to-problems 1 (cdr result) (rest tactics) rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp info-acc nil state)
                 (prog2$ (er hard 'apply-proof-tactics-to-problem "Bad tactic result: ~x0." result)
                         (mv *error* nil state))))))))))

 ;; Apply the given TACTICS to try to prove each of the PROBLEMS
 ;; Returns (mv result info-acc state), where result is *valid*, *invalid*, *error*, or *unknown*.
 ;; Returns info about the last problem for each step that has multiple problems.
 (defun apply-proof-tactics-to-problems (num problems tactics rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning
                                             counterexamplep print-cex-as-signedp
                                             info-acc ;includes info for all previous steps, but not other problems in this step
                                             prev-info ; may include info for previous problems in the current step (list of problems)
                                             state)
   (declare (xargs :guard (and (proof-problemsp problems)
                               (tacticsp tactics)
                               (or (null max-conflicts)
                                   (natp max-conflicts))
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (booleanp call-stp-when-pruning)
                               (booleanp counterexamplep)
                               (booleanp print-cex-as-signedp)
                               (print-levelp print)
                               (booleanp normalize-xors))
                   :stobjs state
                   :mode :program))
   (if (endp problems)
       (prog2$ (cw "Finished proving all problems.~%")
               (mv *valid* (add-to-end prev-info info-acc) state))
     (b* ( ;; Try to prove the first problem:
          (- (cw "(Attacking sub-problem ~x0 of ~x1.~%" num (+ num (- (len problems) 1))))
          ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
          ((mv result new-info-acc state)
           (apply-proof-tactics-to-problem (first problems) tactics rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp info-acc state))
          ((mv elapsed state) (real-time-since start-real-time state))
          (new-info (car (last new-info-acc))))
       (if (eq result *valid*)
           (progn$ (cw "Proved problem ~x0 in " num)
                   (print-to-hundredths elapsed)
                   (cw" s.)~%" )
                   (apply-proof-tactics-to-problems (+ 1 num) (rest problems) tactics rule-alist interpreted-function-alist monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp
                                                    info-acc
                                                    new-info ;replaces the prev-info (todo: use it somehow?)
                                                    state))
         (if (eq result *invalid*)
             (prog2$ (cw "Problem ~x0 is invalid.)~%" num)
                     (mv *invalid* (add-to-end new-info info-acc) state))
           (if (eq *error* result)
               (prog2$ (cw "Problem ~x0 gave an error.)~%" num)
                       (mv *error* (add-to-end new-info info-acc) state))
             (if (eq *unknown* result)
                 (prog2$ (cw "Failed to prove problem ~x0.)~%" num)
                         (mv *unknown* (add-to-end new-info info-acc) state))
               (prog2$ (er hard 'apply-proof-tactics-to-problems "Bad result: ~x0." result)
                       (mv *error* nil state))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv result info-acc state), where result is :valid, :invalid, :error, or :unknown.
(defun apply-tactic-prover (dag-or-constant
                            assumptions ; may be untranslated (todo: translate outside)
                            interpreted-fns
                            type ; Either :boolean (try to prove the dag is true) or :bit (try to prove the dag is 1)
                            ;;tests ;a natp indicating how many tests to run
                            tactics
                            rules
                            simplify-assumptionsp
                            ;;types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                            print
                            ;; debug
                            max-conflicts ;a number of conflicts, or nil for no max
                            call-stp-when-pruning
                            counterexamplep
                            print-cex-as-signedp
                            monitor
                            normalize-xors
                            state)
  (declare (xargs :guard (and (or (quotep dag-or-constant)
                                  (pseudo-dagp dag-or-constant))
                              ;; assumptions are untranslated terms
                              (symbol-listp interpreted-fns)
                              (member-eq type '(:bit :boolean))
                              (tacticsp tactics)
                              (symbol-listp rules)
                              (booleanp simplify-assumptionsp)
                              (print-levelp print)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp call-stp-when-pruning)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (symbol-listp monitor)
                              (booleanp normalize-xors))
                  :mode :program
                  :stobjs state))
  (b* ((- (and print (cw "(Applying tactic prover:~%")))
       ;; Check for a constant:
       ((when (quotep dag-or-constant))
        (if (unquote dag-or-constant)
            (prog2$ (cw "NOTE: The goal is the (non-nil) constant ~x0.~%" dag-or-constant)
                    (mv *valid* nil state))
          (prog2$ (cw "NOTE: The goal is the constant NIL.~%")
                  (mv *invalid* nil state))))
       (dag dag-or-constant) ; it was not a constant
       ;; Convert the result type to boolean if needed:
       ((mv erp dag-or-constant)
        (if (eq type :boolean) ; no conversion needed
            (mv (erp-nil) dag)
          ;; If the DAG is bit-valued, we will attempt to prove it is 1:
          (b* (((mv erp dag-or-constant)
                (compose-term-and-dag '(if (equal x '1) 't 'nil) 'x dag))
               ((when erp) (mv erp nil)))
            (mv (erp-nil) dag-or-constant))))
       ((when erp) (mv *error* nil state))
       ;; todo: is a quotep even possible here?
       ((when (quotep dag-or-constant))
        (er hard? 'apply-tactic-prover "Unexpected quotep: ~x0." dag-or-constant)
        (mv *error* nil state))
       (dag dag-or-constant) ; it was not a constant
       ;; Make the rule-alist:
       ((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv *error* nil state))
       ;; (axe-rule-set (make-axe-rules rules state)) ;todo; don't need both of these..
       ;; Print the number of assumptions:
       (- (if (endp assumptions)
              (cw "(No assumptions given.)~%")
            (if (endp (rest assumptions))
                (cw "(1 assumption given.)~%")
              (cw "(~x0 assumptions given.)~%" (len assumptions)))))
       (assumptions (translate-terms assumptions 'apply-tactic-prover (w state))) ;throws an error on bad input
       (- (check-assumptions assumptions)) ; may print some warnings
       ((mv erp assumptions state)
        (if simplify-assumptionsp
            (simplify-terms-repeatedly ;; simplify-terms-using-each-other ; todo: consider simplify-conjunction-basic here
              assumptions rule-alist
              nil ; monitored-rules
              t ; memoizep
              t ; warn-missingp
              state)
          (mv nil assumptions state)))
       ((when erp) (mv *error* nil state))
       ;; TODO: Handle constant assumptions here (and perhaps negated constants)
       (vars (dag-vars dag))
       (- (and print (cw "(Variables in DAG: ~x0)~%" vars)))
       ((mv result info-acc state)
        (apply-proof-tactics-to-problem (make-problem dag assumptions)
                                        tactics
                                        rule-alist
                                        (make-interpreted-function-alist interpreted-fns (w state))
                                        monitor normalize-xors print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp nil state))
       (- (and print (cw "Tactic prover result: ~x0.)~%" result))) ; balances "(Applying tactic prover" above
       )
    (mv result info-acc state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state).
;TODO: erp is a bit of a misnomer; failure to prove isn't necessarily an error..
;TODO: Auto-generate the name
(defun prove-with-tactics-fn (dag-or-term
                              ;tests ;a natp indicating how many tests to run
                              assumptions ;untranslated terms
                              interpreted-fns
                              type
                              tactics
                              rules
                              simplify-assumptions
                              ;types
                              ;test-types
                              name
                              print
                              debug ; whether to refrain from deleting the temp dir containing STP inputs
                              max-conflicts ;a number of conflicts, or nil for no max
                              call-stp-when-pruning
                              counterexamplep
                              print-cex-as-signedp
                              monitor
                              normalize-xors
                              produce-theoremp
                              rule-classes
                              whole-form
                              state)
  (declare (xargs :guard (and (member-eq type '(:boolean :bit))
                              (tacticsp tactics)
                              (symbol-listp rules)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp simplify-assumptions)
                              (booleanp debug)
                              (symbol-listp interpreted-fns)
                              (booleanp call-stp-when-pruning)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (booleanp normalize-xors)
                              (booleanp produce-theoremp))
                  :mode :program
                  :stobjs state))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ;; Check some inputs:
       ((when (not (member-eq type '(:bit :boolean))))
        (er hard 'prove-with-tactics-fn "Illegal value of :type argument: ~x0.  Must be :boolean or :bit." type)
        (mv :bad-input nil state))
       ((when (not (tacticsp tactics)))
        (er hard 'prove-with-tactics-fn "Illegal tactics: ~x0. See TACTICP." tactics)
        (mv :bad-input nil state))
       ;; Form the dag to prove:
       ((mv erp dag-or-constant assumptions2)
        ;; Also translates the term:
        (dag-or-term-to-dag-and-assumptions dag-or-term (w state)))
       ((when erp) (mv :error-translating-input nil state))
       (all-assumptions (append assumptions assumptions2)) ; reorder args?
       ((mv result info-acc state)
        (apply-tactic-prover dag-or-constant
                             all-assumptions
                             interpreted-fns
                             type
                             tactics
                             rules
                             simplify-assumptions
                             print
                             max-conflicts
                             call-stp-when-pruning
                             counterexamplep
                             print-cex-as-signedp
                             monitor
                             normalize-xors
                             state))
       ;; todo: move into apply-tactic-prover?:
       ;; Remove the temp dir unless debug is set:
       (state (if debug state (maybe-remove-temp-dir state))))
    (if (eq result *valid*)
        (b* ((- (cw "Proof of theorem succeeded.~%"))
             (table-event `(table prove-with-tactics-table ',whole-form ',name)) ; just using the name here, since there may be no theorem
             (maybe-theorem
               (and produce-theoremp
                    (b* ((theorem-conclusion (if (< (dag-or-quotep-size dag-or-constant) 1000)
                                                 (if (quotep dag-or-constant) dag-or-constant (dag-to-term dag-or-constant))
                                               (embed-dag-in-term dag-or-constant (w state))))
                         (defthm-name (or name (fresh-name-in-world-with-$s 'prove-with-tactics nil (w state))))
                         (disablep (if rule-classes t nil)) ;can't disable if :rule-classes nil ;todo: make this an option
                         (defthm-variant (if disablep 'defthmd 'defthm)))
                      `(skip-proofs ;todo: have apply-tactic-prover return a theorem and use it to prove this
                         (,defthm-variant ,defthm-name
                           (implies (and ,@assumptions) ;the original assumptions, not translated, no assumptions extracted from the dag
                                    ,theorem-conclusion)
                           :rule-classes ,rule-classes ;todo: suppress if just :rewrite
                           ))))))
          (mv (erp-nil)
              `(progn ,@(and maybe-theorem (list maybe-theorem)) ,table-event (value-triple ',name))
              state))
      (progn$ (cw "Failure info: ~X01." info-acc nil)
              (er hard 'prove-with-tactics-fn "Failed to prove.~%")
              (mv (erp-t) nil state)))))

;todo: add option to suppress generation of the theorem
;; todo: get doc from kestrel-acl2/axe/doc.lisp
(defmacro prove-with-tactics (&whole whole-form
                              dag-or-term ; gets evaluated
                              &key
                              (assumptions 'nil)
                              (interpreted-fns 'nil)
                              (type ':boolean) ;; Indicates whether to try to prove the term is non-nil (:boolean) or 1 (:bit).
                              (tactics ''(:rewrite))
                              (rules 'nil) ;todo: these are for use by the axe rewriter.  think about how to also include acl2 rules here for the :acl2 tactic
                              (simplify-assumptions 'nil) ;todo: consider making t the default
                              (name 'nil) ;the name of the proof, if we care to give it one.  also used for the name of the theorem
                              (print ':brief)
                              (debug 'nil)
                              (max-conflicts '*default-stp-max-conflicts*) ;1000 here broke proofs
                              (call-stp-when-pruning 't)
                              (counterexamplep 't)
                              (print-cex-as-signedp 'nil)
                              (monitor 'nil)
                              (normalize-xors 't)
                              (produce-theorem 'nil)
                              (rule-classes '(:rewrite)))
  `(make-event-quiet
     (prove-with-tactics-fn ,dag-or-term ,assumptions ,interpreted-fns ',type ,tactics ,rules ',simplify-assumptions ,name ',print ,debug ,max-conflicts
                            ,call-stp-when-pruning ,counterexamplep ,print-cex-as-signedp ,monitor
                            ,normalize-xors ',produce-theorem ',rule-classes ',whole-form state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp event state).
;TODO: Auto-generate a better name.
(defun prove-equal-with-tactics-fn (dag-or-term1 ; if a term, may be untranslated
                                    dag-or-term2 ; if a term, may be untranslated
                                    assumptions ; terms, may be untranslated
                                    interpreted-fns
                                    ;; no type arg (always :boolean)
                                    tactics
                                    rules
                                    simplify-assumptions
                                    name ; nil means generate a name
                                    print
                                    debug
                                    max-conflicts
                                    call-stp-when-pruning
                                    counterexamplep
                                    print-cex-as-signedp
                                    monitor
                                    normalize-xors
                                    produce-theoremp
                                    rule-classes
                                    different-vars-ok
                                    whole-form
                                    state)
  (declare (xargs :guard (and (symbol-listp interpreted-fns)
                              (tacticsp tactics)
                              (symbol-listp rules)
                              (booleanp simplify-assumptions)
                              (symbolp name)
                              (print-levelp print)
                              (booleanp debug)
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (booleanp call-stp-when-pruning)
                              (booleanp counterexamplep)
                              (booleanp print-cex-as-signedp)
                              (symbol-listp monitor)
                              (booleanp normalize-xors)
                              (booleanp produce-theoremp)
                              (booleanp different-vars-ok))
                  :mode :program
                  :stobjs state))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ;; Check inputs:
       ((when (not (tacticsp tactics)))
        (er hard 'prove-equal-with-tactics-fn "Illegal tactics: ~x0. See TACTICP." tactics)
        (mv :bad-input nil state))
       ;; Make the equality:
       ((mv erp dag-or-constant) (make-equality-dag-gen dag-or-term1 dag-or-term2 different-vars-ok (w state)))
       ((when erp) (mv erp nil state))
       ;; Do the proof:
       ((mv result info-acc state)
        (apply-tactic-prover dag-or-constant assumptions interpreted-fns :boolean tactics rules
                             simplify-assumptions print max-conflicts call-stp-when-pruning counterexamplep print-cex-as-signedp
                             monitor normalize-xors state))
       ;; Remove the temp dir unless debug is set:
       (state (if debug state (maybe-remove-temp-dir state))))
    (if (eq result *valid*)
        (b* ((- (cw "Proof of equivalence succeeded.~%"))
             (table-event `(table prove-equal-with-tactics-table ',whole-form ',name)) ; just using the name here, since there may be no theorem
             (maybe-theorem
               (and produce-theoremp
                    (b* ((term1 (dag-or-term-to-term dag-or-term1 state)) ; todo: can blow up?
                         (term2 (dag-or-term-to-term dag-or-term2 state)) ; todo: can blow up?
                         (defthm-name (or name (fresh-name-in-world-with-$s 'prove-equal-with-tactics nil (w state))))
                         (disablep (if rule-classes t nil)) ;can't disable if :rule-classes nil ;todo: make this an option
                         (defthm-variant (if disablep 'defthmd 'defthm)))
                      `(skip-proofs ;todo: have apply-tactic-prover return a theorem and use it to prove this
                         (,defthm-variant ,defthm-name
                           (implies (and ,@assumptions)
                                    (equal ,term1
                                           ,term2))
                           :rule-classes ,rule-classes ;todo: suppress if just :rewrite
                           ))))))
          (mv (erp-nil)
              `(progn ,@(and maybe-theorem (list maybe-theorem)) ,table-event (value-triple ',name))
              state))
      (progn$ (cw "Failure info: ~X01." info-acc nil)
              (er hard 'prove-equal-with-tactics-fn "Failed to prove.~%")
              (mv (erp-t) nil state)))))

;todo: add option to suppress generation of the theorem
;; todo: get doc from kestrel-acl2/axe/doc.lisp
(defmacro prove-equal-with-tactics (&whole
                                    whole-form
                                    dag-or-term1 ; gets evaluated
                                    dag-or-term2 ; gets evaluated
                                    &key
                                    ;; Options that affect what is proved:
                                    (assumptions 'nil)
                                    (interpreted-fns 'nil)
                                    ;; no type arg (always :boolean)
                                    ;; Options that affect how the proof goes: ; todo: put the ones that just affect printing last
                                    (tactics ''(:rewrite))
                                    (rules 'nil) ;todo: these are for use by the axe rewriter.  think about how to also include acl2 rules here for the :acl2 tactic
                                    (simplify-assumptions 'nil) ;todo: consider making t the default
                                    (name 'nil) ;the name of the proof, if we care to give it one.  also used for the name of the theorem ; todo: call choose-miter-name
                                    (print ':brief)
                                    (debug 'nil)
                                    (max-conflicts '*default-stp-max-conflicts*)
                                    (call-stp-when-pruning 't)
                                    (counterexamplep 't)
                                    (print-cex-as-signedp 'nil)
                                    (monitor 'nil)
                                    (normalize-xors 't)
                                    (produce-theorem 'nil)
                                    (rule-classes '(:rewrite))
                                    (different-vars-ok 'nil) ; not present in prove-with-tactics
                                    )
  `(make-event-quiet
     (prove-equal-with-tactics-fn ,dag-or-term1 ,dag-or-term2 ,assumptions ,interpreted-fns ,tactics ,rules
                                  ',simplify-assumptions ,name ',print ,debug ,max-conflicts ,call-stp-when-pruning
                                  ,counterexamplep ,print-cex-as-signedp ,monitor ,normalize-xors
                                  ',produce-theorem
                                  ',rule-classes
                                  ',different-vars-ok
                                  ',whole-form
                                  state)))
