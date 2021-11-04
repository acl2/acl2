; The tactic-based prover
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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

(include-book "prune")
(include-book "dag-size")
(include-book "dagify") ;todo
(include-book "tools/prove-dollar" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system)
(include-book "kestrel/utilities/redundancy" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system) ; for extend-progn
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))

(local (in-theory (enable member-equal-becomes-memberp))) ;todo

(defthm pseudo-termp-when-memberp
  (implies (and (memberp a y)
                (pseudo-term-listp y))
           (pseudo-termp a))
  :hints (("Goal" :in-theory (enable pseudo-term-listp MEMBERP))))

(defthm pseudo-term-listp-of-union-equal-2 ;name clash
  (equal (pseudo-term-listp (union-equal x y))
         (and (pseudo-term-listp (true-list-fix x))
              (pseudo-term-listp y)))
  :hints (("Goal" :in-theory (e/d (union-equal pseudo-term-listp)
                                  (pseudo-termp)))))

;;
;; Proof tactics
;;

;; TODO: Add a tactic for the Axe prover
;; TODO: Add a :sweep-and-merge tactic.
;; TODO: Add a bit-blasting tactic?
(defun tacticp (tac)
  (declare (xargs :guard t))
  (or (member-eq tac '(:rewrite :prune :prune-with-rules :acl2 :stp))
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

;; A "proof problem" is a DAG to be shown non-nil and a list of assumptions
;; (terms) that can be assumed non-nil.
(defun proof-problemp (prob)
  (declare (xargs :guard t))
  (and (true-listp prob)
       (eql 2 (len prob))
       (weak-dag-or-quotep (first prob))
       (pseudo-term-listp (second prob))))

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


;; These constants ensure we don't mis-type the keywords:
;(defconst *valid* :valid) ; already defined
;(defconst *invalid* :invalid) ; already defined
;(defconst *error* :error) ; already defined
(defconst *no-change* :no-change)
(defconst *problems* :problems)

;; The result of applying a tactic (a separate piece of "info" may also be returned)
(defun tactic-resultp (x)
  (or (eq x *valid*)
      (eq x *invalid*)
      (eq x *no-change*)
      (eq x *error*)
      (and (consp x)
           (eq *problems* (car x))
           (proof-problemsp (rest x)) ;todo: require non-empty?
           )))

;; A common helper function
(defun make-tactic-result (new-dag old-dag assumptions state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-dag-or-quotep new-dag)
                              (pseudo-dag-or-quotep old-dag)
                              (pseudo-term-listp assumptions)
                              (< (+ (len new-dag) (len old-dag))
                                 2147483646))))
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
          state
         ))))

;;
;; The :rewrite tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; Could return the rules used as the INFO return value.
(defun apply-tactic-rewrite (problem rule-alist monitor simplify-xors print state)
  (declare (xargs :stobjs (state)
                  :mode :program ;todo ;because of simp-dag
                  :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (booleanp simplify-xors))))
  (b* ((dag (first problem))
       (assumptions (second problem))
       (- (and print (cw "(Applying the Axe rewriter~%")))
       ((mv erp new-dag state)
        (simp-dag dag
                  :rule-alist rule-alist
                  :monitor monitor
                  :assumptions assumptions
                  :use-internal-contextsp t
                  :simplify-xorsp simplify-xors
                  :print print
                  :check-inputs nil))
       ((when erp) (mv *error* nil state))
       (- (and print (cw "Done applying the Axe rewriter (term size: ~x0, DAG size: ~x1))~%"
                         (dag-or-quotep-size new-dag)
                         (if (quotep new-dag)
                             1
                           (len new-dag))))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :prune tactic
;;

;; TODO: Deprecate?
;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-prune (problem print call-stp-when-pruning state)
  (declare (xargs :stobjs (state)
                  :mode :program ;todo
                  :guard (and (proof-problemp problem)
                              (booleanp call-stp-when-pruning))))
  (b* ((dag (first problem))
       (assumptions (second problem))
       (- (and print (cw "(Pruning branches without rules (DAG size: ~x0)~%" (dag-or-quotep-size dag))))
       (term (dag-to-term dag))
       ((mv erp term state)
        (prune-term-with-rule-alist term assumptions
                                    (empty-rule-alist) ;no rules (but see :prune-with-rules below)
                                    nil ;no point in monitoring anything
                                    call-stp-when-pruning
                                    state))
       ((when erp) (mv *error* nil state)) ;todo: perhaps add erp to the return signature of this and similar functions (and remove the *error* case from tactic-resultp)
       ((mv erp new-dag) (dagify-term2 term))
       ((when erp) (mv *error* nil state))
       (- (and print (cw "Done pruning branches)~%"))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :prune-with-rules tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-prune-with-rules (problem rule-alist monitor print call-stp-when-pruning state)
  (declare (xargs :stobjs (state)
                  :mode :program ;todo
                  :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (booleanp call-stp-when-pruning))))
  (b* ((dag (first problem))
       (assumptions (second problem))
       (- (and print (cw "(Pruning branches with rules (DAG size: ~x0)~%" (dag-or-quotep-size dag))))
       (term (dag-to-term dag))
       ((mv erp term state)
        (prune-term-with-rule-alist term assumptions rule-alist
                                    monitor
                                    call-stp-when-pruning
                                    state))
       ((when erp) (mv *error* nil state))
       ((mv erp new-dag) (dagify-term2 term))
       ((when erp) (mv *error* nil state))
       (- (and print (cw "Done pruning branches)~%"))))
    (make-tactic-result new-dag dag assumptions state)))

;;
;; The :acl2 tactic
;;

;; Returns (mv result info state) where RESULT is a tactic-resultp.
(defun apply-tactic-acl2 (problem print state)
  (declare (xargs :stobjs (state)
                  :mode :program ;; because this calls prove$-fn
                  :guard (proof-problemp problem)))
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
(defund lookup-nodes-in-counterexample (cex dag-array-name dag-array)
  (declare (xargs :guard (and (counterexamplep cex) ;; all nodenums in the cex should be nodenums of variables
                              (if (consp cex)
                                  (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem (strip-cars cex))))
                                t))
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
      (acons expr value (lookup-nodes-in-counterexample (rest cex) dag-array-name dag-array)))))

(defthm alistp-of-lookup-nodes-in-counterexample
  (alistp (lookup-nodes-in-counterexample cex dag-array-name dag-array))
  :hints (("Goal" :in-theory (enable lookup-nodes-in-counterexample))))

(verify-guards lookup-nodes-in-counterexample)

;; Returns (mv result info state) where RESULT is a tactic-resultp.
;; A true counterexample returned in the info is fixed up to bind vars, not nodenums
(defun apply-tactic-stp (problem print timeout state)
  (declare (xargs :stobjs (state)
;                  :mode :program
                  :guard (proof-problemp problem)
                  :verify-guards nil ;todo: first verify guards for PROVE-DISJUNCTION-WITH-STP
                  ))
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
       (assumptions (second problem))
       (- (and print (cw "(Using ~x0 assumptions: ~X12.~%" (len assumptions) assumptions nil)))
       (dag-size (dag-size dag))
       (- (and print (cw " Calling STP to prove: ~x0.~%" (if (< dag-size 100) (dag-to-term dag) dag))))
       ;; todo: pull out some of this machinery (given a dag and assumptions, set up a disjunction in a dag-array):
       (dag-array-name 'dag-array)
       (dag-array (make-into-array dag-array-name dag))
       (top-nodenum (top-nodenum dag))
       (dag-len (+ 1 top-nodenum))
       (dag-parent-array-name 'dag-parent-array)
       ((mv dag-parent-array dag-constant-alist dag-variable-alist)
        (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len))
       ;; Add the assumptions to the DAG:
       ((mv erp negated-assumption-nodenum-or-quoteps dag-array dag-len dag-parent-array & &)
        (merge-trees-into-dag-array ;inefficient? call a merge-terms... function?
         (negate-terms assumptions)
         nil
         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
         nil ;fixme ifns
         ))
       ((when erp) (mv *error* nil state))
       ;; We'll prove that either the conclusion is true or one of the assumptions is false:
       ;; TODO: What if the top-nodenum is a disjunction?
       ;; TODO: What if a negated assumption is disjunction (e.g., a negated conjuntion)?
       (disjuncts (cons top-nodenum negated-assumption-nodenum-or-quoteps))
       ((mv result state)
        (prove-disjunction-with-stp disjuncts
                                    dag-array ;must be named 'dag-array (fixme generalize?)
                                    dag-len
                                    dag-parent-array ;must be named 'dag-parent-array (fixme generalize?)
                                    "TACTIC-QUERY"
                                    print
                                    timeout
                                    t ;counterexamplep ;todo:;pass in
                                    state)))
    ;; this tactic has to prove the whole problem (it can't return a residual DAG)
    (if (eq *error* result)
        (prog2$ (er hard 'apply-tactic-stp "Error applying STP tactic.)~%")
                (mv *error* nil state))
      (if (eq *valid* result)
          (prog2$ (and print (cw "STP proved the goal.)~%"))
                  (mv *valid* nil state))
        (if (eq *invalid* result) ;TODO: Can't happen if we ask for counterexamples?
            (prog2$ (and print (cw "STP said the goal is invalid.)~%"))
                    (mv *no-change* nil state))
          (if (eq *timedout* result)
              (prog2$ (and print (cw "STP timed out.)~%"))
                      (mv *no-change* nil state))
            (if (call-of *counterexample* result)
                (prog2$ (and print (cw "STP returned a counterexample.)~%"))
                        (mv *invalid* ;this is a true counterexample, so give up
                            `(:var-counterexample ,(lookup-nodes-in-counterexample (farg1 result) dag-array-name dag-array)) ;; return the counterexample in the info
                            state))
              (if (call-of *possible-counterexample* result)
                  (prog2$ (and print (cw "STP returned a possible counterexample.)~%"))
                          (mv *no-change*
                              result ;; return the counterexample in the info
                              state))
                (prog2$ (er hard 'apply-tactic-stp "Bad result: ~x0." result)
                        (mv *error* nil state))))))))))

;;
;; The :cases tactic
;;

;; Returns (mv exhaustivep state)
(defun prove-cases-exhaustivep (cases assumptions state)
  (declare (xargs :stobjs state
                  :mode :program
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
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (proof-problemp problem)))
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

;; Apply a single tactic, possibly returning a list of remaining problems
;; which, if proved, guarantee that the given problem can be proved.  Returns
;; (mv result info state) where RESULT is a tactic-resultp.
;todo: add more printing
;todo: print message if a tactic has no effect
;todo: print an error if :cases is given followed by no more tactics?
(defun apply-proof-tactic (problem tactic rule-alist monitor simplify-xors print timeout call-stp-when-pruning state)
  (declare (xargs :stobjs (state)
                  :mode :program
                  :guard (and (proof-problemp problem)
                              (rule-alistp rule-alist)
                              (tacticp tactic)
                              (booleanp call-stp-when-pruning)
                              (booleanp simplify-xors))))
  (if (eq :rewrite tactic)
      (apply-tactic-rewrite problem rule-alist monitor simplify-xors print state)
    (if (eq :prune tactic) ;todo: deprecate in favor of :prune-with-rules?
        (apply-tactic-prune problem print call-stp-when-pruning state)
      (if (eq :prune-with-rules tactic)
          (apply-tactic-prune-with-rules problem rule-alist monitor print call-stp-when-pruning state)
        (if (eq :acl2 tactic)
            (apply-tactic-acl2 problem print state)
          (if (eq :stp tactic)
              (apply-tactic-stp problem print timeout state)
            (if (and (consp tactic)
                     (eq :cases (car tactic)))
                (apply-tactic-cases problem (fargs tactic) print state)
              (prog2$ (er hard 'apply-proof-tactic "Unknown tactic: ~x0." tactic)
                      (mv :error nil state)))))))))

(defconst *unknown* :unknown)

;; TODO: add an option to make an error in a tactic non-fatal (just try the remaining tactics)?

(mutual-recursion
 ;; Apply the given TACTICS in order, to try to prove the PROBLEM
 ;; (mv result info-acc state), where result is :valid, :invalid, :error, or :unknown.
 (defun apply-proof-tactics-to-problem (problem tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning info-acc state)
   (declare (xargs :stobjs (state)
                   :mode :program
                   :guard (and (or (null timeout)
                                   (natp timeout))
                               (proof-problemp problem)
                               (rule-alistp rule-alist)
                               (tacticsp tactics)
                               (booleanp call-stp-when-pruning)
                               (booleanp simplify-xors))))
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
           (apply-proof-tactic problem tactic rule-alist monitor simplify-xors print timeout call-stp-when-pruning state))
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
                         (apply-proof-tactics-to-problem problem (rest tactics) rule-alist monitor simplify-xors print timeout call-stp-when-pruning info-acc state)
                         )
               ;; This tactic returned one or more subproblems to solve (TODO: What if there are zero subproblems returned -- should return :valid instead..)?
               (if (and (consp result)
                        (eq *problems* (car result)))
                   ;; Apply the rest of the tactics to all the residual problems:
                   (apply-proof-tactics-to-problems 1 (cdr result) (rest tactics) rule-alist monitor simplify-xors print timeout call-stp-when-pruning info-acc nil state)
                 (prog2$ (er hard 'apply-proof-tactics-to-problem "Bad tactic result: ~x0." result)
                         (mv *error* nil state))))))))))

 ;; Apply the given TACTICS to try to prove each of the PROBLEMS
 ;; Returns (mv result info-acc state), where result is :valid, :invalid, :error, or :unknown.
 ;; Returns info about the last problem for each step that has multiple problems.
 (defun apply-proof-tactics-to-problems (num problems tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning
                                             info-acc ;includes info for all previous steps, but not other problems in this step
                                             prev-info ; may include info for previous problems in the current step (list of problems)
                                             state)
   (declare (xargs :stobjs (state)
                   :mode :program
                   :guard (and (or (null timeout)
                                   (natp timeout))
                               (proof-problemsp problems)
                               (rule-alistp rule-alist)
                               (tacticsp tactics)
                               (booleanp call-stp-when-pruning)
                               (booleanp simplify-xors))))
   (if (endp problems)
       (prog2$ (cw "Finished proving all problems.~%")
               (mv *valid* (add-to-end prev-info info-acc) state))
     (b* ( ;; Try to prove the first problem:
          (- (cw "(Attacking sub-problem ~x0 of ~x1.~%" num (+ num (- (len problems) 1))))
          ((mv result new-info-acc state)
           (apply-proof-tactics-to-problem (first problems) tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning info-acc state))
          (new-info (car (last new-info-acc))))
       (if (eq result *valid*)
           (prog2$ (cw "Proved problem ~x0.)~%" num)
                   (apply-proof-tactics-to-problems (+ 1 num) (rest problems) tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning
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

;;
;; prove-with-tactics
;;

;; Returns (mv erp dag-or-quotep assumptions)
;todo: redo this to first convert to a dag, then extract hyps and conc from the dag (may blow up but unlikely in practice?)
; TODO: Consider if
(defun dag-or-term-to-dag-and-assumptions (item type wrld)
  (declare (xargs :mode :program ;why?
                  :guard (member-eq type '(:boolean :bit))))
  (if (eq nil item) ;we interpret nil as a term (not an empty dag)
      (if (eq type :boolean)
          (mv (erp-nil) *nil* nil)
        (prog2$ (er hard? 'dag-or-term-to-dag-and-assumptions "Type is :boolean, but term is nil.")
                (mv (erp-t) nil nil)))
    (if (weak-dagp item)
        ;; TODO: Add support for getting assumptions out of a DAG that is an
        ;; IMPLIES (but what if they are huge?), in both the :boolean and :bit
        ;; cases.
        (if (eq type :boolean)
            (mv (erp-nil) item nil)
          ;; If the DAG is bit-valued, we attempt to prove it is 1:
          (b* (((mv erp dag-or-quotep)
                (compose-term-and-dag '(if (equal x '1) 't 'nil) 'x item))
               ((when erp)
                (mv erp nil nil)))
            (mv (erp-nil) dag-or-quotep nil)))
      (b* ((term (translate-term item 'dag-or-term-to-dag-and-assumptions wrld))
           ;; If the DAG is bit-valued, we attempt to prove it is 1:
           (term (if (eq type :boolean)
                     term
                   `(if (equal ,term '1) 't 'nil)))
           ;; TODO: Consider extracting hyps from bit-valued terms:
           ((mv assumptions term)
            (term-hyps-and-conc term))
           ((mv erp dag) (dagify-term2 term))
           ((when erp) (mv erp nil nil)))
        (mv (erp-nil) dag assumptions)))))

;;Returns (mv result info-acc actual-dag assumptions-given state), where result is :valid, :invalid, :error, or :unknown.
(defun apply-tactic-prover (dag-or-term
                            ;;tests ;a natp indicating how many tests to run
                            tactics
                            assumptions
                            simplify-assumptions
                            ;;types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                            print
                            ;debug
                            timeout ;a number of seconds, or nil for no timeout
                            call-stp-when-pruning
                            rules
                            monitor
                            simplify-xors
                            type
                            state
                            ;;rand
                           )
  (declare (xargs :stobjs (state ;rand
                          )
                  :mode :program
                  :guard (and ;(natp tests) ;TODO: add to guard
                          (or (null timeout)
                              (natp timeout))
                          (booleanp simplify-assumptions)
                          (symbol-listp rules)
                          (booleanp call-stp-when-pruning)
                          (booleanp simplify-xors))))
  (b* (((when (not (tacticsp tactics)))
        (er hard 'prove-with-tactics-fn "Illegal tactics: ~x0. See TACTICP." tactics)
        (mv *error* nil nil nil state))
       ((when (not (member-eq type '(:bit :boolean))))
        (er hard 'prove-with-tactics-fn "Illegal value of :type argument: ~x0. Must be :boolean or :bit." type)
        (mv *error* nil nil nil state))
       ((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv *error* nil nil nil state))
;       (axe-rule-set (make-axe-rules rules state)) ;todo; don't need both of these..
       ;; Print the number of assumptions:
       (- (if (endp assumptions)
              (cw "(No assumptions given.)~%")
            (if (endp (rest assumptions))
                (cw "(1 assumption given.)~%")
              (cw "(~x0 assumptions given.)~%" (len assumptions)))))
       (assumptions (translate-terms assumptions 'prove-with-tactics-fn (w state))) ;throws an error on bad input
       ((mv erp dag assumptions2)
        ;; TODO: Or do we want to leave the assumptions so they can get rewritten?
        ;; Also translates the term:
        (dag-or-term-to-dag-and-assumptions dag-or-term type (w state)))
       ((when erp) (mv *error* nil nil nil state))
       (assumptions (append assumptions assumptions2)) ;TODO: which assumptions / term / dag should be used in the theorem below?
       ((mv erp assumptions state)
        (if simplify-assumptions
            (simplify-terms-using-each-other assumptions rule-alist)
          (mv nil assumptions state)))
       ((when erp) (mv *error* nil nil nil state))
       (vars (merge-sort-symbol< (dag-vars dag)))
       (- (cw "Variables in DAG: ~x0~%" vars))
       ((mv result info-acc state)
        (apply-proof-tactics-to-problem (make-problem dag assumptions)
                                        tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning nil state)))
    ;;todo: returning the dag and assumptions here seems a bit gross:
    (mv result info-acc dag assumptions state)))

;returns (mv erp event state)
;TODO: erp is a bit of a misnomer; failure to prove isn't necessarily an error..
;TODO: Auto-generate the name
;TODO: Build the types from the assumptions or vice versa (types for testing may have additional restrictions to avoid huge inputs)
(defun prove-with-tactics-fn (dag-or-term
                              ;tests ;a natp indicating how many tests to run
                              tactics
                              assumptions ;untranslated terms
                              simplify-assumptions
                              ;types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                              name
                              print
                              debug ; whether to refrain from deleting the temp dir containing STP inputs
                              timeout ;a number of seconds, or nil for no timeout
                              call-stp-when-pruning
                              rules
                              monitor
                              simplify-xors
                              rule-classes
                              type
                              whole-form
                              state
                              ;rand
                             )
  (declare (xargs :stobjs (state ;rand
                          )
                  :mode :program
                  :guard (and ;(natp tests) ;TODO: add to guard
                              (or (null timeout)
                                  (natp timeout))
                              (booleanp simplify-assumptions)
                              (booleanp debug)
                              (symbol-listp rules)
                              (booleanp call-stp-when-pruning)
                              (booleanp simplify-xors))))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       ((mv result info-acc actual-dag assumptions-given state)
        (apply-tactic-prover dag-or-term
                             tactics
                             assumptions
                             simplify-assumptions
                             print
                             timeout
                             call-stp-when-pruning
                             rules
                             monitor
                             simplify-xors
                             type
                             state
                            ))
       (state (if debug
                  state
                (maybe-remove-temp-dir state))))
    (if (eq result *valid*)
        (b* ((- (cw "Proof of theorem succeeded.~%"))
             ;; make the theorem:
             (theorem-conclusion (if (< (dag-or-quotep-size actual-dag) 1000)
                                     (dag-to-term actual-dag)
                                   (embed-dag-in-term actual-dag (w state))))
             (defthm-name (or name (fresh-name-in-world-with-$s 'prove-with-tactics nil (w state))))
             (disablep (if rule-classes t nil)) ;can't disable if :rule-classes nil ;todo: make this an option
             (defthm-variant (if disablep 'defthmd 'defthm))
             (defthm `(skip-proofs ;todo: have apply-proof-tactics-to-problem return a theorem and use it to prove this
                       (,defthm-variant ,defthm-name
                         (implies (and ,@assumptions-given) ;the original assumptions, not translated, no assumptions extracted from the dag
                                  ,theorem-conclusion)
                         :rule-classes ,rule-classes ;todo: suppress if just :rewrite
                         )))
             ;; (- (and types ;todo: remove this restriction
             ;;         (cw "Note: Suppressing theorem because :types are not yet supported when generating theorems.~%")))
             ;; (event (if types
             ;;            '(progn)
             ;;          defthm))
             )
          (mv (erp-nil)
              (extend-progn defthm `(table prove-with-tactics-table ',whole-form ',defthm))
              state))
      (progn$ (cw "Failure info: ~x0." info-acc)
              (er hard 'prove-with-tactics-fn "Failed to prove.~%")
              (mv (erp-t) nil state)))))

;todo: allow :rule-classes
(defmacro prove-with-tactics (&whole whole-form
                              dag-or-term
                              &key
                              ;;(tests '100) ;defaults to 100, 0 is used if :tactic is :rewrite
                              (tactics ''(:rewrite))
                              (assumptions 'nil) ;assumed when rewriting the goal
                              (print ':brief)
                              ;;(types 'nil) ;gives types to the vars so we can generate tests for sweeping
                              (name 'nil) ;the name of the proof if we care to give it one.  also used for the name of the theorem
                              (debug 'nil)
                              (timeout '*default-stp-timeout*) ;1000 here broke proofs
                              (rules 'nil) ;todo: these are for use by the axe rewriter.  think about how to also include acl2 rules here...
                              (monitor 'nil)
                              (simplify-xors 't)
                              (rule-classes '(:rewrite))
                              (call-stp-when-pruning 't)
                              (simplify-assumptions 'nil) ;todo: consider making t the default
                              (type ':boolean) ;; Indicates whether to try to prove the term is non-nil (:boolean) or 1 (:bit).
                              )
  `(make-event (prove-with-tactics-fn ,dag-or-term
                                      ;; ,tests
                                      ,tactics
                                      ,assumptions
                                      ',simplify-assumptions
                                      ;; ,types
                                      ,name
                                      ',print
                                      ,debug
                                      ,timeout
                                      ,call-stp-when-pruning
                                      ,rules
                                      ,monitor
                                      ,simplify-xors
                                      ',rule-classes
                                      ',type
                                      ',whole-form
                                      state ; rand
                                     )))

;;
;; prove-equivalence2
;;

;returns (mv erp event state)
;TODO: Auto-generate the name
;TODO: Build the types from the assumptions or vice versa (types for testing may have additional restrictions to avoid huge inputs)
(defun prove-equivalence2-fn (dag-or-term1
                              dag-or-term2
                              ;tests ;a natp indicating how many tests to run
                              tactics
                              assumptions
                              ;types ;does soundness depend on these or are they just for testing? these seem to be used when calling stp..
                              name
                              print
                              ;debug
                              timeout
                              call-stp-when-pruning
                              rules
                              monitor
                              simplify-xors
                              different-vars-ok
                              whole-form
                              state
                              ;rand
                             )
  (declare (xargs :stobjs (state ;rand
                          )
                  :mode :program
                  :guard (and ;(natp tests) ;TODO: add to guard
                              (or (null timeout)
                                  (natp timeout))
                              (symbol-listp rules)
                              (tacticsp tactics)
                              (booleanp call-stp-when-pruning)
                              (booleanp simplify-xors))))
  (b* (((when (command-is-redundantp whole-form state))
        (mv nil '(value-triple :invisible) state))
       (assumptions (translate-terms assumptions 'prove-equivalence2-fn (w state))) ;throws an error on bad input
       ((mv erp dag1) (dag-or-term-to-dag dag-or-term1 (w state)))
       ((when erp) (mv erp nil state))
       ((mv erp dag2) (dag-or-term-to-dag dag-or-term2 (w state)))
       ((when erp) (mv erp nil state))
       (vars1 (merge-sort-symbol< (dag-vars dag1)))
       (- (cw "Variables in DAG1: ~x0~%" vars1))
       (vars2 (merge-sort-symbol< (dag-vars dag2)))
       (- (cw "Variables in DAG2: ~x0~%" vars2))
       (different-varsp (not (perm vars1 vars2)))
       (- (and different-varsp
               different-vars-ok
               (cw "NOTE: The two dags have different variables.~%")))
       ((when (and different-varsp
                   (not different-vars-ok)))
        (mv (hard-error 'prove-equivalence2-fn "The two dags have different variables." nil)
            nil state ;rand
           ))
       ((mv erp dag) (make-equality-dag dag1 dag2))
       ((when erp) (mv erp nil state))
       ((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv erp nil state))
       ((mv result info-acc state)
        (apply-proof-tactics-to-problem
         (make-problem dag assumptions)
         tactics rule-alist monitor simplify-xors print timeout call-stp-when-pruning nil state))
       (state (maybe-remove-temp-dir state)))
    (if (eq result *valid*)
        (b* ((- (cw "Proof of equivalence succeeded.~%"))
             ;; make the theorem:
             (term1 (dag-or-term-to-term dag-or-term1 state))
             (term2 (dag-or-term-to-term dag-or-term2 state))
             (defthm-name (or name (FRESH-NAME-IN-WORLD-WITH-$S 'prove-equivalence2 nil (w state))))
             (defthm `(skip-proofs ;todo: have prove-miter return a theorem and use it to prove this
                       (defthmd ,defthm-name
                         (implies (and ,@assumptions)
                                  (equal ,term1
                                         ,term2)))))
             ;; (- (and types ;todo: remove this restriction
             ;;         (cw "Note: Suppressing theorem because :types are not yet supported when generating theorems.~%")))
             ;; (event (if types
             ;;            '(progn)
             ;;          defthm))
             )
          (mv (erp-nil)
              (extend-progn defthm `(table prove-equivalence2-table ',whole-form ',defthm))
              state))
      (progn$ (cw "Failure info: ~x0." info-acc)
              (er hard 'prove-equivalence2-fn "Failed to prove.~%")
              (mv (erp-t) nil state)))))

       ;; (tests (if (eq :rewrite tactic)
       ;;            0
       ;;          tests))
       ;; ((mv erp
       ;;      & ; the event is usually an empty progn
       ;;      state rand)
       ;;  (prove-miter dag
       ;;               tests
       ;;               types
       ;;               :name (or name 'main-miter)
       ;;               :timeout timeout
       ;;               :initial-rule-sets (if (eq :auto initial-rule-sets)
       ;;                                      (add-rules-to-rule-sets extra-rules (phased-bv-axe-rule-sets state) state) ;todo: overkill?
       ;;                                    initial-rule-sets) ;todo: add the extra rules here too?
       ;;               :print print
       ;;               :debug debug
       ;;               :assumptions assumptions
       ;;               :monitor monitor
       ;;               :use-context-when-miteringp use-context-when-miteringp))

;todo: allow :rule-classes
(defmacro prove-equivalence2 (&whole whole-form
                              dag-or-term1
                              dag-or-term2
                              &key
                              ;;(tests '100) ;defaults to 100, 0 is used if :tactic is :rewrite
                              (tactics ''(:rewrite))
                              (assumptions 'nil) ;assumed when rewriting the miter
                              (print ':brief)
                              ;;(types 'nil) ;gives types to the vars so we can generate tests for sweeping
                              (name 'nil) ;the name of the miter, if we care to give it one.  also used for the name of the theorem
                              ;;(debug 'nil)
                              (timeout '*default-stp-timeout*)
                              (rules 'nil) ;todo: these are for use by the axe rewriter.  think about how to also include acl2 rules here...
                              (monitor 'nil)
                              (simplify-xors 't)
                              (different-vars-ok 'nil)
                              (call-stp-when-pruning 't)
                              )
  `(make-event (prove-equivalence2-fn ,dag-or-term1
                                      ,dag-or-term2
                                      ;; ,tests
                                      ,tactics
                                      ,assumptions
                                      ;; ,types
                                      ,name
                                      ',print
                                      ;;  ,debug
                                      ,timeout
                                      ,call-stp-when-pruning
                                      ,rules
                                      ,monitor
                                      ,simplify-xors
                                      ',different-vars-ok
                                      ',whole-form
                                      state ; rand
                                     )))
