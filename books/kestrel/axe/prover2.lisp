; More Axe Prover material
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

;; TODO compare this stuff to prover.lisp
;; This book is only used by equivalence-checker.lisp.

(include-book "prover")

(defun default-case-designator () "UNKNOWN") ;make a macro?

(defun axe-prover-args-okay (clause hints)
  (declare (xargs :guard t))
  (and (pseudo-term-listp clause) ;fixme what does the guard of a :program mode function mean?
       (axe-rule-listp (g :rules hints))
       ;;what else should this guard check?
       (symbol-listp (g :runes hints))
       (symbol-listp (g :monitor hints))
       (let ((goal-name-passed-in (g :goal-name hints)))
         (or (equal nil goal-name-passed-in)
             (symbolp goal-name-passed-in)
             (stringp goal-name-passed-in)))))

;; The clause-processor function used in the :clause-processor hint.
;;Allowable keys in HINTS:
;; :rules, whose value is a list of dag rules to be used
;; :runes, whose value is list of runes, which are looked up in the state first and added to :rules
;...more
;pass in :silent or a print arg?  how can we tell the difference between no print arg and a print are of nil?
;;Returns (mv erp cl-list state).
;ffixme this should probably return with erp true in come cases (e.g., can't write stp file) - pass back that information from the subfunctions?
;fixme could use the ctx info for computed hints to get the name of the theorem (and the ID info to get the goal spec)...
(defun axe-prover (clause ; (a list of terms, whose disjunction we are to prove)
                   hints  ; a map (ffixme use an alist?)
                   state)
  (declare (xargs :mode :program
                  :stobjs state
                  ;;does this guard actually get checked? is doing so expensive?
                  :guard (axe-prover-args-okay clause hints)))
  (if (not (axe-prover-args-okay clause hints))
      (prog2$ (hard-error 'axe-prover "Bad inputs.  clause: ~x0.  hints: ~x1." (acons #\0 clause (acons #\1 hints nil)))
              (mv (erp-t) (list clause) state))
    (b* ( ;(state (make-temp-dir state)) ;maybe delay until needed?
         ;;(supplied-id (g :id hints))
         ;;(goal-spec (if supplied-id (string-for-tilde-@-clause-id-phrase supplied-id) "unknown"))
;           (unroll (g :unroll hints))         ;format?
         (runes-passed-in (g :runes hints)) ;slow to make the alist out of these?
         (rules-passed-in (g :rules hints)) ;slow to make the alist out of these?
         (rule-alist-passed-in (g :rule-alist hints))
;(extra-stuff (g :extra-stuff hints))
;           (test-cases (g :test-cases hints))
         (print (g :print hints))
         (timeout (g :timeout hints))
         (monitored-symbols (g :monitor hints))
         (interpreted-function-alist (g :interpreted-function-alist hints))
         (goal-name-passed-in (g :goal-name hints)) ;should be a string or symbol (or nil)
         (goal-name (if goal-name-passed-in
                        (if (symbolp goal-name-passed-in)
                            (symbol-name goal-name-passed-in)
                          goal-name-passed-in)
                      (default-case-designator)))
         (- (cw "(Starting DAG prover for:~% ~s0.~%" goal-name))
;           (analyzed-function-table-passed-in (g :analyzed-function-table hints))
;           (analyzed-function-table (or analyzed-function-table-passed-in (empty-analyzed-function-table)))
         (- (progn$ ; (cw "Test case count: ~x0.~%" (len test-cases))
;(and test-cases (cw "First Test case: ~x0.~%" (car test-cases)))
             (and (eq :verbose print) (cw "Using extra runes ~x0.~%" runes-passed-in))
;                           (cw "Unroll ~x0.~%" unroll)
             nil ;(cw "Using extra rules ~x0.~%" (rule-name-list rules-passed-in))
             (cw "Print: ~x0.~%" print)
             (cw "Monitored symbols: ~x0.~%" monitored-symbols)))

;yuck:
;           (prover-rules (append (make-axe-rules runes-passed-in state) rules-passed-in))
         ;;also sorts rules by priority:
         (rule-alist ;(make-rule-alist runes-passed-in rules-passed-in
;                t ;whether to remove duplicate rules ;make this an option?
;               state)
          ;; todo: just use plain make-axe-rules here
          (extend-rule-alist (append rules-passed-in (make-axe-rules! runes-passed-in (w state))) ;pass in an acc
                             t
                             (table-alist 'axe-rule-priorities-table (w state))
                             rule-alist-passed-in))
         (- (cw "~x0 total rules~%" (rule-count-in-rule-alist rule-alist)))
         ;;  merge all literals into one big dag:
         ((mv erp literal-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
          (make-terms-into-dag-array clause
                                     'dag-array ;fffixme use a different array name?
                                     'dag-parent-array ;fffixme use a different array name?
                                     interpreted-function-alist))
         ((when erp) (mv erp (list clause) state))
         ;;Process the clause by trying to prove the disjunction of LITERAL-TERMS
         ;;should this return an updated rule-alist?
         (- (and (eq print :verbose) (cw "Initial literals: ~x0. Initial DAG:~%" literal-nodenums-or-quoteps)))
         (- (and (eq print :verbose) (print-array2 'dag-array dag-array dag-len)))
         ((mv erp result & & & & & ;; dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
              info tries state)
          (prove-disjunction-with-axe-prover literal-nodenums-or-quoteps
                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                        (list rule-alist)
                                        interpreted-function-alist
                                        monitored-symbols
                                        print
                                        goal-name
                                        timeout
                                        t ;print-timeout-goalp
                                        t ;work-hard..
                                        (and print (empty-info-world))
                                        (and print (zero-tries))
                                        0                  ;prover-depth
                                        nil                ;options
                                        (+ -1 (expt 2 59)) ;max fixnum?
                                        state))
         ((when erp) (mv erp (list clause) state))
         (- (and print (cw "(~x0 tries.)~%" tries)))
         (- (and print (print-hit-counts print info (rules-from-rule-alist rule-alist)))))
      (if (eq :proved result)
          (prog2$ (cw "!! The DAG prover proved the clause)~%")
                  ;;fixme very cryptic error message when we only returned the one value
                  (mv (erp-nil)
                      (list (list *t*)) ;the clause-list containing the single clause t
                      ;;fffixme try an empty list of clauses
                      state))
        ;;failed or timed out:
        (prog2$ (cw "!! The Axe prover FAILED to prove the clause)~%")
                (mv (erp-nil)
                    ;;the clause processor didn't do anything:
                    (list clause) ;the clause list containing the original clause
                    state))))))

;; TODO: Think about what it would take to verify the clause processor.  We
;; might need meta-extract.  And the fact that it calls STP would be a problem.
;; Also, the code would need to be put into :logic mode.

(define-trusted-clause-processor
  axe-prover
  nil ;ffixme do i need to include all supporting function names here?
  :ttag axe-prover)
