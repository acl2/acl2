; Pruning irrelevant IF-branches in a DAG
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This utility tries to resolve IF/MYIF/BOOLIF/BVIF tests in the dag, using STP and the contexts of the nodes.

;; TODO: Flesh this out

(include-book "prove-with-stp")
(include-book "rewriter-basic")

;; When the test of an IF or MYIF can be resolved, the IF/MYIF can be replaced
;; by a call of ID around either its then-branch or its else-branch.  This
;; ensures the resulting DAG is still legal and had no changes in node
;; numbering.  The calls to ID can be removed by a sequent call of the
;; rewriter.
(defun id (x) x)

;; todo: update:
;; (defund try-to-resolve-node-with-stp (test-nodenum
;;                                       assumptions
;;                                       equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
;;   (declare (xargs :guard (and (pseudo-termp test)
;;                               (pseudo-term-listp assumptions)
;;                               (pseudo-term-listp equality-assumptions)
;;                               (symbol-listp monitored-rules)
;;                               (rule-alistp rule-alist)
;;                               (interpreted-function-alistp interpreted-function-alist)
;;                               (or (booleanp call-stp)
;;                                   (natp call-stp)))
;;                   :stobjs state))
;;   (b* ((- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptions.~%" (len assumptions) (len equality-assumptions)))
;;        ;; First apply the Axe Rewriter to the test:
;;        (- (cw "(Simplifying test.~%"))
;;        ;; TODO: Consider first doing something faster than a DAG-producing
;;        ;; rewrite, such as evaluating ground terms, using assumptions, and
;;        ;; applying rules that don't expand the term size too much.
;;        ((mv erp simplified-dag-or-quotep)
;;         (simplify-term-basic test
;;                              assumptions ;no equality assumptions here to prevent loops (todo: think about this)
;;                              rule-alist
;;                              interpreted-function-alist
;;                              monitored-rules
;;                              nil ; memoizep
;;                              nil ; count-hits
;;                              nil ; print
;;                              nil ; normalize-xors
;;                              (w state)))
;;        ((when erp)
;;         (cw "ERROR simplifying test.))~%")
;;         (mv erp nil state))
;;        ((when (quotep simplified-dag-or-quotep))
;;         ;; Resolved the test via rewriting:
;;         (cw "Simplified to the constant ~x0.))~%" simplified-dag-or-quotep)
;;         (if (unquote simplified-dag-or-quotep)
;;             (mv nil :true state)
;;           (mv nil :false state)))
;;        ;; Test did not rewrite to a constant, so try other things:
;;        ;; (- (cw "(Simplified to ~X01.)~%" simplified-dag-or-quotep nil))
;;        (- (cw "Test did not simplify to a constant.)~%"))
;;        ;; Is this needed, given that we simplified the test above using the assumptions?
;;        ;; TODO: Also look for an equality in the other order?:
;;        ((when (or (member-equal test assumptions)
;;                   (member-equal test equality-assumptions))) ;; In case the test is not a known boolean (so rewriting can't rewrite it to t). ;todo: use simplified-test-term here?
;;         (cw "(The test is a known assumption.))") ; todo: look for negated assumptions too
;;         (mv nil :true state)) ;a test that's in the assumptions is like a test that rewrites to t
;;        ;; TODO: What if the test is equal to an assumption but not identical to it (e.g., a disjunction with the disjuncts reordered?)
;;        ((when (not call-stp))
;;         (cw "Failed to resolve test by rewriting and we have been told not to call STP.)")
;;         (mv nil :unknown state)) ; give up if we are not allowed to call STP
;;        ;; TODO: Avoid turning the DAG into a term:
;;        (simplified-test-term (dag-to-term simplified-dag-or-quotep)) ;TODO: check that this is not huge (I suppose it could be if something gets unrolled)
;;        ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first (e.g., by running a test).
;;        (- (cw "(Attempting to prove test true with STP:~%"))
;;        ((mv true-result state)
;;         (prove-implication-with-stp simplified-test-term
;;                                     assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
;;                                     nil         ;counterexamplep
;;                                     (if (natp call-stp) call-stp *default-stp-max-conflicts*)
;;                                     nil                ;print
;;                                     "PRUNE-PROVE-TRUE" ;todo: do better?
;;                                     state))
;;        ((when (eq *error* true-result))
;;         (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
;;                 (mv :error-calling-stp :unknown state)))
;;        ((when (eq *valid* true-result)) ;; STP proved the test
;;         (prog2$ (cw "STP proved the test true.))~%")
;;                 (mv nil :true state)))
;;        (- (cw "STP failed to prove the test true.)~%"))
;;        (- (cw "(Attempting to prove test false with STP:~%"))
;;        ((mv false-result state)
;;         (prove-implication-with-stp `(not ,simplified-test-term)
;;                                     assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
;;                                     nil         ;counterexamplep
;;                                     (if (natp call-stp) call-stp *default-stp-max-conflicts*)
;;                                     nil                 ;print
;;                                     "PRUNE-PROVE-FALSE" ;todo: do better?
;;                                     state))
;;        ((when (eq *error* false-result))
;;         (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
;;                 (mv :error-calling-stp :unknown state)))
;;        ((when (eq *valid* false-result)) ;; STP proved the negation of the test
;;         (prog2$ (cw "STP proved the test false.))~%")
;;                 (mv nil :false state))))
;;     (prog2$ (cw "STP did not resolve the test.))~%")
;;             (mv nil :unknown state))))

;; (defun prune-dag-with-contexts-aux (dag dag-len dag-array context-array dag-acc state)
;;   (declare (xargs :guard (and (weak-dagp-aux dag dag)
;;                               (natp dag-len)
;;                               (context-arrayp 'context-array context-array dag-len))
;;                   :stobjs state))
;;   (if (endp dag)
;;       (reverse-list dag-acc)
;;     (let* ((entry (first dag))
;;            (nodenum (car entry))
;;            (expr (cdr entry)))
;;       (if (atom expr)
;;           (prune-dag-with-contexts-aux (rest dag) dag-len dag-array context-array (cons expr dag-acc) state)
;;         (let ((fn (ffn-symb expr)))
;;           (case fn
;;             (quote (prune-dag-with-contexts-aux (rest dag) dag-len dag-array context-array (cons expr dag-acc) state))
;;             ((if myif)
;;              (b* ((context (aref1 'context-array context-array nodenum))
;;                   ;; try to prove and disprove
;;                   ((mv result state) (prove-disjunction-with-stp
;;                                       ...
;;                                       disjuncts
;;                                     dag-array ;must be named 'dag-array (todo: generalize?)
;;                                     dag-len
;;                                     dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
;;                                     base-filename    ;a string
;;                                     print
;;                                     max-conflicts ;a number of conflicts, or nil for no max
;;                                     counterexamplep ;perhaps this should always be t?
;;                                     state)

;;             ;; todo: boolif and bvif?
;;             (t
;;              (prune-dag-with-contexts-aux (rest dag) dag-len context-array (cons expr dag-acc) state))))))))


;; ;; Returns (mv erp dag-or-quotep).
;; ;; Smashes the arrays named 'dag-array, 'temp-dag-array, and 'context-array.
;; ;; todo: may need multiple passes, but watch for loops!
;; (defund prune-dag-with-contexts (dag
;;                                  ;; assumptions
;;                                  ;; rules ; todo: add support for this
;;                                  ;; interpreted-fns
;;                                  ;; monitored-rules
;;                                  call-stp
;;                                  state)
;;   (declare (xargs :guard (and (pseudo-dagp dag)
;;                               ;; (pseudo-term-listp assumptions)
;;                               ;; (symbol-listp rules)
;;                               ;; (symbol-listp interpreted-fns)
;;                               ;; (symbol-listp monitored-rules)
;;                               (or (booleanp call-stp)
;;                                   (natp call-stp))
;;                               (ilks-plist-worldp (w state)))
;;                    :stobjs state))
;;   (b ((context-array (make-full-context-array-for-dag dag))
;;       (dag-array (make-into-array 'dag-array dag))
;;       (dag (prune-dag-with-contexts-aux dag dag-array context-array state))
;;       ((mv erp rule-alist) (make-rule-alist rules (w state)))
;;       ((when erp) (mv erp nil))
;;       ((mv erp dag-or-quotep) (simplify-dag-basic dag
;;                                                   nil ;assumptions
;;                                                   nil nil
;;                                                   rule-alist
;;                                                   nil
;;                                                   nil ; print
;;                                                   nil ; known-booleans
;;                                                   nil ; monitored-symbols
;;                                                   nil
;;                                                   nil))
;;       ((when erp) (mv erp nil)))
;;      (mv (erp-nil) dag-or-quotep)))
