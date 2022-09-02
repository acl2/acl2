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
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(local (in-theory (disable state-p natp w)))

(defthm bounded-possibly-negated-nodenumsp-when-bounded-contextp
  (implies (bounded-contextp context bound)
           (equal (bounded-possibly-negated-nodenumsp context bound)
                  (not (equal (false-context) context))))
  :hints (("Goal" :in-theory (enable bounded-contextp))))

;move:

;; Checks that DAG is a true-list of pairs of the form (<nodenum> . <bounded-dag-expr>).
(defund bounded-weak-dagp-aux (dag bound)
  (declare (xargs :guard (natp bound)))
  (if (atom dag)
      (null dag)
    (let ((entry (car dag)))
      (and (consp entry)
           (let* ((nodenum (car entry))
                  (expr (cdr entry)))
             (and (natp nodenum)
                  (< nodenum bound)
                  (bounded-dag-exprp nodenum expr)
                  (bounded-weak-dagp-aux (cdr dag) bound)))))))

(defthm weak-dagp-aux-when-bounded-weak-dagp-aux
  (implies (bounded-weak-dagp-aux dag bound) ; free var
           (weak-dagp-aux dag))
  :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux
                                     weak-dagp-aux))))

(defthm bounded-weak-dagp-aux-of-cdr
  (implies (bounded-weak-dagp-aux dag bound)
           (bounded-weak-dagp-aux (cdr dag) bound))
  :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux))))

(defthm bounded-weak-dagp-aux-forward-to-alistp
  (implies (bounded-weak-dagp-aux dag bound)
           (alistp dag))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-weak-dagp-aux alistp))))

(defthm bounded-weak-dagp-aux-when-pseudo-dagp-aux
  (implies (and (pseudo-dagp-aux dag n)
                (< n bound)
                (natp n)
                (natp bound))
           (bounded-weak-dagp-aux dag bound))
  :hints (("Goal" :in-theory (enable pseudo-dagp-aux bounded-weak-dagp-aux))))

(defthm bounded-weak-dagp-aux-of-len-when-pseudo-dagp
  (implies (pseudo-dagp dag)
           (bounded-weak-dagp-aux dag (len dag)))
  :hints (("Goal" :in-theory (enable pseudo-dagp pseudo-dagp-aux bounded-weak-dagp-aux))))


;; When the test of an IF or MYIF can be resolved, the IF/MYIF can be replaced
;; by a call of ID around either its then-branch or its else-branch.  This
;; ensures the resulting DAG is still legal and had no changes in node
;; numbering.  The calls to ID can be removed by a sequent call of the
;; rewriter.
(defun id (x) x)

;; Returns (mv erp result state), where result is :true (meaning non-nil), :false, or :unknown.
;; TODO: Also use rewriting?  See try-to-resolve-node.
(defund try-to-resolve-node-with-stp (nodenum-or-quotep
                                      assumptions
                                      ;; rule-alist interpreted-function-alist monitored-rules call-stp
                                      dag-array ;must be named 'dag-array (todo: generalize?)
                                      dag-len
                                      dag-parent-array ;must be named 'dag-parent-array (todo: generalize?)
                                      base-filename    ;a string
                                      print
                                      max-conflicts ;a number of conflicts, or nil for no max
                                      ;; counterexamplep
                                      state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (or (myquotep nodenum-or-quotep)
                                  (and (natp nodenum-or-quotep)
                                       (< nodenum-or-quotep dag-len)))
                              (bounded-possibly-negated-nodenumsp assumptions dag-len)
                              (stringp base-filename)
                              ;; print
                              (or (null max-conflicts)
                                  (natp max-conflicts)))
                  :stobjs state))
  (b* (((when (consp nodenum-or-quotep)) ; test for quotep
        (if (unquote nodenum-or-quotep)
            (mv (erp-nil) :true state)
          (mv (erp-nil) :false state)))
       (nodenum nodenum-or-quotep)
       (- (cw "(Attempting to resolve test with STP using ~x0 assumptions.~%" (len assumptions)))
       ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first (e.g., by running a test).
       (- (cw "(Attempting to prove test true with STP:~%"))
       ((mv true-result state)
        (prove-node-implication-with-stp assumptions
                                         nodenum
                                         dag-array dag-len dag-parent-array
                                         base-filename print max-conflicts
                                         nil ; counterexamplep
                                         state))
       ((when (eq *error* true-result))
        (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* true-result)) ;; STP proved the test
        (prog2$ (cw "STP proved the test true.))~%")
                (mv (erp-nil) :true state)))
       (- (cw "STP failed to prove the test true.)~%"))
       (- (cw "(Attempting to prove test false with STP:~%"))
       ((mv false-result state)
        (prove-node-implication-with-stp assumptions
                                         `(not ,nodenum)
                                         dag-array dag-len dag-parent-array
                                         base-filename print max-conflicts
                                         nil ;counterexamplep
                                         state
                                         ))
       ((when (eq *error* false-result))
        (prog2$ (er hard? 'try-to-resolve-node-with-stp "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* false-result)) ;; STP proved the negation of the test
        (prog2$ (cw "STP proved the test false.))~%")
                (mv (erp-nil) :false state))))
    (prog2$ (cw "STP did not resolve the test.))~%")
            (mv (erp-nil) :unknown state))))

(defthm w-of-mv-nth-2-of-try-to-resolve-node-with-stp
  (equal (w (mv-nth 2 (try-to-resolve-node-with-stp dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
         (w state))
  :hints (("Goal" :in-theory (enable try-to-resolve-node-with-stp
                                     ;;todo:
                                     prove-node-implication-with-stp
                                     ))))

;; Returns (mv erp dag state).
(defund prune-dag-with-contexts-aux (dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (bounded-dag-parent-arrayp 'dag-parent-array dag-parent-array dag-len)
                              (equal (alen1 'dag-parent-array dag-parent-array)
                                     (alen1 'dag-array dag-array))
                              (bounded-weak-dagp-aux dag dag-len)
                              (bounded-context-arrayp 'context-array context-array dag-len dag-len)
                              ;; print
                              (or (null max-conflicts)
                                  (natp max-conflicts))
                              (alistp dag-acc)
                              )
                  :guard-hints (("Goal" :expand (bounded-weak-dagp-aux dag dag-len)
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (enable pseudo-dagp-aux)))
                  :stobjs state))
  (if (endp dag)
      (mv (erp-nil) (reverse-list dag-acc) state)
    (let* ((entry (first dag))
           (nodenum (car entry))
           (expr (cdr entry)))
      (if (atom expr) ; variable (nothing to do):
          (prune-dag-with-contexts-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)
        (let ((fn (ffn-symb expr)))
          (case fn
            ;; quoted constant (nothing to do):
            (quote (prune-dag-with-contexts-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))
            ((if myif)
             (b* (((when (not (consp (cdr (cdr (dargs expr))))))
                   (mv :bad-if-arity nil state))
                  ;; Get the context for this IF/MYIF node (note that its test node may appear in other contexts too):
                  (context (aref1 'context-array context-array nodenum))
                  ((when (eq (false-context) context))
                   (cw "NOTE: False context encountered for node ~x0 (selecting then-branch).~%" nodenum)
                   (prune-dag-with-contexts-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum `(id ,(darg2 expr)) dag-acc) state))
                  ;; Try to resolve the IF test:
                  ((mv erp result state)
                   (try-to-resolve-node-with-stp (darg1 expr) ; the test of the IF/MYIF
                                                 context      ; the assumptions
                                                 dag-array dag-len dag-parent-array
                                                 "PRUNE" ; todo: improve?
                                                 print
                                                 max-conflicts
                                                 state))
                  ((when erp) (mv erp nil state))
                  ;; We use a wrapper of ID here so as to ensure the node is
                  ;; still legal (not a naked nodenum) and not change the node
                  ;; numbering (calls to ID will later be removed by rewriting):
                  (expr (if (eq result :true)
                            `(id ,(darg2 expr)) ; the IF/MYIF is equal to its then-branch
                          (if (eq result :false)
                              `(id ,(darg3 expr)) ; the IF/MYIF is equal to its else-branch
                            ;; Could not resolve the test:
                            expr))))
               (prune-dag-with-contexts-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state)))
            ;; todo: add support for boolif and bvif?
            (t
             (prune-dag-with-contexts-aux (rest dag) dag-array dag-len dag-parent-array context-array print max-conflicts (acons nodenum expr dag-acc) state))))))))

(defthm w-of-mv-nth-2-of-prune-dag-with-contexts-aux
  (equal (w (mv-nth 2 (prune-dag-with-contexts-aux dag dag-array dag-len dag-parent-array context-array print max-conflicts dag-acc state)))
         (w state))
  :hints (("Goal" :in-theory (enable prune-dag-with-contexts-aux))))

;; Returns (mv erp dag-or-quotep state).
;; Smashes the arrays named 'dag-array, 'temp-dag-array, and 'context-array.
;; todo: may need multiple passes, but watch for loops!
(defund prune-dag-with-contexts (dag
                                 ;; assumptions
                                 ;; rules ; todo: add support for this
                                 ;; interpreted-fns
                                 ;; monitored-rules
                                 ;;call-stp
                                 state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (<= (len dag) 2147483646)
                              ;; (pseudo-term-listp assumptions)
                              ;; (symbol-listp rules)
                              ;; (symbol-listp interpreted-fns)
                              ;; (symbol-listp monitored-rules)
                              ;; (or (booleanp call-stp)
                              ;;     (natp call-stp))
                              (ilks-plist-worldp (w state)))
                  :verify-guards nil ; todo
                  :stobjs state))
  (b* ((- (cw "(Pruning DAG:~%"))
       (context-array (make-full-context-array-for-dag dag))
       (dag-array (make-into-array 'dag-array dag))
       (dag-len (+ 1 (top-nodenum-of-dag dag)))
       (dag-parent-array (make-dag-parent-array-with-name2 dag-len 'dag-array dag-array 'dag-parent-array))
       ((mv erp dag state)
        (prune-dag-with-contexts-aux dag dag-array dag-len dag-parent-array context-array
                                     t         ;print
                                     60000     ;todo max-conflicts
                                     nil       ; dag-acc
                                     state))
       ((when erp) (mv erp nil state))
       ((mv erp rule-alist) (make-rule-alist '(id) ; todo: more rules
                                             (w state)))
       ((when erp) (mv erp nil state))
       ((mv erp dag-or-quotep) (simplify-dag-basic dag
                                                   nil ;assumptions
                                                   nil nil
                                                   rule-alist
                                                   nil
                                                   nil ; print
                                                   nil ; known-booleans
                                                   nil ; monitored-symbols
                                                   nil
                                                   nil))
       ((when erp) (mv erp nil state))
       (- (cw "Done pruning DAG.)~%")))
    (mv (erp-nil) dag-or-quotep state)))
