; Pruning irrelevant IF-branches
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

;; Prune irrelevant if-then-else branches in terms and DAGs using rewriting and calls to STP.

;; TODO: Use counterexamples returned by STP to avoid later calls that will fail.

;; TODO: Use the basic-rewriter here?

(include-book "rewriter") ;because we call simplify-term (an Axe rewriter function)
(include-book "dag-size-fast")
(include-book "kestrel/utilities/subtermp" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(in-theory (disable table-alist)) ;why?

;; Fixup assumption when it will obviously loop when used as a directed equality.
;; could check for (equal <constant> <x>) here too, but Axe may be smart enough to reorient that
;; Returns a possibly-empty list
(defund fixup-assumption (assumption)
  (declare (xargs :guard (pseudo-termp assumption)))
  (if (not (and (consp assumption)
                (eq 'equal (ffn-symb assumption))
                (eql 2 (len (fargs assumption))) ;for guards
                ))
      (list assumption)
    (if (subtermp (farg1 assumption) (farg2 assumption))
        (prog2$ (cw "Note: re-orienting equality assumption ~x0.~%" assumption)
                `((equal ,(farg2 assumption) ,(farg1 assumption))))
      (if (quotep (farg1 assumption))
          (list assumption)
        (if (quotep (farg2 assumption))
            `((equal ,(farg1 assumption) ,(farg2 assumption)))
          (prog2$ (cw "Note: Dropping equality assumption ~x0.~%" assumption)
                  nil))))))

(defthm pseudo-term-listp-of-fixup-assumption
  (implies (pseudo-termp assumption)
           (pseudo-term-listp (fixup-assumption assumption)))
  :hints (("Goal" :in-theory (enable fixup-assumption))))

;; Reorder equalities that obviously loop (because a term is equated to a
;; superterm).  TODO: Perform a more thorough analysis of possible looping.
(defund fixup-assumptions (assumptions)
  (declare (xargs :guard (pseudo-term-listp assumptions)))
  (if (endp assumptions)
      nil
    (union-equal (fixup-assumption (first assumptions))
                 (fixup-assumptions (rest assumptions)))))

(defthm pseudo-term-listp-of-fixup-assumptions
  (implies (pseudo-term-listp assumptions)
           (pseudo-term-listp (fixup-assumptions assumptions)))
  :hints (("Goal" :in-theory (enable fixup-assumptions))))

(defund get-equalities (assumptions)
  (declare (xargs :guard (pseudo-term-listp assumptions)))
  (if (endp assumptions)
      nil
    (let ((assumption (first assumptions)))
      (if (call-of 'equal assumption)
          (cons assumption (get-equalities (rest assumptions)))
        (get-equalities (rest assumptions))))))

(defthm pseudo-term-listp-of-get-equalities
  (implies (pseudo-term-listp assumptions)
           (pseudo-term-listp (get-equalities assumptions)))
  :hints (("Goal" :in-theory (enable get-equalities))))

(defttag invariant-risk)
(set-register-invariant-risk nil) ;potentially dangerous but needed for execution speed

;; Returns  (mv erp result state) where RESULT is :true, :false, or :unknown
;; TODO: If this can show the test must be both true and false (because the assumptions contradict), then the entire if/myif/bvif may be irrelevant.
;; TODO: What if the test rewrote to a constant other than t or nil?
(defun try-to-resolve-test (test assumptions equality-assumptions rule-alist monitored-rules call-stp state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp test)
                              (pseudo-term-listp assumptions)
                              (pseudo-term-listp equality-assumptions)
                              (symbol-listp monitored-rules)
                              (rule-alistp rule-alist)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :mode :program ;because this calls the rewriter
                  ))
  (b* ( ;; First apply the Axe rewriter to the test:
       (- (cw "(Simplifying test.~%"))
       ((mv erp simplified-test state)
        (simp-term test ;; TODO: Does this use contexts?
                   :rule-alist rule-alist
                   :monitor monitored-rules
                   :assumptions assumptions ;no equality assumptions here to prevent loops (todo: think about this)
                   :check-inputs nil))
       ((when erp)
        (mv erp nil state)))
    (if (equal *t* simplified-test) ;todo: allow any non-nil constant?
        (prog2$ (cw "Simplified to t.)~%")
                (mv nil :true state))
      (if (equal *nil* simplified-test)
          (prog2$ (cw "Simplified to nil.)~%")
                  (mv nil :false state))
        ;; Test did not rewrite to t or nil, so try other things:
        (b* ((- (cw "Did not simplify to t or nil)~%"))
             ((when (or (member-equal test assumptions)
                        (member-equal test equality-assumptions))) ;; In case the test is not a known boolean (so rewriting can't rewrite it to t). ;todo: use simplified-test-term here?
              (prog2$ (cw "(The test is a known assumption.)")
                      (mv nil :true state))) ;a test that's in the assumptions is like a test that rewrites to t
             ;; TODO: What if the test is equal to an assumption but not identical to it (e.g., a disjunction with the disjuncts reordered?)
             (simplified-test-term (dag-to-term simplified-test)) ;TODO: check that this is not huge (I supposed it could be if something gets unrolled)
             ((when (not call-stp))
              (mv nil :unknown state))
             (- (cw "(Attempting to prove test true:~%"))
             ((mv true-result state)
              (prove-implication-with-stp simplified-test-term
                                          assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
                                          nil ;counterexamplep
                                          *default-stp-max-conflicts*
                                          nil                ;print
                                          "PRUNE-PROVE-TRUE" ;todo: do better?
                                          state))
             ((when (eq *error* true-result))
              (prog2$ (er hard 'try-to-resolve-test "Error calling STP")
                      (mv :error-calling-stp :unknown state)))
             (- (cw "Done attempting to prove test true.)~%")) ;todo: improve this printing once we don't try both true and false
             ;;todo: eventually skip this if the call above proves that the test is true
             (- (cw "(Attempting to prove test false:~%"))
             ((mv false-result state)
              (prove-implication-with-stp `(not ,simplified-test-term)
                                          assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
                                          nil ;counterexamplep
                                          (if (natp call-stp) call-stp *default-stp-max-conflicts*)
                                          nil                 ;print
                                          "PRUNE-PROVE-FALSE" ;todo: do better?
                                          state))
             ((when (eq *error* false-result))
              (prog2$ (er hard 'try-to-resolve-test "Error calling STP")
                      (mv :error-calling-stp :unknown state)))
             (- (cw "Done attempting to prove test false.)~%"))
             ;;todo: remove this check eventually, once we see it never being triggered (but perhaps the assumptions contradict!):
             ((when (and (eq *valid* true-result)
                         (eq *valid* false-result)))
              (progn$ (cw "Test for warning below: ~x0~%" test)
                      (cw "Assumptions for warning below: ~x0~%" assumptions)
                      (cw "Equality ssumptions for warning below: ~x0~%" equality-assumptions)
                      (cw "WARNING: STP proved the test both true and false (see details above)!  This may indicate that the assumptions contradict.")
                      ;; Arbitrarily picking :true here for now:
                      (mv nil :true state))))
          (if (eq *valid* true-result) ;; STP proved the test
              (prog2$ (cw "(STP resolved the test to true.)~%")
                      (mv nil :true state))
            (if (eq *valid* false-result) ;; STP proved the negation of the test
                (prog2$ (cw "(STP resolved the test to false.)~%")
                        (mv nil :false state))
              (prog2$ (cw "(STP did not resolve the test.)~%")
                      (mv nil :unknown state)))))))))

;; TODO: Thread through a print option
(mutual-recursion
 ;; Returns (mv erp result-term state) where RESULT-TERM is equal
 ;; to TERM. Tries to rewrite each myif test using context from all overarching
 ;; tests (and any given assumptions).
;TODO: Add an IFF flag and, if set, turn (if x t nil) into x and (if x nil t) into (not x)
 (defun prune-term (term assumptions equality-assumptions rule-alist monitored-rules call-stp state)
   (declare (xargs :stobjs (state)
                   :guard (and (pseudo-termp term)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions) ;used only for looking up conditions
                               (symbol-listp monitored-rules)
                               (rule-alistp rule-alist)
                               (or (member-eq call-stp '(t nil))
                                   (natp call-stp)))
                   :mode :program))
   (if (variablep term)
       (mv (erp-nil) term state)
     (let ((fn (ffn-symb term)))
       (case fn
         (quote (mv (erp-nil) term state)) ;constant
         ((if myif) ;; (myif test then-branch else-branch)
          (b* ((test (farg1 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (prune-term (farg2 term) assumptions equality-assumptions rule-alist monitored-rules call-stp state)) ;we could add the condition as an assumption here
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (prog2$ (cw "Resolved the test to false.)~%")
                          (prune-term (farg3 term) assumptions equality-assumptions rule-alist monitored-rules call-stp state)) ;we could add the negated condition as an assumption here
                ;;todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term (farg2 term)
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term (farg3 term)
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state)))
                  (mv (erp-nil) `(,fn ,test ,then-part ,else-part) state))))))
         (bvif ;; (bvif size test then-branch else-branch)
          (b* ((size (farg1 term)) ;todo: prune this (it will usually be a constant, so that will be quick)
               (test (farg2 term))
               (then-branch (farg3 term))
               (else-branch (farg4 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (mv-let (erp then-branch state)
                          ;; we could add the condition as an assumption here:
                          (prune-term then-branch assumptions equality-assumptions rule-alist monitored-rules call-stp state)
                          (if erp
                              (mv erp nil state)
                            (mv (erp-nil)
                                `(bvchop ;$inline
                                  ,size ,then-branch) state))))
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (prog2$ (cw "Resolved the test to false.)~%")
                          (mv-let (erp else-branch state)
                            ;; we could add the negated condition as an assumption here:
                            (prune-term else-branch assumptions equality-assumptions rule-alist monitored-rules call-stp state)
                            (if erp
                                (mv erp nil state)
                              (mv (erp-nil)
                                  `(bvchop ;$inline
                                    ,size ,else-branch) state))))
                ;; todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term then-branch
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term else-branch
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state)))
                  (mv (erp-nil) `(bvif ,size ,test ,then-part ,else-part) state))))))
         (boolif ;; (boolif test then-branch else-branch)
          (b* ((test (farg1 term))
               (then-branch (farg2 term))
               (else-branch (farg3 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (mv-let (erp then-branch state)
                          ;; we could add the condition as an assumption here:
                          (prune-term then-branch assumptions equality-assumptions rule-alist monitored-rules call-stp state)
                          (if erp
                              (mv erp nil state)
                            (mv (erp-nil)
                                ;; todo: skip the bool-fix if known-boolean:
                                `(bool-fix ,then-branch) state))))
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (prog2$ (cw "Resolved the test to false.)~%")
                          (mv-let (erp else-branch state)
                            ;; we could add the negated condition as an assumption here:
                            (prune-term else-branch assumptions equality-assumptions rule-alist monitored-rules call-stp state)
                            (if erp
                                (mv erp nil state)
                              (mv (erp-nil)
                                  ;; todo: skip the bool-fix if known-boolean:
                                  `(bool-fix ,else-branch) state))))
                ;; todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term then-branch
                                  ;; todo: repeated call to get-conjuncts-of-term2 (and similar things elsewhere in this function):
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term else-branch
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state)))
                  (mv (erp-nil) `(boolif ,test ,then-part ,else-part) state))))))
         (t ;; Anything other than if/myif/bvif/boolif:
          ;; TODO: Handle bv-array-if?
          ;; TODO: Handle boolor?
          ;; TODO: Handle booland?
          ;; Look this up in the assumptions (if boolean or if only iff must be preserved -- could pass in an iff flag)?
          ;; TODO: Just do this for tests?
          ;; Do this even when the node is an IF...
          (if (and (or (member-equal term assumptions)
                       (member-equal term equality-assumptions))
                   (member-eq (ffn-symb term) (known-booleans (w state)))) ;todo avoid repeated calls to known-booleans
              (mv (erp-nil) *t* state)
            ;; Prune branches in arguments:
            (b* ((args (fargs term))
                 ((mv erp new-args state) (prune-terms args assumptions equality-assumptions rule-alist monitored-rules call-stp state))
                 ((when erp) (mv erp nil state)))
              (mv (erp-nil) `(,fn ,@new-args) state))))))))

 ;; Returns (mv erp result-terms state) where, if ERP is nil, then the
 ;; RESULT-TERMS are equal to their corresponding TERMS, given the ASSUMPTIONS
 ;; and EQUALITY-ASSUMPTIONS.
 (defun prune-terms (terms assumptions equality-assumptions rule-alist monitored-rules call-stp state)
   (declare (xargs :stobjs (state)
                   :guard (and (pseudo-term-listp terms)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions)
                               (rule-alistp rule-alist)
                               (symbol-listp monitored-rules)
                               (or (member-eq call-stp '(t nil))
                                   (natp call-stp)))
                   :mode :program))
   (if (endp terms)
       (mv (erp-nil) nil state)
     (b* (((mv erp pruned-first state) (prune-term (first terms) assumptions equality-assumptions rule-alist monitored-rules call-stp state))
          ((when erp) (mv erp nil state))
          ((mv erp pruned-rest state) (prune-terms (rest terms) assumptions equality-assumptions rule-alist monitored-rules call-stp state))
          ((when erp) (mv erp nil state)))
       (mv (erp-nil) (cons pruned-first pruned-rest) state)))))

;; Returns (mv erp result-term state).
;; This one takes a rule-alist
(defun prune-term-with-rule-alist (term assumptions rule-alist monitored-rules call-stp state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp term)
                              ;;(pseudo-term-listp assumptions)
                              (rule-alistp rule-alist)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :mode :program))
  (b* ((- (cw "(Pruning branches in term (~x0 rules, ~x1 assumptions).~%" (count-rules-in-rule-alist rule-alist) (len assumptions)))
       (assumptions (translate-terms assumptions 'prune-term-with-rule-alist (w state))) ;todo: add a flag to avoid this
       ((mv erp new-term state)
        (prune-term term
                    (fixup-assumptions assumptions)
                    (get-equalities assumptions)
                    rule-alist
                    monitored-rules call-stp
                    state))
       ((when erp) (mv erp nil state))
       (- (and (equal term new-term)
               (cw "No change!~%")))
       (- (cw "Done pruning.)~%")))
    (mv (erp-nil) new-term state)))

;; ;; Returns (mv result-term state)
;; ;; This one takes rules = a list of rule names
;; (defun prune-term (term assumptions rules monitored-rules call-stp state)
;;   (declare (xargs :stobjs (state)
;;                   :guard (and (pseudo-termp term)
;;                               ;;(pseudo-term-listp assumptions)
;;                               (symbol-listp rules)
;;                               (symbol-listp monitored-rules)
;;                               (or (member-eq call-stp '(t nil))
;;                                   (natp call-stp)))
;;                   :mode :program))
;;   (prune-term-with-rule-alist term assumptions (make-rule-alist rules (w state)) monitored-rules call-stp state))

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp result-dag state).
(defun prune-dag-with-rule-alist (dag-lst assumptions rule-alist monitored-rules call-stp state)
  (declare (xargs :stobjs (state)
                  :guard (and (rule-alistp rule-alist)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :mode :program))
  (b* ((term (dag-to-term dag-lst)) ; can explode!
       ((mv erp term state)
        (prune-term-with-rule-alist term assumptions rule-alist monitored-rules call-stp state))
       ((when erp) (mv erp nil state))
       ((mv erp dag) (dagify-term2 term))
       ((when erp) (mv erp nil state)))
    (mv (erp-nil) dag state)))

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp result-dag state).
(defun prune-dag (dag-lst assumptions rules monitored-rules call-stp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-listp rules)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :mode :program))
  (b* (((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv erp nil state)))
    (prune-dag-with-rule-alist dag-lst assumptions rule-alist monitored-rules call-stp state)))

;;Returns (mv erp result-dag state).  Pruning turns the DAG into a term and
;;then tries to resolve IF tests via rewriting and perhaps by calls to STP.
(defun maybe-prune-dag (prune-branches ; t, nil, or a limit on the size
                        dag-lst assumptions rules monitored-rules call-stp state)
  (declare (xargs :stobjs (state)
                  :guard (and (symbol-listp rules)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :mode :program))
  (let ((prune-branchesp (if (eq t prune-branches)
                             t
                           (if (eq nil prune-branches)
                               nil
                             (if (not (natp prune-branches))
                                 (er hard 'maybe-prune-dag "Bad prune-branches option (~x0)." prune-branches)
                               ;; todo: allow this to fail fast:
                               (dag-or-quotep-size-less-thanp dag-lst
                                                              prune-branches))))))
    (if prune-branchesp
        (b* ((size (dag-or-quotep-size-fast dag-lst)) ;todo: also perhaps done above
             (- (cw "(Pruning branches in DAG (~x0 nodes, ~x1 unique)~%" size (len dag-lst)))
             ;; (- (progn$ (cw "(DAG:~%")
             ;;            (print-list dag-lst)
             ;;            (cw ")~%")))
             (- (progn$ (cw "(Assumptions: ~X01)~%" assumptions nil)))
             ((mv erp result-dag state)
              (prune-dag dag-lst assumptions rules monitored-rules call-stp state))
             ((when erp) (mv erp nil state))
             (- (cw "Done pruning branches in DAG)~%")))
          (mv nil result-dag state))
      (mv nil dag-lst state))))

;; (include-book "kestrel/utilities/verify-guards-program" :dir :system)
;; (defttag fake)
;; (verify-guards-program prune-term :otf-flg t :hints (("Goal" :in-theory (disable SIMPLIFY-WITH-RULE-SETS))))
