; Pruning irrelevant IF-branches
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Prune irrelevant if-then-else branches in terms and DAGs using rewriting and calls to STP.

;; TODO: Use counterexamples returned by STP to avoid later calls that will fail.

(include-book "rewriter-basic") ;because we call simplify-term-basic
(include-book "prove-with-stp")
(include-book "make-term-into-dag-simple")
(include-book "interpreted-function-alists")
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

;; Returns (mv erp result state) where RESULT is :true (meaning non-nil), :false, or :unknown.
;; (It may be the case that the test can be shown to be other true and false,
;; because the assumptions contradict, in which case the entire enclosing
;; IF/MYIF/BOOLIF/BVIF may be irrelevant.)
;; TODO: Allow STP to run longer (more conflicts) for IFs that are higher up in the term, since resolving such an IF throws away more stuff.
(defund try-to-resolve-test (test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
  (declare (xargs :guard (and (pseudo-termp test)
                              (pseudo-term-listp assumptions)
                              (pseudo-term-listp equality-assumptions)
                              (symbol-listp monitored-rules)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :stobjs (state)))
  (b* ( ;; First apply the Axe Rewriter to the test:
       (- (cw "(Simplifying test.~%"))
       ;; ((mv erp simplified-dag-or-quotep state)
       ;;  (simp-term test ;; TODO: Does this use contexts?
       ;;             :rule-alist rule-alist
       ;;             :interpreted-function-alist interpreted-function-alist
       ;;             :monitor monitored-rules
       ;;             :assumptions assumptions ;no equality assumptions here to prevent loops (todo: think about this)
       ;;             :check-inputs nil))
       ((mv erp simplified-dag-or-quotep)
        (simplify-term-basic test ;; TODO: Does this use contexts?
                             assumptions ;no equality assumptions here to prevent loops (todo: think about this)
                             rule-alist
                             interpreted-function-alist
                             monitored-rules
                             nil ; memoizep
                             nil ; count-hits
                             nil ; print
                             (w state)))
       ((when erp) (mv erp nil state))
       ((when (quotep simplified-dag-or-quotep))
        ;; Resolved the test via rewriting:
        (cw "Simplified to the constant ~x0.)~%" simplified-dag-or-quotep)
        (if (unquote simplified-dag-or-quotep)
            (mv nil :true state)
          (mv nil :false state)))
       ;; Test did not rewrite to a constant, so try other things:
       ;; (- (cw "(Simplified to ~X01.)~%" simplified-dag-or-quotep nil))
       (- (cw "Did not simplify to a constant.)~%"))
       ;; Is this needed, given that we simplified the test above using the assumptions?
       ((when (or (member-equal test assumptions)
                  (member-equal test equality-assumptions))) ;; In case the test is not a known boolean (so rewriting can't rewrite it to t). ;todo: use simplified-test-term here?
        (prog2$ (cw "(The test is a known assumption.)")
                (mv nil :true state))) ;a test that's in the assumptions is like a test that rewrites to t
       ;; TODO: What if the test is equal to an assumption but not identical to it (e.g., a disjunction with the disjuncts reordered?)
       (simplified-test-term (dag-to-term simplified-dag-or-quotep)) ;TODO: check that this is not huge (I suppose it could be if something gets unrolled)
       ((when (not call-stp))
        (mv nil :unknown state))
       ;; TODO: Consider trying to be smart about whether to try the true proof or the false proof first.
       (- (cw "(Attempting to prove test true with STP:~%"))
       ((mv true-result state)
        (prove-implication-with-stp simplified-test-term
                                    assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
                                    nil         ;counterexamplep
                                    *default-stp-max-conflicts*
                                    nil                ;print
                                    "PRUNE-PROVE-TRUE" ;todo: do better?
                                    state))
       ((when (eq *error* true-result))
        (prog2$ (er hard? 'try-to-resolve-test "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* true-result)) ;; STP proved the test
        (prog2$ (cw "STP proved the test true.)~%")
                (mv nil :true state)))
       (- (cw "STP failed to prove the test true.)~%"))
       (- (cw "(Attempting to prove test false with STP:~%"))
       ((mv false-result state)
        (prove-implication-with-stp `(not ,simplified-test-term)
                                    assumptions ;todo: this caused problems with an rlp example: (append assumptions equality-assumptions)
                                    nil         ;counterexamplep
                                    (if (natp call-stp) call-stp *default-stp-max-conflicts*)
                                    nil                 ;print
                                    "PRUNE-PROVE-FALSE" ;todo: do better?
                                    state))
       ((when (eq *error* false-result))
        (prog2$ (er hard? 'try-to-resolve-test "Error calling STP")
                (mv :error-calling-stp :unknown state)))
       ((when (eq *valid* false-result)) ;; STP proved the negation of the test
        (prog2$ (cw "STP proved the test false.)~%")
                (mv nil :false state))))
    (prog2$ (cw "STP did not resolve the test.)~%")
            (mv nil :unknown state))))

;; TODO: Thread through a print option
(mutual-recursion
 ;; Returns (mv erp result-term state) where RESULT-TERM is equal
 ;; to TERM. Tries to rewrite each myif test using context from all overarching
 ;; tests (and any given assumptions).
;TODO: Add an IFF flag and, if set, turn (if x t nil) into x and (if x nil t) into (not x)
 (defund prune-term-aux (term assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
   (declare (xargs :stobjs (state)
                   :guard (and (pseudo-termp term)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions) ;used only for looking up conditions
                               (symbol-listp monitored-rules)
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (or (member-eq call-stp '(t nil))
                                   (natp call-stp)))
                   :verify-guards nil ; done below
                   ))
   (if (variablep term)
       (mv (erp-nil) term state)
     (let ((fn (ffn-symb term)))
       (case fn
         (quote (mv (erp-nil) term state)) ;constant
         ((if myif) ;; (myif test then-branch else-branch)
          (b* ((test (farg1 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (prune-term-aux (farg2 term) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)) ;we could add the condition as an assumption here
              (if (eq :false result)
                  ;; Throw away the then-branch:
                  (prog2$ (cw "Resolved the test to false.)~%")
                          (prune-term-aux (farg3 term) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)) ;we could add the negated condition as an assumption here
                ;;todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term-aux (farg2 term)
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term-aux (farg3 term)
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state)))
                  (mv (erp-nil) `(,fn ,test ,then-part ,else-part) state))))))
         (bvif ;; (bvif size test then-branch else-branch)
          (b* ((size (farg1 term)) ;todo: prune this (it will usually be a constant, so that will be quick)
               (test (farg2 term))
               (then-branch (farg3 term))
               (else-branch (farg4 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (mv-let (erp then-branch state)
                          ;; we could add the condition as an assumption here:
                          (prune-term-aux then-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
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
                            (prune-term-aux else-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
                            (if erp
                                (mv erp nil state)
                              (mv (erp-nil)
                                  `(bvchop ;$inline
                                    ,size ,else-branch) state))))
                ;; todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term-aux then-branch
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term-aux else-branch
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state)))
                  (mv (erp-nil) `(bvif ,size ,test ,then-part ,else-part) state))))))
         (boolif ;; (boolif test then-branch else-branch)
          (b* ((test (farg1 term))
               (then-branch (farg2 term))
               (else-branch (farg3 term))
               ;; First prune the test:
               ((mv erp test state)
                (prune-term-aux test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state))
               (- (cw "(Attempting to resolve test using ~x0 assumptions and ~x1 equality assumptons.~%" (len assumptions) (len equality-assumptions)))
               ;; Now try to resolve the pruned test:
               ((mv erp result ;:true, :false, or :unknown
                    state)
                (try-to-resolve-test test assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
               ((when erp) (mv erp nil state)))
            (if (eq :true result)
                (prog2$ (cw "Resolved the test to true.)~%")
                        ;; Throw away the else-branch:
                        (mv-let (erp then-branch state)
                          ;; we could add the condition as an assumption here:
                          (prune-term-aux then-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
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
                            (prune-term-aux else-branch assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
                            (if erp
                                (mv erp nil state)
                              (mv (erp-nil)
                                  ;; todo: skip the bool-fix if known-boolean:
                                  `(bool-fix ,else-branch) state))))
                ;; todo: if it simplifies to something other than t/nil, use that here?
                (b* ((- (cw "Did not resolve test.)~%"))
                     ;; Recur on the then-branch, assuming the (pruned, but not simplified) test:
                     ((mv erp then-part state)
                      (prune-term-aux then-branch
                                  ;; todo: repeated call to get-conjuncts-of-term2 (and similar things elsewhere in this function):
                                  (union-equal (fixup-assumptions (get-conjuncts-of-term2 test)) assumptions)
                                  (union-equal (get-equalities (get-conjuncts-of-term2 test)) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
                     ((when erp) (mv erp nil state))
                     ;; Recur on the else-branch, assuming the negation of the (pruned, but not simplified) test:
                     ;; TODO: Perhaps call get-disjunction and handle a possible constant returned?:
                     (negated-test-conjuncts (negate-disjuncts (get-disjuncts-of-term2 test)))
                     ((mv erp else-part state)
                      (prune-term-aux else-branch
                                  (union-equal (fixup-assumptions negated-test-conjuncts) assumptions)
                                  (union-equal (get-equalities negated-test-conjuncts) equality-assumptions)
                                  rule-alist interpreted-function-alist monitored-rules call-stp state))
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
                 ((mv erp new-args state) (prune-terms-aux args assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
                 ((when erp) (mv erp nil state)))
              (mv (erp-nil) `(,fn ,@new-args) state))))))))

 ;; Returns (mv erp result-terms state) where, if ERP is nil, then the
 ;; RESULT-TERMS are equal to their corresponding TERMS, given the ASSUMPTIONS
 ;; and EQUALITY-ASSUMPTIONS.
 (defund prune-terms-aux (terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
   (declare (xargs :stobjs (state)
                   :guard (and (pseudo-term-listp terms)
                               (pseudo-term-listp assumptions)
                               (pseudo-term-listp equality-assumptions)
                               (rule-alistp rule-alist)
                               (interpreted-function-alistp interpreted-function-alist)
                               (symbol-listp monitored-rules)
                               (or (member-eq call-stp '(t nil))
                                   (natp call-stp)))))
   (if (endp terms)
       (mv (erp-nil) nil state)
     (b* (((mv erp pruned-first state) (prune-term-aux (first terms) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
          ((when erp) (mv erp nil state))
          ((mv erp pruned-rest state) (prune-terms-aux (rest terms) assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
          ((when erp) (mv erp nil state)))
       (mv (erp-nil) (cons pruned-first pruned-rest) state)))))

(make-flag prune-term-aux)

(defthm-flag-prune-term-aux
  (defthm len-of-mv-nth-1-of-prune-terms-aux-skip
    :flag prune-term-aux
    :skip t)
  (defthm len-of-mv-nth-1-of-prune-terms-aux
    (implies (not (mv-nth 0 (prune-terms-aux terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)))
             (equal (len (mv-nth 1  (prune-terms-aux terms assumptions equality-assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)))
                    (len terms)))
    :flag prune-terms-aux)
  :hints (("Goal" :in-theory (enable len prune-terms-aux))))

(defthm-flag-prune-term-aux
  (defthm prune-term-aux-return-type
    (implies (and (pseudo-termp term)
                  (pseudo-term-listp assumptions)
                  (pseudo-term-listp equality-assumptions) ;used only for looking up conditions
                  (symbol-listp monitored-rules)
                  (rule-alistp rule-alist)
                  (interpreted-function-alistp interpreted-function-alist)
                  )
             (pseudo-termp (mv-nth 1 (prune-term-aux term assumptions equality-assumptions
                                                 rule-alist interpreted-function-alist
                                                 monitored-rules call-stp state))))
    :flag prune-term-aux)
  (defthm prune-terms-aux-return-type
    (implies (and (pseudo-term-listp terms)
                  (pseudo-term-listp assumptions)
                  (pseudo-term-listp equality-assumptions)
                  (rule-alistp rule-alist)
                  (interpreted-function-alistp interpreted-function-alist)
                  (symbol-listp monitored-rules)
                  )
             (pseudo-term-listp (mv-nth 1  (prune-terms-aux terms assumptions equality-assumptions
                                                        rule-alist interpreted-function-alist
                                                        monitored-rules call-stp state))))
    :flag prune-terms-aux)
  :hints (("Goal" :in-theory (enable prune-term-aux prune-terms-aux))))

(verify-guards prune-term-aux)

;; Returns (mv erp result-term state).
;todo: rename to prune-term
;; TODO: Print some stats about the pruning process?
(defund prune-term-new (term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp assumptions)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :stobjs state))
  (b* ((- (cw "(Pruning branches in term (~x0 rules, ~x1 assumptions).~%" (count-rules-in-rule-alist rule-alist) (len assumptions)))
       ((mv erp new-term state)
        (prune-term-aux term
                        (fixup-assumptions assumptions)
                        (get-equalities assumptions)
                        rule-alist
                        interpreted-function-alist
                        monitored-rules
                        call-stp
                        state))
       ((when erp) (mv erp nil state))
       (- (and (equal term new-term)
               (cw "No change!~%")))
       (- (cw "Done pruning.)~%")))
    (mv (erp-nil) new-term state)))

(defthm pseudo-termp-of-mv-nth-1-of-prune-term-new
  (implies (and (pseudo-termp term)
                (pseudo-term-listp assumptions)
                (rule-alistp rule-alist)
                (interpreted-function-alistp interpreted-function-alist)
                (symbol-listp monitored-rules)
                (or (member-eq call-stp '(t nil))
                    (natp call-stp)))
           (pseudo-termp (mv-nth 1 (prune-term-new term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))))
  :hints (("Goal" :in-theory (enable prune-term-new))))


;; ;; Returns (mv erp result-term state).
;; ;; TODO: Deprecate?  Why does this not translate the term too?
;; ;todo: rename
;; (defun prune-term-with-rule-alist (term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
;;   (declare (xargs :stobjs (state)
;;                   :guard (and (pseudo-termp term)
;;                               ;;(pseudo-term-listp assumptions)
;;                               (rule-alistp rule-alist)
;;                               (interpreted-function-alistp interpreted-function-alist)
;;                               (symbol-listp monitored-rules)
;;                               (or (member-eq call-stp '(t nil))
;;                                   (natp call-stp)))
;;                   :mode :program ; because we call translate-terms
;;                   ))
;;   (prune-term-new term
;;                   (translate-terms assumptions 'prune-term-with-rule-alist (w state))
;;                   rule-alist
;;                   interpreted-function-alist
;;                   monitored-rules
;;                   call-stp
;;                   state))

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

;; ;; Prune unreachable branches using full contexts.  Warning: can explode the
;; ;; term size. Returns (mv erp result-dag state).
;; ;; TODO: This internally translates assumptions - deprecate?
;; (defun prune-dag-with-rule-alist (dag-lst assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
;;   (declare (xargs :guard (and (rule-alistp rule-alist)
;;                               (interpreted-function-alistp interpreted-function-alist)
;;                               (symbol-listp monitored-rules)
;;                               (or (member-eq call-stp '(t nil))
;;                                   (natp call-stp)))
;;                   :mode :program
;;                   :stobjs state))
;;   (b* ((term (dag-to-term dag-lst)) ; can explode!
;;        ((mv erp term state)
;;         (prune-term-with-rule-alist term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
;;        ((when erp) (mv erp nil state))
;;        ((mv erp dag) (dagify-term2 term)) ; todo: try make-term-into-dag-simple here
;;        ((when erp) (mv erp nil state)))
;;     (mv (erp-nil) dag state)))

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp result-dag state).
(defund prune-dag-with-rule-alist-new (dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp state)
  (declare (xargs :guard (and (or (pseudo-dagp dag)
                                  ;; (QUOTEP dag) ; possible?
                                  )
                              (pseudo-term-listp assumptions)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp)))
                  :stobjs state))
  (b* ((term (dag-to-term dag)) ; can explode!
       ((mv erp term state)
        (prune-term-new term assumptions rule-alist interpreted-function-alist monitored-rules call-stp state))
       ((when erp) (mv erp nil state))
       ((mv erp dag) (make-term-into-dag-simple term))
       ((when erp) (mv erp nil state)))
    (mv (erp-nil) dag state)))

;; ;; Prune unreachable branches using full contexts.  Warning: can explode the
;; ;; term size. Returns (mv erp result-dag state).
;; ;todo: deprecate?
;; (defun prune-dag (dag-lst assumptions rules interpreted-fns monitored-rules call-stp state)
;;   (declare (xargs :stobjs (state)
;;                   :guard (and (symbol-listp rules)
;;                               (symbol-listp interpreted-fns)
;;                               (symbol-listp monitored-rules)
;;                               (or (member-eq call-stp '(t nil))
;;                                   (natp call-stp)))
;;                   :mode :program))
;;   (b* (((mv erp rule-alist) (make-rule-alist rules (w state)))
;;        ((when erp) (mv erp nil state)))
;;     (prune-dag-with-rule-alist dag-lst assumptions rule-alist
;;                                (make-interpreted-function-alist interpreted-fns (w state))
;;                                monitored-rules call-stp state)))

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp result-dag state).
(defund prune-dag-new (dag-lst assumptions rules interpreted-fns monitored-rules call-stp state)
  (declare (xargs :guard (and (pseudo-dagp dag-lst)
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules)
                              (symbol-listp interpreted-fns)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* (((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv erp nil state)))
    (prune-dag-with-rule-alist-new dag-lst assumptions rule-alist
                                   (make-interpreted-function-alist interpreted-fns (w state))
                                   monitored-rules call-stp state)))

;; ;;Returns (mv erp result-dag state).  Pruning turns the DAG into a term and
;; ;;then tries to resolve IF tests via rewriting and perhaps by calls to STP.
;; ;deprecate?
;; (defun maybe-prune-dag (prune-branches ; t, nil, or a limit on the size
;;                         dag-lst assumptions rules interpreted-fns monitored-rules call-stp state)
;;   (declare (xargs :stobjs (state)
;;                   :guard (and (symbol-listp rules)
;;                               (symbol-listp interpreted-fns)
;;                               (symbol-listp monitored-rules)
;;                               (or (member-eq call-stp '(t nil))
;;                                   (natp call-stp)))
;;                   :mode :program))
;;   (let ((prune-branchesp (if (eq t prune-branches)
;;                              t
;;                            (if (eq nil prune-branches)
;;                                nil
;;                              (if (not (natp prune-branches))
;;                                  (er hard 'maybe-prune-dag "Bad prune-branches option (~x0)." prune-branches)
;;                                ;; todo: allow this to fail fast:
;;                                (dag-or-quotep-size-less-thanp dag-lst
;;                                                               prune-branches))))))
;;     (if prune-branchesp
;;         (b* ((size (dag-or-quotep-size-fast dag-lst)) ;todo: also perhaps done above
;;              (- (cw "(Pruning branches in DAG (~x0 nodes, ~x1 unique)~%" size (len dag-lst)))
;;              ;; (- (progn$ (cw "(DAG:~%")
;;              ;;            (print-list dag-lst)
;;              ;;            (cw ")~%")))
;;              (- (progn$ (cw "(Assumptions: ~X01)~%" assumptions nil)))
;;              ((mv erp result-dag state)
;;               (prune-dag dag-lst assumptions rules interpreted-fns monitored-rules call-stp state))
;;              ((when erp) (mv erp nil state))
;;              (- (cw "Done pruning branches in DAG)~%")))
;;           (mv nil result-dag state))
;;       (mv nil dag-lst state))))

;;Returns (mv erp result-dag state).  Pruning turns the DAG into a term and
;;then tries to resolve IF tests via rewriting and perhaps by calls to STP.
(defund maybe-prune-dag-new (prune-branches ; t, nil, or a limit on the size
                            dag-lst assumptions rules interpreted-fns monitored-rules call-stp state)
  (declare (xargs :guard (and (or (eq nil prune-branches)
                                  (eq t prune-branches)
                                  (natp prune-branches))
                              (pseudo-dagp dag-lst)
                              (< (len dag-lst) 2147483647) ;todo?
                              (pseudo-term-listp assumptions)
                              (symbol-listp rules)
                              (symbol-listp interpreted-fns)
                              (symbol-listp monitored-rules)
                              (or (member-eq call-stp '(t nil))
                                  (natp call-stp))
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
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
              (prune-dag-new dag-lst assumptions rules interpreted-fns monitored-rules call-stp state))
             ((when erp) (mv erp nil state))
             (- (cw "Done pruning branches in DAG)~%")))
          (mv nil result-dag state))
      (mv nil dag-lst state))))
