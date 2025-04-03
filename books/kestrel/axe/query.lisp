; The code query tool
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains the query tool, which attempts to determine whether a
;; term is satisfiable.  Currently this uses rewriting and calls to the STP SMT
;; solver.  See documentation in doc.lisp.

;; TODO: Suppress more of the output printed during queries.

(include-book "tactic-prover")
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)

;; We define these constants to ensure we never mistype the corresponding
;; keywords.
(defconst *sat* :sat)
(defconst *unsat* :unsat)

;; Tries to find values of the variables in TERM that make TERM true.  TERM will
;; often be a conjunction.  TERM need not already be translated.
;; TODO: Should this do any kind of redundancy checking?
;; Returns (mv result state) where result is *sat*, *unsat*, *unknown*, or *error*.
;; TODO: Suppress Axe printing like "Giving up because the uncut goal TACTIC-QUERY is invalid."
(defun query-fn (term ;; untranslated, often a conjunction
                 rules
                 max-conflicts
                 print
                 state)
  (declare (xargs :guard (and (symbol-listp rules) ;TODO: Support rules :auto (include some basic things like pushing NOT across IF)
                              (or (natp max-conflicts)
                                  (null max-conflicts) ; no limit
                                  (eq :auto max-conflicts))
                              ;; print
                              )
                  :stobjs state
                  :mode :program ;because this calls translate-term (TODO: Separate that out) and also apply-proof-tactics-to-problem
                  ))
  (b* ((term (translate-term term 'query-fn (w state)))
       (term `(not ,term)) ;we attempt to prove the negation of the term
       ;; TODO: Try to extract assumptions from the term, but this is not quite right?  perhaps push the not through first?
       ;;((mv assumptions term) (term-hyps-and-conc term))
       (assumptions nil)
       (tactics '(:rewrite :stp))
       ((mv erp rule-alist) (make-rule-alist rules (w state)))
       ((when erp) (mv *error* state))
       ((mv erp dag) (dagify-term term))
       ((when erp) (mv *error* state))
       (monitor nil) ;todo
       (call-stp-when-pruning t)
       (max-conflicts (if (eq :auto max-conflicts) *default-stp-max-conflicts* max-conflicts)) ; a number of conflicts, or nil for no max
       ;;(rule-alist (make-rule-alist rules (w state))) ;todo; don't need both of these..
       ;;(assumptions (translate-terms assumptions 'prove-with-tactics-fn (w state))) ;throws an error on bad input
       ;; ((mv dag assumptions2)
       ;;  ;; TODO: Or do we want to leave the assumptions so they can get rewritten?
       ;;  (dag-or-term-to-dag-and-assumptions dag-or-term (w state)))
       ;; (assumptions (append assumptions assumptions2)) ;TODO: which assumptions / term / dag should be used in the theorem below?
       ;; ((mv assumptions state)
       ;;  (if simplify-assumptions
       ;;      (simplify-terms-using-each-other assumptions rule-alist)
       ;;    (mv assumptions state)))
       (vars (dag-vars dag))
       (- (and print (cw "Variables in DAG: ~x0~%" vars)))
       ((mv result info-acc state)
        (apply-proof-tactics-to-problem (make-problem dag assumptions)
                                        tactics rule-alist
                                        nil ; interpreted-function-alist ; todo: thread through
                                        monitor
                                        t ;normalize-xors (todo: make this an option?)
                                        print max-conflicts call-stp-when-pruning
                                        t ; counterexamplep
                                        nil ; print-cex-as-signedp
                                        nil state)))
    (if (eq *error* result)
        (prog2$ (er hard? 'query-fn "Error encountered in the tactic prover.")
                (mv *unknown* state))
      (if (eq *unknown* result)
          (mv *unknown* state)
        (if (eq *valid* result) ;negated term was valid, so no assignment can satisfy the query
            (mv *unsat* state)
          (if (eq *invalid* result)
              (b* ((last-info (car (last info-acc)))
                   ;;(- (cw "Info: ~x0~%" last-info))
                   )
                (if (call-of :var-counterexample last-info)
                    (prog2$ (cw "(Satisfying assignment: ~x0.)~%" (second last-info))
                            ;; found a satisfying assignment (TODO: Check it! -- actually, it should be checked deeper in the code, once we process the raw counterexample)
                            (mv *sat* state))
                  (if (call-of *possible-counterexample* last-info)
                      ;;counterexample may be spurious, so we print it but return unknown
                      (prog2$ (cw "(Possible counterexample: ~X01)~%." (cdr last-info) nil)
                              (mv *unknown* state))
                    (if (eq :simplified-to-nil last-info)
                        (prog2$ (cw "(True for all values!)~%")
                                ;; TODO: Perhaps return a satisfying assignment (respecting types?)
                                (mv *valid* state))
                      (prog2$ (er hard 'query-fn "Bad info from last tactic in invalid case: ~x0" last-info)
                              (mv *unknown* state))))))
            (prog2$ (er hard? 'query-fn "Unexpected result from tactic prover: ~x0." result)
                    (mv *unknown* state))))))))

;; Try to find values of the variables in TERM that make TERM true.  TERM will
;; often be a conjunction.  TERM need not already be translated.
;; todo: get doc from kestrel-acl2/axe/doc.lisp
(defmacro query (term &key
                      (rules 'nil)
                      (max-conflicts ':auto)
                      (print 'nil))
  `(query-fn ',term ,rules ',max-conflicts ,print state))

(defmacro assert-query-result (query expected-result)
  `(assert-equal-with-stobjs ,query
                             ',expected-result
                             :stobjs state))
