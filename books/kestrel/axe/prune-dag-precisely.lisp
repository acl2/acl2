; Pruning irrelevant IF-branches
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Prune irrelevant if-then-else branches in DAGs using rewriting and calls to STP.

(include-book "prune-term")
(include-book "dag-size-fast")
(include-book "make-term-into-dag-simple")
;(include-book "kestrel/utilities/real-time-since" :dir :system)
;(include-book "kestrel/utilities/rational-printing" :dir :system) ; for print-to-hundredths
(local (include-book "kestrel/utilities/get-real-time" :dir :system))

(local (in-theory (disable mv-nth myquotep w symbol-listp ilks-plist-worldp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp dag-or-quotep state).
(defund prune-dag-precisely-with-rule-alist (dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp check-fnsp print state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (pseudo-term-listp assumptions)
                              (rule-alistp rule-alist)
                              (interpreted-function-alistp interpreted-function-alist)
                              (symbol-listp monitored-rules)
                              (or (booleanp call-stp)
                                  (natp call-stp))
                              (booleanp check-fnsp)
                              (print-levelp print))
                  :stobjs state))
  (let (;; Refrain from pruning if there are no functions that cause pruning attempts:
        (prunep (if check-fnsp (dag-fns-include-anyp dag '(if myif boolif bvif)) t)))
    (if (not prunep)
        (mv (erp-nil) dag state)
      (b* ( ;; TODO: Consider first doing a pruning as a DAG, using only approximate contexts (or would that not do anything that rewriting doesn't already do?)
           (term (dag-to-term dag)) ; can explode!
           ((mv erp changep term state)
            (prune-term term assumptions rule-alist interpreted-function-alist monitored-rules call-stp print state)) ; todo: call something here that returns a dag, not a term!
           ((when erp) (mv erp nil state))
           ((mv erp dag)
            (if changep
              ;; something changed, so make a new dag:
                (make-term-into-dag-simple term)
            ;; returning the original dag ensures that nodenums didn't change:
              (mv (erp-nil) dag)))
           ((when erp) (mv erp nil state)))
        (mv (erp-nil) dag state)))))

(defthm pseudo-dagp-of-mv-nth-1-of-prune-dag-precisely-with-rule-alist
  (implies (and (not (mv-nth 0 (prune-dag-precisely-with-rule-alist dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp check-fnsp print state)));; no error
                (not (myquotep (mv-nth 1 (prune-dag-precisely-with-rule-alist dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp check-fnsp print state))))
                (pseudo-dagp dag)
                (pseudo-term-listp assumptions)
                (rule-alistp rule-alist)
                (interpreted-function-alistp interpreted-function-alist)
                (symbol-listp monitored-rules)
                (or (booleanp call-stp)
                    (natp call-stp)))
           (pseudo-dagp (mv-nth 1 (prune-dag-precisely-with-rule-alist dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp check-fnsp print state))))
  :hints (("Goal" :in-theory (enable prune-dag-precisely-with-rule-alist))))

(defthm w-of-mv-nth-2-of-prune-dag-precisely-with-rule-alist
  (equal (w (mv-nth 2 (prune-dag-precisely-with-rule-alist dag assumptions rule-alist interpreted-function-alist monitored-rules call-stp check-fnsp print state)))
         (w state))
  :hints (("Goal" :in-theory (enable prune-dag-precisely-with-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prune unreachable branches using full contexts.  Warning: can explode the
;; term size. Returns (mv erp dag-or-quotep state).
;; TODO: This makes the rule-alist each time it is called.
;; TODO: Consider first pruning with approximate contexts.
(defund prune-dag-precisely (dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp check-fnsp print state)
  (declare (xargs :guard (and (pseudo-dagp dag)
                              (pseudo-term-listp assumptions)
                              (or (symbol-listp rules)
                                  (eq :none rules))
                              (or (rule-alistp rule-alist)
                                  (eq :none rule-alist))
                              ;; At most one of the rules and rule-alist are not :none:
                              (<= (+ (if (eq :none rules) 0 1)
                                     (if (eq :none rule-alist) 0 1))
                                  1)
                              (symbol-listp interpreted-fns)
                              (symbol-listp monitored-rules)
                              (or (booleanp call-stp)
                                  (natp call-stp))
                              (booleanp check-fnsp)
                              (print-levelp print)
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* (((mv erp rule-alist)
        (if (not (eq :none rule-alist))
            (mv (erp-nil) rule-alist)
          (if (not (eq :none rules))
              (make-rule-alist rules (w state)) ; todo: avoid this if the dag-fns-include-anyp check will fail
            (mv (erp-nil) nil))))
       ((when erp) (mv erp nil state)))
    (prune-dag-precisely-with-rule-alist dag assumptions rule-alist
                                         (make-interpreted-function-alist interpreted-fns (w state))
                                         monitored-rules call-stp check-fnsp print state)))

(defthm pseudo-dagp-of-mv-nth-1-of-prune-dag-precisely
  (implies (and (not (mv-nth 0 (prune-dag-precisely dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp check-fnsp print state))) ;; no error
                (not (myquotep (mv-nth 1 (prune-dag-precisely dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp check-fnsp print state))))
                (pseudo-dagp dag)
                (pseudo-term-listp assumptions)
                (or (symbol-listp rules)
                    (eq :none rules))
                (or (rule-alistp rule-alist)
                    (eq :none rule-alist))
                (symbol-listp interpreted-fns)
                (symbol-listp monitored-rules)
                (or (booleanp call-stp)
                    (natp call-stp))
                (ilks-plist-worldp (w state)))
           (pseudo-dagp (mv-nth 1 (prune-dag-precisely dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp check-fnsp print state))))
  :hints (("Goal" :in-theory (enable prune-dag-precisely))))

(defthm w-of-mv-nth-2-of-prune-dag-precisely
  (equal (w (mv-nth 2 (prune-dag-precisely dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp check-fnsp print state)))
         (w state))
  :hints (("Goal" :in-theory (enable prune-dag-precisely))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Returns (mv erp result-dag-or-quotep state).  Pruning turns the DAG into a term and
;;then tries to resolve IF tests via rewriting and perhaps by calls to STP.
;; TODO: This can make the rule-alist each time it is called.
(defund maybe-prune-dag-precisely (prune-branches ; t, nil, or a limit on the size
                                   dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp
                                   print
                                   state)
  (declare (xargs :guard (and (or (booleanp prune-branches)
                                  (natp prune-branches))
                              (pseudo-dagp dag)
                              (pseudo-term-listp assumptions)
                              (or (symbol-listp rules)
                                  (eq :none rules))
                              (or (rule-alistp rule-alist)
                                  (eq :none rule-alist))
                              ;; At most one of the rules and rule-alist are not :none:
                              (<= (+ (if (eq :none rules) 0 1)
                                     (if (eq :none rule-alist) 0 1))
                                  1)
                              (symbol-listp interpreted-fns)
                              (symbol-listp monitored-rules)
                              (or (booleanp call-stp)
                                  (natp call-stp))
                              (print-levelp print)
                              (ilks-plist-worldp (w state)))
                  :stobjs state))
  (b* (((when (not prune-branches))
        ;; don't even print anything in this case, as we've been told not to prune
        (mv nil dag state))
       ((when (not (<= (len dag) *max-1d-array-length*)))
        (mv :dag-too-big nil state))
       ((when (not (dag-fns-include-anyp dag '(if myif boolif bvif))))
        (and (print-level-at-least-tp print) (cw "(No precise pruning to do.)~%"))
        (mv nil dag state))
       ((when (and (natp prune-branches) ; it's a limit on the size
                   ;; todo: allow this to fail fast:
                   (not (dag-or-quotep-size-less-thanp dag prune-branches))))
        ;; todo: don't recompute the size here:
        (cw "(Note: Not pruning with precise contexts since DAG size (~x0) exceeds ~x1.)~%" (dag-or-quotep-size-fast dag) prune-branches)
        (mv nil dag state))
       ;; prune-branches is either t or is a size limit and the dag is small enough, so we prune
       ;;todo: size also computed above
       (- (cw "(Pruning DAG precisely (~x0 nodes, ~x1 unique):~%" (dag-or-quotep-size-fast dag) (len dag)))
       (old-dag dag)
       ((mv start-real-time state) (get-real-time state)) ; we use wall-clock time so that time in STP is counted
       (- (and (print-level-at-least-tp print)
               (progn$ (cw "(DAG:~%")
                       (print-list dag)
                       (cw ")~%")
                       (cw "(Assumptions: ~X01)~%" assumptions nil))))
       ((mv erp result-dag-or-quotep state)
        (prune-dag-precisely dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp
                             nil ; we already know there are prunable ops
                             print
                             state))
       ((when erp) (mv erp nil state))
       ;; todo: should we do a rewrite here?
       ((mv elapsed state) (real-time-since start-real-time state))
       (- (cw " (Pruning took ")
          (print-to-hundredths elapsed) ; todo: could have real-time-since detect negative time
          (cw "s.)~%"))
       ((when (quotep result-dag-or-quotep))
        (cw " Done pruning. Result: ~x0)~%" result-dag-or-quotep)
        (mv (erp-nil) result-dag-or-quotep state))
       ;; It's a dag:
       (result-dag-len (len result-dag-or-quotep))
       (result-dag-size (if (not (<= result-dag-len *max-1d-array-length*))
                            "many" ; too big to call dag-or-quotep-size-fast (todo: impossible?)
                          (dag-or-quotep-size-fast result-dag-or-quotep)))
       (- (cw " Done pruning (~x0 nodes, ~x1 unique)." result-dag-size result-dag-len)
          (and (equal old-dag dag) (cw " No change."))
          (cw ")~%")))
    (mv nil result-dag-or-quotep state)))

(defthm pseudo-dagp-of-mv-nth-1-of-maybe-prune-dag-precisely
  (implies (and (not (mv-nth 0 (maybe-prune-dag-precisely prune-branches dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp print state))) ;; no error
                (not (myquotep (mv-nth 1 (maybe-prune-dag-precisely prune-branches dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp print state))))
                (pseudo-dagp dag)
                (pseudo-term-listp assumptions)
                (or (symbol-listp rules)
                    (eq :none rules))
                (or (rule-alistp rule-alist)
                    (eq :none rule-alist))
                (symbol-listp interpreted-fns)
                (symbol-listp monitored-rules)
                (or (booleanp call-stp)
                    (natp call-stp))
                (ilks-plist-worldp (w state)))
           (pseudo-dagp (mv-nth 1 (maybe-prune-dag-precisely prune-branches dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp print state))))
  :hints (("Goal" :in-theory (enable maybe-prune-dag-precisely))))

(defthm w-of-mv-nth-2-of-maybe-prune-dag-precisely
  (equal (w (mv-nth 2 (maybe-prune-dag-precisely prune-branches dag assumptions rules rule-alist interpreted-fns monitored-rules call-stp print state)))
         (w state))
  :hints (("Goal" :in-theory (enable maybe-prune-dag-precisely))))
