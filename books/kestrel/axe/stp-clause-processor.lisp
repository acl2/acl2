; A clause-processor that calls STP
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

(include-book "prove-with-stp")

;Attempts to prove CLAUSE using STP.
;Returns (mv erp clauses state) where clauses is nil if STP proved the goal and
;otherwise is a singleton set containing the original clause (indicating that
;no change was made).  TODO: What is the format of the hint?
(defun stp-clause-processor (clause hint state)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (alistp hint))
                  :stobjs state))
  (b* (;; Get and check options:
       (hint-keys (strip-cars hint))
       (allowed-hint-keys '(:must-prove :counterexample))
       ((when (not (subsetp-equal hint-keys allowed-hint-keys)))
        (er hard? 'stp-clause-processor "Unsupported keys in hint: ~x0." (set-difference-equal hint-keys allowed-hint-keys))
        (mv :bad-hint (list clause) state))
       ;; Handle :must-prove :
       (must-prove (lookup-eq :must-prove hint))
       ((when (not (booleanp must-prove)))
        (er hard? 'stp-clause-processor "Bad :must-prove option, ~x0, in hint ~x1." must-prove hint)
        (mv :bad-hint (list clause) state))
       ;; Handle :counterexample :
       (counterexample (lookup-eq :counterexample hint))
       ((when (not (booleanp counterexample)))
        (er hard? 'stp-clause-processor "Bad :counterexample option, ~x0, in hint ~x1." counterexample hint)
        (mv :bad-hint (list clause) state))
       ;; Call STP:
       ((mv result state)
        (prove-clause-with-stp clause
                               counterexample
                               nil ; print-cex-as-signedp
                               *default-stp-max-conflicts* ;todo: get from the hint?
                               nil                   ;todo: get from the hint?
                               "STP-CLAUSE-PROC" ;todo: do better?  can we access the name of the theorem?
                               state)))
    (if (eq *error* result)
        (mv (erp-t) (list clause) state) ; error (and no change to clause set)
      (if (eq *valid* result)
          (mv (erp-nil) nil state) ; success: return the empty set of clauses
        ;; invalid or counterexample or timedout:
        (if must-prove
            (prog2$ (er hard? 'stp-clause-processor "Failed to prove but :must-prove was given.")
                    (mv (erp-t) (list clause) state))
          ;; no error but change to clause set:
          (mv (erp-nil) (list clause) state))))))

(define-trusted-clause-processor
  stp-clause-processor
  nil ;supporters ; todo: Think about this (I don't understand what :doc define-trusted-clause-processor says about "supporters")
  :ttag translate-dag-to-stp)

;;Check whether STP alone can prove a theorem
(defmacro defthm-with-stp-clause-processor (name term)
  `(defthm ,name ,term
     :hints (("Goal" :clause-processor (stp-clause-processor clause '((:must-prove . t)) state)))))
