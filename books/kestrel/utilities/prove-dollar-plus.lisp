; An interface to prove$ that indicates whether a step limit was reached.
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add a way to return the failed subgoals

(include-book "tools/prove-dollar" :dir :system)
(include-book "tools/prover-steps-counted" :dir :system)

;; Returns (mv erp provedp failure-info state).
(defun prove$+-fn (term
                   hints
                   instructions
                   otf-flg
                   step-limit ; don't support time-limit because that's not portable
                   state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (natp step-limit)
                                  (null step-limit)))
                  :mode :program
                  :stobjs state))
  (mv-let (erp val state)
    (prove$ term
            :hints hints
            :instructions instructions
            :otf-flg otf-flg
            :ignore-ok t ; okay to have ignored let-vars
            :step-limit step-limit)
    (if erp
        (mv erp nil nil state)
      ;; no error (but may have failed to prove):
      (let* ((prover-steps (prover-steps-counted state))
             ;; replace nil, which can happen for very trivial theorems, with 0:
             (prover-steps (or prover-steps 0)))
        (if val
            ;; proved:
            (progn$ (cw "Proved it in ~x0 steps.~%" prover-steps)
                    (mv nil t nil state))
          ;; failed to prove:
          (if (not (natp prover-steps))
              ;; negative prover-steps means reached the step limit
              (progn$ (cw "Failed to prove (step limit reached).~%" prover-steps)
                      (mv nil nil :step-limit-reached state))
            (progn$ (cw "Failed to prove (unknown reason).~%" prover-steps)
                    (mv nil nil :unknown state))))))))

;; Returns (mv erp provedp failure-info state).
(defmacro prove$+ (term
                   &key
                   (hints 'nil)
                   (instructions 'nil)
                   (otf-flg 'nil)
                   (step-limit 'nil))
  `(prove$+-fn ,term ,hints ,instructions ,otf-flg ,step-limit state))
