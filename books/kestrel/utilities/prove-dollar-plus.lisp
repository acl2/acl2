; An interface to prove$ that indicates whether a step limit was reached.
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add a way to return the failed subgoals
;; TODO: Add a version that returns the runes used (see get-event-data)

;(include-book "tools/prove-dollar" :dir :system)
(include-book "prove-dollar-nice")

;; Returns (mv erp provedp failure-info state), where failure-info may be
;; :step-limit-reached, :time-limit-reached, or :unknown.
;; TODO: How to determine if the time-limit was reached?
(defun prove$+-fn (term ; untranslated (todo: optimize if known to be translated?)
                   hints
                   instructions
                   otf-flg
                   step-limit ; warning: not sufficient to interrupt certain prover operations, such as subsumption
                   time-limit ; warning: not portable
                   print
                   state)
  (declare (xargs :guard (and (booleanp otf-flg)
                              (or (natp step-limit)
                                  (null step-limit))
                              (or (rationalp time-limit)
                                  (null time-limit)))
                  :mode :program ; because this (ultimately) calls the prover
                  :stobjs state))
  (mv-let (erp provedp state)
    (prove$-nice term
                 :hints hints
                 :instructions instructions
                 :otf-flg otf-flg
                 :step-limit step-limit
                 :time-limit time-limit)
    (if erp
        (mv erp nil nil state)
      ;; no error (but may have failed to prove):
      (let ((prover-steps (last-prover-steps$ state)))
        (if provedp
            (progn$ (and print (cw "Proved it in ~x0 steps.~%" prover-steps))
                    (mv nil t nil state))
          ;; failed to prove:
          (if (not (natp prover-steps))
              ;; negative prover-steps means the step limit was reached:
              (progn$ (and print (cw "Failed to prove (step limit of ~x0 reached).~%" step-limit))
                      (mv nil nil :step-limit-reached state))
            (if (member-eq 'time-limit-reached (get-event-data 'abort-causes state))
                (progn$ (and print (cw "Failed to prove (time limit of ~x0 reached).~%" time-limit))
                        (mv nil nil :time-limit-reached state))
              ;; todo: can we detect whether the rewrite stack limit was reached?
              (progn$ (and print (cw "Failed to prove (unknown reason).~%" prover-steps))
                      (mv nil nil :unknown state)))))))))

;; Returns (mv erp provedp failure-info state), where failure-info may be
;; :step-limit-reached, :time-limit-reached, or :unknown.
(defmacro prove$+ (term
                   &key
                   (hints 'nil)
                   (instructions 'nil)
                   (otf-flg 'nil)
                   (step-limit 'nil)
                   (time-limit 'nil)
                   (print 't) ; todo: change default to nil?
                   )
  `(prove$+-fn ,term ,hints ,instructions ,otf-flg ,step-limit ,time-limit ,print state))

;; Tests:
;; (prove$+ '(equal (car (cons x y)) x))
;; (prove$+ '(equal (car (cons x y)) x) :step-limit 6)
