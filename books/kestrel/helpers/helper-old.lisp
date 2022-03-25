; A helper that can generate simple proof hints
;
; Copyright (C) 2021-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; To use this tool, include this book and also do:
;; (adjust-ld-history t state)
;; to tell ACL2 to save the full command history.

;; TODO: Have this tool try much harder to create hints that work.  (Currently,
;; it just tries enabling functions from the goal one at a time.)  For example,
;; try enabling pairs of functions from the goal.

;; TODO: Don't try enabling functions that are already enabled.

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "tools/prove-dollar" :dir :system)

;; Returns (mv erp proved hints state).
(defun try-enabling-functions (fns claim state)
  (declare (xargs :guard (symbol-listp fns)
                  :mode :program
                  :stobjs state))
  (if (endp fns)
      (mv nil nil nil state)
    (b* ((fn (first fns))
         (hints-to-try `(("Goal" :in-theory (enable ,fn))))
         (- (cw "(Trying :hints ~x0..." hints-to-try))
         ((mv erp provedp state)
          (prove$ claim :hints hints-to-try :ignore-ok t :step-limit 10000))
         ((when erp) (mv erp nil nil state)))
      (if provedp
          (prog2$ (- (cw "Success!)~%" hints-to-try))
                  (mv nil t hints-to-try state))
        (prog2$ (- (cw "Failed.)~%" hints-to-try))
                (try-enabling-functions (rest fns) claim state))))))

;; Returns (mv erp provedp hints state) where if HINTS is nil, then no hints were found.
(defun try-to-find-hints-for-claim (claim state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((wrld (w state))
       (translated-claim (translate-term claim 'try-to-find-hints-for-claim wrld))
       (claim-fns (all-fnnames translated-claim))
       ((mv erp provedp hints state) (try-enabling-functions claim-fns claim state))
       ((when erp) (mv erp nil nil state))
       ((when provedp)
        (mv nil t hints state)))
    (mv nil nil nil state)))

;; Returns (mv erp event state).
;; The purpose of this is to print :hints that are likely to prove the last theorem that the user attempted.
(defun helper-old-fn (state)
  (declare (xargs :mode :program
                  :stobjs state))
  (b* ((- (and (not (multiple-ld-history-entry-modep state))
               (cw "WARNING: This tool can not see the full command history.  Execute (adjust-ld-history t state) to enable that.")
               ))
       (state (set-print-case :downcase state)) ; make all printing downcase
       (most-recent-theorem (most-recent-theorem state)) ; can this be a defrule?
       (theorem-type (car most-recent-theorem))
       (body (if (eq 'thm theorem-type)
                 (second most-recent-theorem)
               (third most-recent-theorem) ; for defthm
               ))
       (name (if (eq 'thm theorem-type)
                 "the thm"
               (symbol-name (second most-recent-theorem)) ; for defthm
               ))
       ((mv erp provedp hints-found state)
        (try-to-find-hints-for-claim body state))
       ((when erp) (mv erp nil state)))
    (if provedp
        (prog2$ (cw "~%To prove ~s0, try:~%~%:hints ~x1~%~%" name hints-found)
                (mv nil '(value-triple :invisible) state))
      ;; Failed (no hints found):
      (mv nil ; not an error, just failed to find hints
          `(value-triple (cw "No hints found for ~s0.~%" ',name) :on-skip-proofs :interactive) ; see cw-event
          state))))

;; To invoke the helper tool (to try to produce hints sufficient to prove the
;; last theorem entered by the user, just do ":h").
(defmacro h-old ()
  '(make-event-quiet (helper-old-fn state)))

;; ;; Test:
;; (adjust-ld-history t state)
;; (defund double-list (x) (if (endp x) nil (cons (* 2 (first x)) (double-list (rest x)))))
;; (defthm integer-listp-of-double-list (implies (integer-listp x) (integer-listp (double-list x))))
;; :h
