; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; G508 (lead F1-696.A, set-print-escape): new route for S-64 (CCL only).
; With print-escape nil (and print-readably nil), prin1$ no longer encloses a
; symbol name containing a backslash in |...|: needs-slashes is false, so raw
; prin1$ writes the name with CCL's princ, which under print-case :downcase
; doubles each backslash, while the logical definition of prin1$ writes
; (string-downcase (symbol-name x)) through princ$.  Logically the keyword
; :|A\b| prints as the 4 characters :a\b; CCL 1.13 writes 5 (:a\\b).
; A verified clause processor that takes STATE observes this on the live state
; and proves NIL.  A sweep of 2765 atoms over print-escape {t, nil, 7} x
; print-readably x print-circle x base {10,16} x radix x case found no other
; difference (all 114 per setting are backslash names under :downcase with
; print-escape nil); SBCL agrees everywhere.
(in-package "ACL2")

(defevaluator g508-ev g508-ev-lst ((if a b c)))

(defun g508-cp (cl hint state)
  (declare (xargs :stobjs state :verify-guards nil)
           (ignore hint))
  (let* ((state (set-print-case :downcase state))
         (state (set-print-escape nil state))
         (state (set-print-readably nil state)))
    (mv-let (chan state)
      (open-output-channel :string :character state)
      (if (null chan)
          (mv nil (list cl) state)
        (let ((state (prin1$ :|A\\b| chan state)))
          (mv-let (erp s state)
            (get-output-stream-string$-fn chan state)

; Logically s is ":a\\b" (4 characters), so the clause list is always (list cl).
; In CCL the live string has 5 characters, so no clauses are returned.

            (mv nil
                (if (and (not erp) (stringp s) (equal (length s) 5))
                    nil
                  (list cl))
                state)))))))

(defthm g508-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (g508-ev (conjoin-clauses (clauses-result (g508-cp cl hint state))) a))
           (g508-ev (disjoin cl) a))
  :rule-classes :clause-processor)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm g508-contradiction nil
  :hints (("Goal" :clause-processor (g508-cp clause nil state)))
  :rule-classes nil)
)

(make-event (if (getpropc 'g508-contradiction 'theorem nil (w state))
                '(value-triple (cw "~%NIL-PROVED~%"))
              '(value-triple :not-proved)))
