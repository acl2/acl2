; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-64: CCL: princ$ doubles backslashes in symbol names under print-case :downcase
; ACL2 Soundness Review, issue S-64.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with CCL 1.13 only (on SBCL the final theorem fails); no trust tags; certifies.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; CCL only: raw princ$ of a symbol whose name contains a backslash, with
; print-case :downcase, writes each backslash twice, while the logical
; definition of princ$ writes (string-downcase (symbol-name x)).
;
; CCL 1.13 itself: (let ((*print-escape* nil) (*print-case* :downcase))
;                    (princ-to-string '|A\\b|))  ==> "a\\\\b" (4 characters),
; whereas with *print-case* :upcase it gives "A\\b" (3 characters).
;
; A verified clause processor that takes STATE can observe the raw output on
; the live state, so it proves NIL.
;
; Tested at ACL2 master 21aaad6:
;   CCL 1.13:  certifies with cert.pl (no trust tags); CONTRADICTION proves,
;              and (include-book ...) followed by (thm nil :hints (("Goal"
;              :use contradiction))) proves NIL in a fresh session.
;   SBCL:      CP-CORRECT proves, CONTRADICTION fails (SBCL prints a\b).

(in-package "ACL2")

(defevaluator evl evl-list ((if a b c)))

(defun cp (cl hint state)
  (declare (xargs :stobjs state :verify-guards nil)
           (ignore hint))
  (let ((state (set-print-case :downcase state)))
    (mv-let (chan state)
      (open-output-channel :string :character state)
      (if (null chan)
          (mv nil (list cl) state)
        (let ((state (princ$ '|A\\b| chan state)))
          (mv-let (erp s state)
            (get-output-stream-string$-fn chan state)

; Logically s is "a\\b" (3 characters), so the clause list is always (list cl).
; In CCL the live string has 4 characters, so no clauses are returned.

            (mv nil
                (if (and (not erp) (stringp s) (equal (length s) 4))
                    nil
                  (list cl))
                state)))))))

(defthm cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses (clauses-result (cp cl hint state))) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction nil
  :hints (("Goal" :clause-processor (cp clause nil state)))
  :rule-classes nil)
)

; The following was commented out by Matt K. since the event just above now
; fails.
; (value-triple (cw "~%NIL-PROVED~%"))
