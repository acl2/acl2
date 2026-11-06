; This file, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  It is not a certifiable book, because of the LD
; call below.  But you can successfully LD this file to completion.

; S-1 (route: a define-pc-macro calls verify-fn during a defthm's :instructions replay; the nested session's goal-free stack replaces the enclosing one; certifiable).
; Expected: proves nil (prints NIL-PROVED); no trust tags; certifies; SBCL and CCL.
;
; Proof of nil, no trust tags; certifies.  Batch G146, lead F1-4724.A
; (same_as S-1).
;
; VERIFY-FN, the function behind the VERIFY macro, is touchable and calls the
; untouchable PC-TOP, which installs a fresh proof-builder goal stack
; (install-initial-state-stack) and runs the given instructions on it.  Its only
; guard against nesting is the test of the state global IN-VERIFY-FLG, but that
; flag is nil while a defthm's :INSTRUCTIONS are replayed (pc-main is called
; with in-verify-flg nil), so a user proof-builder macro run during the replay
; can call verify-fn.  Here verify-fn proves the trivial goal T and leaves that
; finished stack (no goals) in place of the enclosing run's stack; the macro
; then expands to the harmless COMMENT command, and PROOF-BUILDER reports that
; all goals of (DEFTHM BAD NIL ...) are proved.  The (:EXIT) instruction
; (no arguments) ends the nested session without reading standard input, so
; this works inside certify-book.
;
; S-1 says verify-fn "also proved nil this way at the top level"; this is the
; certifiable form.  Note for the fix: unlike state-from-instructions and
; state-stack-from-instructions, verify-fn cannot simply be made untouchable,
; since the VERIFY macro expands into a call of it; verify-fn itself must refuse
; to run while a proof-builder run is in progress (in-verify-flg does not
; detect that during :instructions replay).
;
; Proves nil by plain LD and certifies (certify-book) on SBCL and CCL at
; 16dbd4bd56 (/work/acl2-new6/saved_acl2, /work/acl2-new6/ccl-saved_acl2) and
; at 21aaad6 (acl2-sbcl, acl2-ccl).

(in-package "ACL2")

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(program)
(set-state-ok t)

(define-pc-macro clobber-vf ()
  (mv-let (erp val state)
    (verify-fn ''t t nil nil '(:prove (:exit)) state)
    (declare (ignore erp val))
    (value 'comment)))

(logic)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm nil-proved
  nil
  :rule-classes nil
  :instructions (:clobber-vf))
)

; Commented out by Matt K.:
; (value-triple (cw "~%NIL-PROVED~%"))
