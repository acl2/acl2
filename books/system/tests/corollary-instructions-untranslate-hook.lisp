; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also
; defabsstobj-pass2-constrained-updater.lisp.

(in-package "ACL2") ; added by Matt K. to make this a certifiable book

; B21-a: a :corollary proved with :instructions is handed to the proof-builder as
; (untranslate goal t wrld) and re-translated (proof-builder-a.lisp proof-builder ->
; state-stack-from-instructions -> pc-top), ignoring the translated goal.  A user
; UNTRANSLATE hook (user-defined-functions-table, no trust tag needed) makes the
; re-translated formula T, so the corollary (car x) = 3 is accepted without proof.
; EXPECT-AFTER-FIX: (defthm bad ...) fails ("unproved goal from replay"), contradiction not proved.

(defun my-untr (term iff-flg wrld) (declare (ignore term iff-flg wrld) (xargs :guard t)) t)
(table user-defined-functions-table 'untranslate 'my-untr)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defthm bad (equal (car (cons x y)) x)
  :rule-classes ((:rewrite :corollary (equal (car x) 3) :instructions (:prove))))
)

; Commented out by Matt K. since bad no longer exists:
#|
(defthm contradiction nil :rule-classes nil :hints (("Goal" :use ((:instance bad (x '(4)))))))
|#
