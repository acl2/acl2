; This file, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  It is not a certifiable book, because of the LD
; call below.  But you can successfully LD this file to completion.

; Proof of nil at the top level (no trust tags).  The verify loop entered below
; reads its commands from the terminal, so give it EXIT: run-examples.sh sends
; the companion file S-1-pc-macro-retrieve-fn-error-save.stdin; by hand,
;   printf '(ld "S-1-pc-macro-retrieve-fn-error-save.lisp")\nexit\n' | acl2
;
; Another writer of the proof-builder goal stack named in S-1, RETRIEVE-FN
; (not untouchable), replaces the goal of a DEFTHM with an unrelated stack.
; 1. A failing :INSTRUCTIONS hint makes proof-builder-cl-proc-1 call SAVE-FN
;    itself (SAVE-FN is untouchable, but this call is system code), storing the
;    current goal stack under :ERROR1.  Here that stack has no goals left
;    (:PROVE succeeded and the following (:DV 1) failed).
; 2. A user proof-builder macro calls RETRIEVE-FN, which sets the untouchable
;    state globals behind STATE-STACK/OLD-SS to the saved stack and enters the
;    verify loop (EXIT leaves it).
; 3. DEFTHM BAD then sees an empty goal list and accepts NIL.
(in-package "ACL2")

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

; Step 1 is meant to fail; the inner LD keeps going.
(ld '((thm (equal x x)
           :hints (("Goal" :instructions (:prove (:dv 1))))))
    :ld-error-action :continue)

(program)
(set-state-ok t)
(define-pc-macro grab ()
  (er-progn (retrieve-fn :error1 state)
            (value 'comment)))
(logic)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad nil :rule-classes nil :instructions (:grab))
)

; Commented out by Matt K.:
; (value-triple (cw "~%NIL-PROVED~%"))
