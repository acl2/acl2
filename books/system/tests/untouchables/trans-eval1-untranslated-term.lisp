; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-221 (lead F1-6588, stage-2 batch G76): the touchable trans-eval1 evaluates an untranslated term on the live
; state.  Proves nil at the top level (plain ld), no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
; For the certified-book route see two-session/S-221-trans-eval1-raw-mode/.
;
; G76 candidate (soundness): proof of nil at the top level, no trust tags.
; trans-eval1 (translate.lisp) is NOT untouchable.  It takes an
; already-"translated" term and a caller-supplied stobjs-out, checks only
; that the term's free variables are global stobj names, and passes it to the
; untouchable ev-for-trans-eval, which evaluates it with EV on the live state.
; Its only caller in the sources, trans-eval0, gives it the output of
; translate; a direct call skips translation, so no untouchable or stobj check
; is made.  Below the term sets the untouchable state globals
; temp-touchable-fns/vars to T; then set-w! installs a world in which BAD-THM
; is a "theorem" with formula NIL.  (A caller-supplied stobjs-out that omits a
; returned stobj also lets the live stobj escape replace-stobjs.)
; Control: the same form through trans-eval is refused (State global variable
; TEMP-TOUCHABLE-FNS has been rendered untouchable).
; Book route: directory G76-trans-eval1-raw-mode/ (two fresh sessions:
; (ld "cert.lisp") certifies bk.lisp with no trust tags, (ld "inc.lisp")
; proves NIL and prints NIL-PROVED): a make-event calls trans-eval1 on
; (put-global 'acl2-raw-mode-p 't state), which protect-system-state-globals
; does not restore, so certify-book reads (defthm b-a-d nil) in raw Lisp.
; Same class as the G73 candidates G73-xtrans-eval-raw-mode.lisp and
; G73-eval-clause-processor-raw-mode.lisp (the other touchable caller of
; ev-for-trans-eval); trans-eval1 needs its own untouchable entry.
; Verified 2026-10-21: top level and book on 947ff84343 (new5 SBCL, CCL) and
; 21aaad6 (acl2-sbcl, acl2-ccl).
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; Note: The make-event wrapper below was added (inside the must-fail
; wrapper) because the original form is not an event, and hence would not be
; legal in a book.
(must-fail
(make-event
 (er-progn
  (trans-eval1 '(put-global 'temp-touchable-fns 't ; fails: untouchable function
                            (put-global 'temp-touchable-vars 't state))
               '(state) 'top (w state) state t nil)
  (value '(value-triple :ok))))
)

; The following are commented out since the event just above now fails.
#|
(set-w! (putprop 'bad-thm 'theorem ''nil (w state)) state)
(defthm nil-proved nil :rule-classes nil :hints (("Goal" :use bad-thm)))

(value-triple (cw "~%NIL-PROVED~%"))
|#
