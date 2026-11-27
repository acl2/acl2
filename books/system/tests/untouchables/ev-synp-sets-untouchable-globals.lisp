; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-196 (lead F1-5341, stage-2 batch G54): the touchable ev-synp evaluates an untranslated term on the
; live state, so a top-level call can set the untouchable globals temp-touchable-fns and temp-touchable-vars.
; Proves nil at the top level (plain ld, no trust tags): SBCL and CCL at 21aaad6, 9a589490e6 and 15e42ee881.
; Control: with a harmless term in place of the put-global calls, set-w! is refused.
;
; G54 (lead F1-5341.A): the touchable EV-SYNP evaluates any list structure it is
; given with EV on the live state.  Without any RETURN-LAST call (so the S-39
; root fix, checking return-last keys in EV-REC, would not block it), the term
; below sets the untouchable state globals temp-touchable-fns and
; temp-touchable-vars, after which the untouchable SET-W! installs a theorem NIL.
; Top level (plain ld) only: make-event would restore the globals.
; Proves nil (plain ld) on SBCL and CCL at 9a589490e6 (/work/acl2-new3) and 21aaad6.
; Control: G54-ev-synp-put-global-untouchable-control.lisp (harmless term; set-w! refused).
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(value-triple (f-get-global 'temp-touchable-fns state))
; Note: The value-triple wrapper below was added (inside the must-fail
; wrapper) because the original form is not an event, and hence would not be
; legal in a book.
(must-fail
(value-triple
 (mv-let (erp val latches)
   (ev-synp '(quote (if mfc ; fails: untouchable function
                        (if (put-global 'temp-touchable-fns 't
                                        (put-global 'temp-touchable-vars 't state))
                            't 't)
                      't))
            nil 'fake-mfc 'syntaxp nil state)
   (declare (ignore latches))
   (list erp val)))
)

; The following are commented out since the event just above now fails.
#|
(value-triple (f-get-global 'temp-touchable-fns state))
(set-w! (putprop 'bad0 'theorem *nil* (w state)) state)
(defthm nil-proved nil :hints (("Goal" :use bad0)) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
