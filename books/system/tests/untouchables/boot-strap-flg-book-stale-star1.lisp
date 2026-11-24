; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-12: Same flag set inside make-event leaves a stale *1*-O< (certifiable book route)
; ACL2 Soundness Review, issue S-12.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
; This file certifies as a book; including the certified book proves nil.
;
; SG1 candidate (soundness, same_as S-12): certifiable-book route for S-12.
; Inside a make-event expansion, (assign boot-strap-flg t) and then redefine
; O< (a chk-new-name-lst name, so chk-just-new-name accepts it as "new" during
; "pass 1 of the boot-strap").  add-trip (interface-raw.lisp) then takes its
; boot-strap pass-1 branch: it does not touch raw O<, but installs a new
; *1*-O< WITHOUT pushing the old one on the *undo-stack*.  make-event restores
; the state globals and reverts the world, yet *1*-O< keeps the fake body,
; which is used whenever the guard (o<g x)/(o<g y) fails.  Ground evaluation
; of (o< 'a 'b) is then T while the real definition gives NIL.
; Certifies with cert.pl, no trust tags; (include-book ...) of the certified
; book in a fresh session yields theorem BAD = NIL.  Verified on master 21aaad6
; with SBCL and CCL 1.13 (certify + include, and plain LD).
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(must-fail
(make-event
 (er-progn (assign boot-strap-flg t) ; fails: untouchable variable
           (defun o< (x y)
             (declare (xargs :guard (and (o<g x) (o<g y)) :verify-guards nil))
             (declare (ignore x y))
             t)
           (value '(value-triple :done))))
)

; The following are commented out since the event just above now fails.
#|
(defthm o<-a-b-exec (equal (o< 'a 'b) t) :rule-classes nil)
(defthm o<-a-b-logic (equal (o< 'a 'b) nil)
  :hints (("Goal" :in-theory (disable (:e o<)))) :rule-classes nil)
(defthm bad nil :hints (("Goal" :use (o<-a-b-exec o<-a-b-logic))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
