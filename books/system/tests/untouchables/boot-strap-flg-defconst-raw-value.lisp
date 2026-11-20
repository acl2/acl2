; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-12: Same flag lets defconst take a raw Lisp value (top level)
; ACL2 Soundness Review, issue S-12.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; SG1 candidate (soundness): third mechanism behind the touchable state global
; boot-strap-flg (issue S-12).  When (f-get-global 'boot-strap-flg state) is
; true, the #-acl2-loop-only code of defconst-val (other-events.lisp ~126)
; ignores the defconst form and returns the existing raw-Lisp symbol-value of
; the name (it only checks that the name is boundp).  ACL2's own raw-Lisp
; implementation binds many *...* variables that are not ACL2 constants, e.g.
; memoize-raw.lisp's *FLOAT-TICKS/SECOND*, a single-float.  So
; (defconst *float-ticks/second* 0) installs a float -- a non-ACL2 object --
; as the logical value of the constant.  Type reasoning then believes it is a
; CHARACTERP (the type-set of a bad object), while evaluation of CHARACTERP
; says no.  Neither chk-just-new-name nor redefinition is involved, so this is
; a different check bypassed than in boot-strap-flg.lisp.
; Plain LD at the top level, no ttag; verified on master 21aaad6 with SBCL and
; CCL 1.13.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; Note: The make-event wrapper below was added (inside the must-fail
; wrapper) because the original form is not an event, and hence would not be
; legal in a book.
(must-fail
(make-event
 (er-progn
  (assign boot-strap-flg t) ; fails: untouchable variable
  (value '(value-triple :ok))))
)

; The following are commented out since the event just above now fails.
#|
(defconst *float-ticks/second* 0)
(assign boot-strap-flg nil)
(defthm ft-char (characterp *float-ticks/second*) :rule-classes nil)
(defthm ft-not-char (not (characterp *float-ticks/second*))
  :hints (("Goal" :in-theory (disable (:e characterp)))) :rule-classes nil)
(defthm bad nil :hints (("Goal" :use (ft-char ft-not-char))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
