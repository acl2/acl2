; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a bug in ACL2 Version 8.7 fixed before ACL2 Version 8.8.

; Finding 64: a function ACL2 PROVES is the identity mutates a global stobj,
; because the *wormholep* check runs after the destructive write.
;
; THE WAY IN: wormhole1 (axioms.lisp:26465) is :COMMON-LISP-COMPLIANT,
; :logic-mode and NOT untouchable -- measured, (symbol-class 'wormhole1 (w state))
; is :COMMON-LISP-COMPLIANT and (logicp 'wormhole1 (w state)) is T, while its
; sibling wormhole-p IS untouchable.  So it is callable from a guard-verified
; body, and ACL2 reports of the caller "the type of BUMP-GV is described by the
; theorem (EQUAL (BUMP-GV X) X)".  The blocker this review previously recorded
; for this item -- that an updating with-global-stobj "cannot be reached from a
; wormhole because it returns state" -- is true of wormhole-eval and false of
; wormhole1.
;
; THREE PROTECTIONS FAIL TOGETHER:
;  1. oneify's generated wormhole guard (interface-raw.lisp:2595-2599) is emitted
;     only when (set-difference-eq stobjs-out '(nil :df state)) is non-empty.  An
;     updating with-global-stobj function has stobjs-out = (state), so it never
;     receives the guard at all.
;  2. When that function is GUARD-VERIFIED, *1*fn returns straight into raw Lisp,
;     so the per-updater *1* guards inside the body are never reached either.
;     This is the entire difference between the attack and the control below.
;  3. write-user-stobj-alist-raw's own *wormholep* test is the first clause of
;     that function (boot-strap-pass-2-a.lisp:1488-1492) -- but that function is
;     the LAST form of with-global-stobj-fn1's expansion
;     (translate.lisp:19803-19824), so <body>'s stobj updaters have already
;     mutated the live object and wormhole-er's throw cannot undo it.
;
; Typed and array fields are mutated too, so this is not limited to untyped
; slots.  By contrast the WORLD is properly protected: a defthm nil admitted
; inside the wormhole with ld-skip-proofsp t enters the world there and is
; completely reverted on exit.  In-place stobj mutation is the thing with no undo
; form, which is exactly why the check there has to be early.
;
; POLARITY: the ASSERT-EVENT states the CORRECT behaviour -- neither call may
; change the field, because both are proved equal to the identity and both run
; inside a wormhole.  RED while present (the field reads 42 after the
; guard-verified call), GREEN once the check is moved before the write.
;
; NOTE ON THE CONTROL: BUMP-NG is the nearest variant that is already correct --
; the identical update in a function with :verify-guards nil has
; *1*update-gfld's (when *wormholep* (wormhole-er ...)) fire BEFORE any mutation.
; It appears as the third component below, which must stay equal to the second.
(in-package "ACL2")

(defstobj gs (gfld :initially 0))

(defun readit (state)
  (declare (xargs :stobjs state))
  (with-global-stobj gs (gfld gs)))

; guard-verified: gets neither the oneify wormhole guard (stobjs-out is (state))
; nor the per-updater guards (guard verification bypasses *1*).
(defun setit-gv (state)
  (declare (xargs :stobjs state))
  (with-global-stobj gs (gs) (update-gfld 42 gs)))

; NOT guard-verified: *1*update-gfld's wormhole check fires before any mutation.
(defun setit-ng (state)
  (declare (xargs :stobjs state :verify-guards nil))
  (with-global-stobj gs (gs) (update-gfld 99 gs)))

(defun bump-gv (x)
  (declare (xargs :guard t))
  (prog2$ (wormhole1 'wgv nil '(pprogn (setit-gv state) (value :d)) nil) x))
(defun bump-ng (x)
  (declare (xargs :guard t))
  (prog2$ (wormhole1 'wng nil '(pprogn (setit-ng state) (value :d)) nil) x))

; ACL2 proves both are the identity.  This must stay provable -- it is the point.
(defthm both-are-the-identity
  (and (equal (bump-gv x) x)
       (equal (bump-ng x) x))
  :rule-classes nil)

(make-event
 (let* ((v0 (readit state))
        (i1 (bump-gv 7))
        (v1 (readit state))
        (i2 (bump-ng 7))
        (v2 (readit state)))
   (declare (ignore i1 i2))
   (prog2$ (cw "~%new-88: gfld initial=~x0 ; after guard-verified=~x1 ~
                ; after non-guard-verified control=~x2~%"
               v0 v1 v2)
           (value (list 'defconst '*measured* (list 'quote (list v0 v1 v2)))))))

; THE DEFECT.  Correct behaviour is (0 0 0): a function proved equal to the
; identity, run inside a wormhole, must not change a global stobj.  Measured
; today: (0 42 42) -- the guard-verified call wrote 42, and the control's 99 was
; correctly refused, which is why the third component equals the second.
(assert-event (equal *measured* '(0 0 0)))
