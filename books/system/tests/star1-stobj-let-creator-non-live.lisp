; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; B26-a: the *1* code for a stobj-let binding of a stobj-table entry,
; (kid (tb-get 'kid par (create-kid)) tb-put), is built by oneified-stobj-let-actuals
; (interface-raw.lisp) as (or (*1*tb-get 'kid par nil) (create-kid)): the RAW creator is called
; even when the parent is not a live stobj.  When the prover evaluates (f '(nil)) through the
; executable counterpart, the raw child (a Lisp vector) is updated in place and stored by
; *1*tb-put into the logical (list) parent, so the value returned to the prover is
; (((KID . #(5)))) -- not an ACL2 object -- while the definition gives (((KID 5))).

(in-package "ACL2") ; 

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(defstobj kid (kf :type integer :initially 0))
(defstobj par (tb :type (stobj-table)))
(defun f (par) (declare (xargs :stobjs par :verify-guards nil))
  (stobj-let ((kid (tb-get 'kid par (create-kid)) tb-put)) (kid) (update-kf 5 kid) par))
(defthm by-definition (equal (f '(nil)) '(((kid 5)))) :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e f)))))

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm by-execution (not (equal (f '(nil)) '(((kid 5))))) :rule-classes nil
  :hints (("Goal" :in-theory '((:e f) (:e equal) (:e not)))))
)

; EXPECT-AFTER-FIX: the executable counterpart of F refuses a non-live parent (creator error), so
; by-execution fails.
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction nil :rule-classes nil :hints (("Goal" :use (by-definition by-execution))))
)
