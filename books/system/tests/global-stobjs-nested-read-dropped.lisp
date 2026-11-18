; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

(in-package "ACL2") ; Added by Matt K. to make the book certifiable.

; ISSUE B28, second route (translate.lisp collect-global-stobjs, used by chk-global-stobj-body):
; the same dropped-read defect defeats (R1U) directly, with no stobj formal and no top-level
; stobj at all.  An updating (with-global-stobj st2 (nil st2) body) is required to have st2
; outside GS(body); here body reads global st2 through a read-only with-global-stobj after
; destructively updating the bound st2, and that read is dropped because a read of st1 sits
; deeper in the term and is the one that gets recorded.
(defstobj st1 f1)
(defstobj st2 f2)
(defevaluator evl evl-lst ((if x y z)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defun cp (cl hint state)
  (declare (xargs :stobjs state :guard t) (ignore hint))
  (mv-let (flg state)
    (with-global-stobj st2 (nil st2)
      (let* ((v1 (f2 st2))
             (st2 (update-f2 (cons v1 v1) st2))        ; raw Lisp: the live global ST2 changes
             (v2 (with-global-stobj st2 (f2 st2)))     ; (R1U) violation, but the read is dropped
             (v0 (with-global-stobj st1 (f1 st1))))    ; the recorded read
        (declare (ignore v0))
        (mv (equal v1 v2) st2)))                        ; logic: v2 = v1 (state unchanged); raw: v2 = (v1 . v1)
    (if flg
        (mv nil (list cl) state)                       ; logically always: the identity processor
      (mv nil nil state))))                            ; raw Lisp: no clauses => goal "proved"
)

; The rest was commented out by Matt K. because it's no longer relevant.
#|
(value-triple (cw "global-stobjs of cp = ~x0~%" (getpropc 'cp 'global-stobjs nil (w state))))
(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a)
                (evl (conjoin-clauses (clauses-result (cp cl hint state))) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)
; EXPECT-AFTER-FIX: the defun of CP is refused ("The form binding stobj ST2 ... is illegal
; because its body makes a WITH-GLOBAL-STOBJ call that binds ST2") and nothing below is reached.
(defthm contradiction nil :rule-classes nil
  :hints (("Goal" :clause-processor (cp clause nil state))))
|#
