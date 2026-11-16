; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

(in-package "ACL2") ; Added by Matt K. to make the book certifiable.

; ISSUE B28 (translate.lisp collect-global-stobjs ~19724-19764): the 'global-stobjs property
; under-approximates the set of stobjs read by WITH-GLOBAL-STOBJ.  After the first
; read-user-stobj-alist (or write-user-stobj-alist) call is processed, the symbol
; READ-USER-STOBJ-ALIST is pushed onto fns-seen, and the (member-eq fn fns-seen) test that comes
; first in the cond then skips every later read-user-stobj-alist call in the same body.  So a
; function whose body reads global ST1 and then global ST2 records only ST1.  The invariants
; (R1R), (R1U) and (R2) of the Essay on the Design of With-global-stobj are computed from that
; property, so a top-level (here: clause-processor) call that returns ST2 and reads global ST2
; mid-way through updating it is not refused -- exactly the aliasing those invariants exist to
; prevent.  Raw Lisp reads the destructively updated value; the logic reads the old one.
(defstobj st1 f1)
(defstobj st2 f2)
(defevaluator evl evl-lst ((if x y z)))
(defun cp (cl hint st2 state)
  (declare (xargs :stobjs (st2 state) :guard t) (ignore hint))
  (let* ((v1 (with-global-stobj st2 (f2 st2)))   ; dropped from the 'global-stobjs property
         (st2 (update-f2 (cons v1 v1) st2))      ; raw Lisp: the live global ST2 changes here
         (v2 (with-global-stobj st2 (f2 st2)))   ; dropped; raw sees (v1 . v1), logic sees v1
         (v0 (with-global-stobj st1 (f1 st1))))  ; the one read that IS recorded: the traversal
    (declare (ignore v0))                        ; is body-first, so the innermost read wins
    (if (equal v1 v2)
        (mv nil (list cl) st2 state)               ; logically always: the identity processor
      (mv nil nil st2 state))))                    ; raw Lisp: no clauses => goal "proved"
(value-triple (cw "global-stobjs of cp = ~x0~%" (getpropc 'cp 'global-stobjs nil (w state))))
(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a)
                (evl (conjoin-clauses (clauses-result (cp cl hint st2 state))) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

; EXPECT-AFTER-FIX: (getpropc 'cp 'global-stobjs) is ((ST1 ST2)) (or ((ST2 ST1))), the hint below is
; refused ("The stobj ST2 is returned ... yet is bound by a WITH-GLOBAL-STOBJ form") and the
; proof fails.
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction nil :rule-classes nil
  :hints (("Goal" :clause-processor (cp clause nil st2 state))))
)
