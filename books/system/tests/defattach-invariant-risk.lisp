; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-21: Attaching a stobj-updating function does not give the constrained function invariant-risk
; ACL2 Soundness Review, issue S-21.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; Proof of nil: invariant-risk is not propagated through attachments.  F is a
; constrained function (no body, hence no 'invariant-risk property); its
; attachment G updates a typed stobj field and has invariant-risk UPDATE-FLD.
; A :program-mode caller P of F gets no invariant-risk, so (p "abc" st) runs
; raw P -> raw F -> raw G with no guard check, and stores a string in the
; (integer 0 *) field of the live stobj.  A clause processor that reads the
; live stobj then proves nil.
(in-package "ACL2")

(defstobj st (fld :type (integer 0 *) :initially 0))

(defun g (v st)
  (declare (xargs :stobjs st :guard (natp v)))
  (update-fld v st))

(encapsulate
  (((f * st) => st :formals (v st) :guard (natp v)))
  (local (defun f (v st)
           (declare (xargs :stobjs st :guard (natp v)))
           (update-fld v st))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defattach f g)
)

; The following events were commented out by Matt K. since the event just above
; now fails.  See modified events that follow this comment.
#|
(defun p (v st)
  (declare (xargs :mode :program :stobjs st))
  (f v st))

(assert-event (and (getpropc 'g 'invariant-risk nil (w state))
                   (not (getpropc 'f 'invariant-risk nil (w state)))
                   (not (getpropc 'p 'invariant-risk nil (w state)))))

(make-event
 (mv-let (erp val state)
   (trans-eval '(p "abc" st) 'top state t)
   (declare (ignore erp val))
   (value '(value-triple :corrupted))))

(defevaluator evl evl-list ((if x y z)))

(defun cp (cl hint st)
  (declare (xargs :stobjs st :guard t) (ignore hint))
  (mv nil
      (if (and (stp st) (not (natp (fld st))))
          nil ; impossible: stp implies (natp (fld st))
        (list cl))
      st))

(defthm cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses (clauses-result (cp cl hint st))) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm bad nil
  :rule-classes nil
  :hints (("Goal" :clause-processor (cp clause nil st))))

(value-triple (cw "~%NIL-PROVED~%"))
|#

; The rest of this book was created by Matt Kaufmann, based on what is above,
; after introduction of the :invariant-risk keywords for signatures.

(encapsulate
  (((f2 * st) => st :formals (v st) :guard (natp v) :invariant-risk t))
  (local (defun f2 (v st)
           (declare (xargs :stobjs st :guard (natp v)))
           (update-fld v st))))

(defattach f2 g)

(defun p (v st)
  (declare (xargs :mode :program :stobjs st))
  (f2 v st))

(assert-event (and (getpropc 'g 'invariant-risk nil (w state))
                   (getpropc 'f2 'invariant-risk nil (w state))
                   (getpropc 'p 'invariant-risk nil (w state))))

(must-fail (trans-eval '(p "abc" st) 'top state t))

; Checking that the trans-eval call above did not update st:
(assert-event (equal (fld st) 0))
