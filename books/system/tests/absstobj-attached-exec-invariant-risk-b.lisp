; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also
; absstobj-attached-exec-invariant-risk-b.lisp.

; S-21 (route: an abstract-stobj export whose :exec is a constrained function gets no invariant-risk when a risky function is attached to it later).
; Expected: proves nil (prints NIL-PROVED); no trust tags; SBCL and CCL.
;
; G138 (lead F1-4253.A): further evidence for S-21 (and S-168), through an
; abstract stobj export.  put-defabsstobj-invariant-risk copies invariant-risk
; from each export's :EXEC function once, at defabsstobj time.  Here the :EXEC
; of SSET is the constrained UPD$C (no invariant-risk; constrained functions
; never get any), the lemmas follow from UPD$C's exported constraints, and
; :CORR-FN-EXISTS T leaves UPD$C attachable.  (defattach upd$c h) then installs
; H, whose invariant-risk is UPDATE-FLD, but SSET and its :program caller stay
; risk-free ((:SSET NIL :H UPDATE-FLD) is printed), so (prog-set "abc" st) runs
; H raw outside its guard and stores "abc" in a field of type (integer 0 *);
; a clause processor reading the live stobj then proves (natp "abc").
; ld proves nil on SBCL and CCL at 16dbd4bd56 (new6) and 21aaad6.  No trust tags.
(in-package "ACL2")
(defstobj st$c (fld :type (integer 0 *) :initially 0))
(encapsulate
  (((upd$c * st$c) => st$c :formals (v st$c) :guard (natp v)
    :invariant-risk t ; added by Matt K.
    ))
  (local (defun upd$c (v st$c)
           (declare (xargs :stobjs st$c :guard (natp v)))
           (update-fld v st$c)))
  (defthm upd$c-fld
    (implies (natp v) (equal (fld (upd$c v st$c)) v)))
  (defthm upd$c-st$cp
    (implies (and (natp v) (st$cp st$c)) (st$cp (upd$c v st$c)))))
(defun st$ap (a) (declare (xargs :guard t)) (natp a))
(defun create-st$a () (declare (xargs :guard t)) 0)
(defun get$a (a) (declare (xargs :guard (st$ap a))) (nfix a))
(defun set$a (v a) (declare (xargs :guard (and (natp v) (st$ap a))) (ignore a)) v)
(defun st$corr (st$c a) (declare (xargs :stobjs st$c :verify-guards nil))
  (and (st$cp st$c) (equal (fld st$c) a)))
(defthm create-st{correspondence} (st$corr (create-st$c) (create-st$a)))
(defthm create-st{preserved} (st$ap (create-st$a)))
(defthm sget{correspondence}
  (implies (and (st$corr st$c st) (st$ap st)) (equal (fld st$c) (get$a st))))
(defthm sset{correspondence}
  (implies (and (st$corr st$c st) (natp v) (st$ap st))
           (st$corr (upd$c v st$c) (set$a v st))))
(defthm sset{preserved}
  (implies (and (natp v) (st$ap st)) (st$ap (set$a v st))))
(defabsstobj st
  :recognizer (stp :logic st$ap :exec st$cp)
  :creator (create-st :logic create-st$a :exec create-st$c)
  :corr-fn st$corr :corr-fn-exists t
  :exports ((sget :logic get$a :exec fld) (sset :logic set$a :exec upd$c :protect t)))
(defun h (v st$c)
  (declare (xargs :stobjs st$c :guard (natp v)))
  (update-fld v st$c))
(defattach upd$c h)
(value-triple (list :sset (getpropc 'sset 'invariant-risk) :h (getpropc 'h 'invariant-risk)))
(defun prog-set (v st)
  (declare (xargs :mode :program :stobjs st))
  (sset v st))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(make-event (let ((st (prog-set "abc" st))) (mv nil '(value-triple :ok) state st)))
)

; Added by Matt K.
(assert-event (equal (sget st) 0))

; The following events were commented out by Matt K. since the make-event just
; above now fails.  See also absstobj-attached-exec-invariant-risk-a.lisp.
#|
(defevaluator my-ev my-ev-lst ((natp x) (not x) (if x y z)))
(defun my-cp (clause hint st)
  (declare (xargs :stobjs st :guard t) (ignore hint))
  (mv nil (list (cons `(not (natp (quote ,(sget st)))) clause)) st))
(defthm my-cp-correct
  (implies (and (pseudo-term-listp clause) (alistp a)
                (my-ev (conjoin-clauses (clauses-result (my-cp clause hint st))) a))
           (my-ev (disjoin clause) a))
  :rule-classes :clause-processor)
(defthm natp-abc (natp "abc")
  :hints (("Goal" :clause-processor (my-cp clause nil st))) :rule-classes nil)
(defthm nil-proved nil :rule-classes nil :hints (("Goal" :use natp-abc)))

(value-triple (cw "~%NIL-PROVED~%"))
|#
