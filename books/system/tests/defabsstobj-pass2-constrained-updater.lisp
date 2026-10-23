; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also defabsstobj-pass2-constrained-exec.lisp.

(in-package "ACL2") ; added by Matt K. to make this a certifiable book

; ISSUE B18 (see B18-a).  Example B18-b: the constrained signature function is
; the :EXEC function of the updater (a stobj-returning function).  After the
; encapsulate it is attached to a function that ignores the new value, so
; executing (fld (update-fld 3 st)) gives 0 although logically it is 3.  (With
; :corr-fn-exists t, attachments are disallowed only for ancestors of the
; recognizer and the correspondence function; the :EXEC function of a producer
; is not among them.)
; EXPECT-AFTER-FIX: the ENCAPSULATE fails in pass 2 ("The following events must be
; admitted before the given defabsstobj event"), so the defattach, k11 and the
; meta rule are rejected and no CONTRADICTION is proved.
(defstobj st$c (fld$c :type integer :initially 0))
(defun st$ap (x) (declare (xargs :guard t) (ignore x)) t)
(defun create-st$a () (declare (xargs :guard t)) 0)
(defun fld$a (x) (declare (xargs :guard t)) (ifix x))
(defun update-fld$a (v x) (declare (xargs :guard (integerp v)) (ignore x)) v)
(defun st$corr (st$c x) (declare (xargs :stobjs st$c :guard t)) (equal (fld$c st$c) (ifix x)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(encapsulate (((hu * st$c) => st$c :formals (v st$c) :guard (integerp v)))
  (local (defun hu (v st$c) (declare (xargs :stobjs st$c :guard (integerp v))) (update-fld$c v st$c)))
  (local (defthm create-st{correspondence} (st$corr (create-st$c) (create-st$a)) :rule-classes nil))
  (local (defthm create-st{preserved} (st$ap (create-st$a)) :rule-classes nil))
  (local (defthm fld{correspondence} (implies (st$corr st$c st) (equal (fld$c st$c) (fld$a st))) :rule-classes nil))
  (local (defthm update-fld{correspondence}
           (implies (and (st$corr st$c st) (integerp v)) (st$corr (hu v st$c) (update-fld$a v st)))
           :rule-classes nil))
  (local (defthm update-fld{preserved} (implies (and (st$ap st) (integerp v)) (st$ap (update-fld$a v st))) :rule-classes nil))
  (defabsstobj st :foundation st$c
    :recognizer (stp :logic st$ap :exec st$cp)
    :creator (create-st :logic create-st$a :exec create-st$c)
    :corr-fn st$corr :corr-fn-exists t
    :exports ((fld :logic fld$a :exec fld$c) (update-fld :logic update-fld$a :exec hu))))
)

; The rest was commented out by Matt K. since the defabsstobj above now fails.
#|
(defun hu-noop (v st$c) (declare (xargs :stobjs st$c :guard (integerp v)) (ignore v)) st$c)
(defattach hu hu-noop)
(defun k11 () (declare (xargs :guard t))
  (with-local-stobj st (mv-let (v st) (let ((st (update-fld 3 st))) (mv (fld st) st)) v)))
(k11)                                                               ; => 0 at the top level
(defthm k11-is-3 (equal (k11) 3) :rule-classes nil)                 ; but this is a theorem
(defun kk (x) (declare (ignore x)) (k11))
(defevaluator mev mev-lst ((kk x)))
(defun mf (term)
  (declare (xargs :guard t))
  (if (and (consp term) (eq (car term) 'kk) (consp (cdr term)) (null (cddr term)))
      (list 'quote (k11))
    term))
(defthm mf-correct
  (equal (mev term a) (mev (mf term) a))
  :rule-classes ((:meta :trigger-fns (kk))))
(defthm bad68 (equal (kk 3) 0) :rule-classes nil :hints (("Goal" :in-theory (disable (:d kk) (:e kk)))))
(defthm bad69 (equal (kk 3) 3) :rule-classes nil :hints (("Goal" :in-theory (disable mf-correct (:e kk) (:e k11)))))
(defthm contradiction68 nil :rule-classes nil :hints (("Goal" :use (bad68 bad69))))
|#
