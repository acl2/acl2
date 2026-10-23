; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also
; defabsstobj-pass2-constrained-updater.lisp.

(in-package "ACL2") ; added by Matt K. to make this a certifiable book

; B21-d: prove-defattach-constraint (and prove-defattach-guards1) hand the proof-builder
; (untranslate goal t wrld) too, so a defattach whose constraint is false is accepted under a
; user UNTRANSLATE hook: g's constraint is (equal (g st$c) (fld$c st$c)) but g7 returns 7.  The
; attachment is then turned into a proof of nil the B18 way (g is the :exec of an abstract
; stobj export whose :logic is fld$a, so the evaluator restriction is not triggered).
; EXPECT-AFTER-FIX: (defattach (g g7) :instructions (:prove)) fails, contradiction66 not proved.
(defstobj st$c (fld$c :type integer :initially 0))
(defun st$ap (x) (declare (xargs :guard t) (ignore x)) t)
(defun create-st$a () (declare (xargs :guard t)) 0)
(defun fld$a (x) (declare (xargs :guard t)) (ifix x))
(defun update-fld$a (v x) (declare (xargs :guard (integerp v)) (ignore x)) v)
(defun st$corr (st$c x) (declare (xargs :stobjs st$c :guard t)) (equal (fld$c st$c) (ifix x)))
(encapsulate (((g st$c) => * :formals (st$c) :guard t))
  (local (defun g (st$c) (declare (xargs :stobjs st$c :guard t)) (fld$c st$c)))
  (defthm g-is-fld$c (equal (g st$c) (fld$c st$c))))
(defun g7 (st$c) (declare (xargs :stobjs st$c :guard t) (ignore st$c)) 7)
(defun my-untr (term iff-flg wrld) (declare (ignore term iff-flg wrld) (xargs :guard t)) t)
(table user-defined-functions-table 'untranslate 'my-untr)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defattach (g g7) :instructions (:prove))                      ; constraint g-is-fld$c is false for g7
)

(defthm create-st{correspondence} (st$corr (create-st$c) (create-st$a)) :rule-classes nil)
(defthm create-st{preserved} (st$ap (create-st$a)) :rule-classes nil)
(defthm fld{correspondence} (implies (st$corr st$c st) (equal (g st$c) (fld$a st))) :rule-classes nil)
(defthm update-fld{correspondence} (implies (and (st$corr st$c st) (integerp v)) (st$corr (update-fld$c v st$c) (update-fld$a v st))) :rule-classes nil)
(defthm update-fld{preserved} (implies (and (st$ap st) (integerp v)) (st$ap (update-fld$a v st))) :rule-classes nil)
(defabsstobj st :foundation st$c :recognizer (stp :logic st$ap :exec st$cp)
  :creator (create-st :logic create-st$a :exec create-st$c) :corr-fn st$corr
  :exports ((fld :logic fld$a :exec g) (update-fld :logic update-fld$a :exec update-fld$c)))
(defun k9 () (declare (xargs :guard t)) (with-local-stobj st (mv-let (v st) (mv (fld st) st) v)))
; Non-event commented out by Matt K.:
; (k9)                                                             ; => 7, but (k9) = 0 is a theorem
(defun kk (x) (declare (ignore x)) (k9))
(defevaluator mev mev-lst ((kk x)))
(defun mf (term) (declare (xargs :guard t)) (if (and (consp term) (eq (car term) 'kk) (consp (cdr term)) (null (cddr term))) (list 'quote (k9)) term))
(defthm mf-correct (equal (mev term a) (mev (mf term) a)) :rule-classes ((:meta :trigger-fns (kk))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defthm bad66 (equal (kk 3) 7) :rule-classes nil :hints (("Goal" :in-theory (disable (:d kk) (:e kk)))))
:expected :hard
)

(defthm bad67 (equal (kk 3) 0) :rule-classes nil :hints (("Goal" :in-theory (disable mf-correct (:e kk) (:e k9)))))

; Commented out by Matt K. since bad66 no longer exists:
#|
(defthm contradiction66 nil :rule-classes nil :hints (("Goal" :use (bad66 bad67))))
|#
