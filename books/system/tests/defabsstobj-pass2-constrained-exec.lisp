; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.  See also
; defabsstobj-pass2-constrained-updater.lisp.

(in-package "ACL2") ; added by Matt K. to make this a certifiable book

; ISSUE B18 (other-events.lisp defabsstobj-fn1): when ld-skip-proofsp is
; INCLUDE-BOOK -- which is also the case in pass 2 of an encapsulate -- a
; defabsstobj whose supporting theorems ({correspondence}, {preserved},
; {guard-thm}) are "missing" (e.g. because they were LOCAL) is installed
; silently.  In pass 2 of a non-trivial encapsulate the world differs from the
; world in which the local theorems were proved: a signature function can be
; the :EXEC function of an export (bogus-exported-compliants only looks at
; logical bodies/guards, and stobj-attachment-restrictions only cover ancestors
; of the recognizer and the correspondence function).  After the encapsulate
; the constrained :EXEC function can be attached to anything, so raw execution
; of the export no longer agrees with its :LOGIC function.
; Example B18-a.  Local witness h = fld$c; exported h is unconstrained; after
; (defattach h h7), (fld st) executes to 7 while logically it is (fld$a st) = 0.
; Top level: (k9) evaluates to 7 although (equal (k9) 0) is a theorem.  A
; metafunction is evaluated with attachments (aok = t), turning this into a
; proof of nil.
; EXPECT-AFTER-FIX: the ENCAPSULATE fails in pass 2 ("The following events must be
; admitted before the given defabsstobj event"), so the defattach, k9 and the
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
(encapsulate (((h st$c) => * :formals (st$c) :guard t))
  (local (defun h (st$c) (declare (xargs :stobjs st$c :guard t)) (fld$c st$c)))
  (local (defthm create-st{correspondence} (st$corr (create-st$c) (create-st$a)) :rule-classes nil))
  (local (defthm create-st{preserved} (st$ap (create-st$a)) :rule-classes nil))
  (local (defthm fld{correspondence} (implies (st$corr st$c st) (equal (h st$c) (fld$a st))) :rule-classes nil))
  (local (defthm update-fld{correspondence}
           (implies (and (st$corr st$c st) (integerp v)) (st$corr (update-fld$c v st$c) (update-fld$a v st)))
           :rule-classes nil))
  (local (defthm update-fld{preserved} (implies (and (st$ap st) (integerp v)) (st$ap (update-fld$a v st))) :rule-classes nil))
  (defabsstobj st :foundation st$c
    :recognizer (stp :logic st$ap :exec st$cp)
    :creator (create-st :logic create-st$a :exec create-st$c)
    :corr-fn st$corr
    :exports ((fld :logic fld$a :exec h) (update-fld :logic update-fld$a :exec update-fld$c))))
)

; The rest was commented out by Matt K. since the defabsstobj above now fails.
#|
(defun h7 (st$c) (declare (xargs :stobjs st$c :guard t) (ignore st$c)) 7)
(defattach h h7)
(defun k9 () (declare (xargs :guard t)) (with-local-stobj st (mv-let (v st) (mv (fld st) st) v)))
(k9)                                                                ; => 7 at the top level
(defthm k9-is-0 (equal (k9) 0) :rule-classes nil)                   ; but this is a theorem
(defun kk (x) (declare (ignore x)) (k9))
(defevaluator mev mev-lst ((kk x)))
(defun mf (term)
  (declare (xargs :guard t))
  (if (and (consp term) (eq (car term) 'kk) (consp (cdr term)) (null (cddr term)))
      (list 'quote (k9))
    term))
(defthm mf-correct
  (equal (mev term a) (mev (mf term) a))
  :rule-classes ((:meta :trigger-fns (kk))))
(defthm bad66 (equal (kk 3) 7) :rule-classes nil :hints (("Goal" :in-theory (disable (:d kk) (:e kk)))))
(defthm bad67 (equal (kk 3) 0) :rule-classes nil :hints (("Goal" :in-theory (disable mf-correct (:e kk) (:e k9)))))
(defthm contradiction66 nil :rule-classes nil :hints (("Goal" :use (bad66 bad67))))
|#
