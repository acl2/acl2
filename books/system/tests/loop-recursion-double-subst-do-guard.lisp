; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-36: Incomplete fix of the loop$-recursion double substitution admits non-terminating functions (DO loop$ guard route)
; ACL2 Soundness Review, issue S-36.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; R10 issue candidate: proof of NIL.  No ttags, no skip-proofs, no defaxiom.
; Tried on ACL2 master 21aaad6 with SBCL (ld) and CCL (cert.pl: certifies).
;
; Root cause.  6cc670aadd fixed a double substitution in the termination
; machine for :loop$-recursion functions (induct.lisp, termination-machine-rec,
; final T branch: "In earlier versions of this code the nil, below, was alist").
; all-loop$-scion-quote-lambdas(-lst) already instantiates the loop$ scion
; calls it collects with ALIST, so the caller must not pass ALIST again.  But
; the same pattern remains at three sibling call sites of
; termination-machine-rec-for-list:
;   - the lambda-application case when :lambdas is not a ruler-extender
;     (all-loop$-scion-quote-lambdas-lst (fargs body) alist) ... alist
;     -- this is reached with the DEFAULT ruler-extenders, used below;
;   - the IF case when IF is not a ruler-extender
;     (all-loop$-scion-quote-lambdas (fargs body 1) alist) ... alist;
;   - the :plain and :fancy loop$-scion cases (target / globals), which pass
;     ALIST to all-loop$-scion-quote-lambdas(-lst) and then ALIST again.
; So in F3 the binding x := (list x) is applied twice to the loop$ target and
; the measure conjecture contains (MEMBER-EQUAL NV0 (LIST (LIST X))) instead of
; (MEMBER-EQUAL NV0 (LIST X)).  F3 is admitted although it does not terminate:
; for an atom x, (f3 x) is defined in terms of (f3 x) itself.
;
; Consequence.  The warrant of F3 is provably false, but warrants are assumed
; in the special DO loop$ guard conjectures (collect-negated-warrants in
; special-conjectures).  So a DO loop$ that mentions F3 gets its measure
; obligation (g) discharged although its measure does not decrease.  The
; guard-verified G then runs the raw Lisp loop, which returns 1, whereas the
; logical definition (do$ returns the default value on non-decrease) gives NIL.
; A guard-verified metafunction observes the raw value.

(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defun f3 (x)
  (declare (xargs :loop$-recursion t
                  :measure (if (consp x) 0 1)))
  (if (consp x)
      t
    (let ((x (list x)))
      (let ((y (loop$ for e in x always (f3 e))))
        (not y)))))
)

; Matt K. mod: Now that the defun of f fails (above), I am commenting out the
; remaining events.
#|
(defwarrant f3)

(defthm f3-atom
  (implies (and (warrant f3) (not (consp x)))
           (equal (f3 x) (not (f3 x))))
  :rule-classes nil
  :hints (("Goal" :expand ((f3 x)))))

(defthm warrant-f3-is-false
  (not (apply$-warrant-f3))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f3-atom (x nil)))
           :in-theory (disable (:e f3) f3 (:type-prescription f3)))))

(verify-guards f3)

; The measure (nfix i) increases on (setq i (+ 1 i)).  F3 occurs only in the
; unreachable FINALLY clause; its (false) warrant is a hypothesis of the
; special guard conjecture that the measure decreases.
(defun g (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal" :use warrant-f3-is-false))))
  (loop$ with i = n
         do
         :measure (nfix i)
         :guard (natp i)
         (cond ((equal i :never) (loop-finish))
               ((< 0 i) (return i))
               (t (setq i (+ 1 i))))
         finally (return (f3 i))))

(defthm g-0-is-nil
  (equal (g 0) nil)
  :rule-classes nil)

(defun foo (x) (declare (ignore x)) t)
(defevaluator evl evl-lst ((foo x)))

(defun mfn (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (equal (g 0) 1) *nil* term))   ; logically the identity

(defthm mrule
  (equal (evl x a) (evl (mfn x) a))
  :rule-classes ((:meta :trigger-fns (foo))))

(defthm step1
  (equal (foo y) nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(mrule)
                                             (theory 'minimal-theory)))))

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance step1 (y 0))))))

(value-triple (cw "~%NIL-PROVED~%"))
|#
