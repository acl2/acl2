; This book consists of events, modified only as noted below by Matt Kaufmann,
; that were produced by Claude and passed along by Eric Smith.  They illustrate
; a soundness bug in ACL2 Version 8.7 (which Claude has labeled "ISSUE B1")
; fixed before ACL2 Version 8.8.

; Note from J Moore:

; AI discovered a bug in the source code fuction clausify, the basic routine
; for converting a goal term to a set of clauses.  When the goal term involved
; a lambda application in which the HIDE function was used in the body, the
; variables inside the HIDE term were not instantiated when the lambda was
; applied.  The AI agent suggested a fix that prohibited expanding lambda
; applications involving HIDE.  But that change to the code broke proofs in the
; regression.  We fixed the bug by ``doing it right,''instantiating the
; variables in the HIDE term.  See the source code function if-compile for
; comments about what we changed.

(in-package "ACL2")

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

; ISSUE B1 (if-compile pushes (HIDE formal) verbatim inside lambda bodies)
; Example B1-a: trivial-clause check (tautologyp/if-tautologyp), no hints.
; EXPECT-AFTER-FIX: BAD8 fails.
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad8 (implies (hide x) (let ((x y)) (if (hide x) t nil))) :rule-classes nil)
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction8 nil
  :hints (("Goal" :use ((:instance bad8 (x t) (y nil))) :expand ((hide nil) (hide t))))
  :rule-classes nil)
)

; ISSUE B1.  Example B1-b: :by hint clausifies the hint theorem with lambda-exp t.
; EXPECT-AFTER-FIX: THM1 proves, BAD fails.
(defthm thm1 (let ((x (cons a b))) (if (hide x) t nil))
  :hints (("Goal" :expand ((:free (x) (hide x))))) :rule-classes nil)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad (hide z) :hints (("Goal" :by thm1)) :rule-classes nil)
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction nil
  :hints (("Goal" :use ((:instance bad (z nil))) :expand ((hide nil)))) :rule-classes nil)
)

; ISSUE B1.  Example B1-c: non-tautological-classes accepts a :corollary without proof.
; EXPECT-AFTER-FIX: THM7 fails (corollary proof attempted and fails), BAD7 fails.
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm thm7 (let ((x (cons a b))) (if (hide x) t nil))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:rewrite :corollary (hide x))))
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad7 (hide z) :rule-classes nil)
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction7 nil
  :hints (("Goal" :use ((:instance bad7 (z nil))) :expand ((hide nil)))) :rule-classes nil)
)

; ISSUE B1.  Example B1-d: guard-clauses-for-fn clausifies the normalized guard with lambda-exp t;
; wrong guard conjecture (HIDE X) instead of (HIDE Y); mbe exec/logic mismatch.
; EXPECT-AFTER-FIX: G's guard verification fails (conjecture must mention (HIDE Y)).
(must-fail ; This must-fail wrapper was added by Matt K.
(defun g (x y)
  (declare (ignorable y)
           (xargs :guard (let ((x y)) (if (hide x) (integerp x) nil))
                  :guard-hints (("Goal" :expand ((:free (x) (hide x)))))))
  (mbe :logic (if x 1 2) :exec 1))
)
; The following were commented out by Matt K. since the defun just above now
; fails.
#|
(assert-event (equal (g nil 5) 1))  ; raw execution takes the :exec branch
(defthm g-nil-5-is-2 (equal (g nil 5) 2) :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e g)))))
(defthm g-nil-5-is-1 (equal (g nil 5) 1) :rule-classes nil)
(defthm contradiction9 nil :rule-classes nil
  :hints (("Goal" :use (g-nil-5-is-2 g-nil-5-is-1))))
|#

; ISSUE B1.  Example B1-e: direct observation.
; EXPECT-AFTER-FIX: first value does not mention a free X, e.g. ((((LAMBDA (X) ...) A))) or (((HIDE A)) (A)).
; Non-event commented out by Matt K.:
#|
(clausify '((lambda (x) (if (hide x) x 'nil)) a) nil t nil)
|#
(assert-event (not (member-eq 'x (all-vars1-lst (append-lst (clausify '((lambda (x) (if (hide x) x 'nil)) a) nil t nil)) nil))))

; ISSUE B1.  Example B1-f: chk-acceptable-type-set-inverter-rule validates the rule with TAUTOLOGYP
; (lambda-exp t).  The escaped lambda formal X collides with the rule's free variable X, so a
; :type-set-inverter rule whose expression is strictly stronger than "X is an integer" is accepted.
; Forcing rounds (clausify-type-alist) then express the hypothesis "x is an integer" with that bogus
; term, which is false for every integer, and the forced obligation is discharged vacuously.
; EXPECT-AFTER-FIX: INV is rejected (not propositionally equivalent to (INTEGERP X)).
(defun foo (x) (declare (ignore x)) nil)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm inv
  (equal (if (hide x) (if (integerp x) (let ((x (foo x))) (if (hide x) t nil)) nil) (integerp x))
         (if (hide x) (if (integerp x) (let ((x (foo x))) (if (hide x) t nil)) nil) (integerp x)))
  :rule-classes ((:type-set-inverter :type-set 23)))   ; 23 = *ts-integer*
)

; The following were commented out by Matt K. since the defun just above now
; fails.
#|
(defun h (x) (declare (ignore x)) 0)
(in-theory (disable h (:e h) (:t h)))
(defun g (x) (if (equal (h x) 7) 42 0))
(defthm r (implies (force (equal (h x) 7)) (equal (g x) 42)))
(in-theory (disable g))
(defthm bad11 (implies (integerp x) (equal (g x) 42)) :rule-classes nil
  :hints (("[1]Goal" :expand ((:free (x) (hide x))))))
(defthm contradiction11 nil :rule-classes nil
  :hints (("Goal" :use ((:instance bad11 (x 3))) :in-theory (enable g h))))
|#

; ISSUE B1.  Example B1-g: :built-in-clause rule whose hypothesis (not its conclusion, so unprettyify
; does not beta-reduce it) is a lambda containing HIDE; the stored clause has a free X where
; (foo a) belongs, and it then subsumes arbitrary goals.
; EXPECT-AFTER-FIX: BAD14 fails (the stored clause must mention (HIDE (FOO A)), not (HIDE X)).
; Matt K. mod: Change the name foo to foo2 to avoid name conflict with earlier
; foo.
(defun foo2 (a) (declare (ignore a)) nil)
(defun q (a) (equal a 7))
(defthm bic (implies (let ((x (foo2 a))) (if (hide x) t nil)) (q a))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes :built-in-clause)
(in-theory (disable q (:t q)))
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad14 (implies (hide z) (q w)) :rule-classes nil)
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction14 nil :rule-classes nil
  :hints (("Goal" :use ((:instance bad14 (z t) (w 8))) :expand ((hide t)) :in-theory (enable q))))
)

; ISSUE B1.  Example B1-h: the proof-builder's REWRITE command relieves a hypothesis by
; IF-TAUTOLOGYP (lambda-exp t); the lambda formal X escapes and the hypothesis
; (if (hide x) (let ((x y)) (if (hide x) t nil)) t) -- really (hide x) -> (hide y) --
; is taken to be a tautology, so the rule fires without its hypothesis.
; EXPECT-AFTER-FIX: the :instructions proof of bad23 fails.
(defun f (x y) (if (implies x y) 1 2))
(defthm f-rule
  (implies (if (hide x) (let ((x y)) (if (hide x) t nil)) t)
           (equal (f x y) 1))
  :hints (("Goal" :expand ((:free (x) (hide x))))))
(in-theory (disable f (:e f) (:t f)))
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad23 (equal (f a b) 1)
  :rule-classes nil
  :instructions ((:dive 1) (:rewrite f-rule) :top :s))          ; false at a = t, b = nil
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction23 nil :rule-classes nil
  :hints (("Goal" :use ((:instance bad23 (a t) (b nil))) :in-theory (enable f (:e f)))))
)

; ISSUE B1 (if-compile pushes (HIDE formal) verbatim inside lambda bodies)
; Example B1-i: defabsstobj's :guard-thm shortcut.  chk-defabsstobj-method-lemmas
; skips the guard theorem when (tautologyp expected-guard-thm-formula wrld);
; with B1 the (false) formula
;   (implies (and (st$corr st$c st) (hide x)) ((lambda (x) (if (hide x) t nil)) (if (consp x) (car x) nil)))
; is judged a tautology, so FOO is admitted although its :exec function's guard
; does not follow from its :logic function's guard.  Executing FOO on x = 5 then
; runs FOO$C's :exec branch outside its guard and returns 1, while the logical
; value of (foo 5 st) is 2.
; EXPECT-AFTER-FIX: DEFABSSTOBJ fails (missing :guard-thm), or BAD24/BAD25 fail.
(defstobj st$c (fld$c :type integer :initially 0))
(defun st$ap (x) (declare (xargs :guard t)) (integerp x))
(defun create-st$a () (declare (xargs :guard t)) 0)
(defun st$corr (st$c st)
  (declare (xargs :stobjs st$c :guard t))
  (and (st$cp st$c) (equal (fld$c st$c) st)))
(defun foo$c (x st$c)
  (declare (xargs :stobjs st$c
                  :guard (let ((x (if (consp x) (car x) nil))) (if (hide x) t nil))
                  :guard-hints (("Goal" :expand ((:free (x) (hide x))))))
           (ignore st$c))
  (mbe :logic (if (consp x) 1 2) :exec 1))
(defun foo$a (x st)
  (declare (xargs :guard (hide x)) (ignore st))
  (if (consp x) 1 2))
(defthm create-st{correspondence} (st$corr (create-st$c) (create-st$a)) :rule-classes nil)
(defthm create-st{preserved} (st$ap (create-st$a)) :rule-classes nil)
(defthm foo{correspondence}
  (implies (and (st$corr st$c st) (hide x))
           (equal (foo$c x st$c) (foo$a x st)))
  :rule-classes nil)

(must-fail ; This must-fail wrapper was added by Matt K.
(defabsstobj st
  :foundation st$c
  :recognizer (stp :logic st$ap :exec st$cp)
  :creator (create-st :logic create-st$a :exec create-st$c)
  :corr-fn st$corr
  :exports ((foo :logic foo$a :exec foo$c)))
)

; The following were commented out by Matt K. since the defun just above now
; fails.
#|
(defun bar ()
  (declare (xargs :guard t :guard-hints (("Goal" :expand ((hide 5))))))
  (with-local-stobj st
    (mv-let (v st) (let ((v (foo 5 st))) (mv v st)) v)))
(defthm bad24 (equal (bar) 2)
  :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e bar) (:e foo) (:e create-st)))))
(defthm bad25 (equal (bar) 1) :rule-classes nil)
(defthm contradiction24 nil :rule-classes nil :hints (("Goal" :use (bad24 bad25))))
|#

; ISSUE B1 (if-compile pushes (HIDE formal) verbatim inside lambda bodies)
; Example B1-j: memoize :invoke.  memoize-invoke-guard-implication-term
; (other-events.lisp) drops the required theorem "guard of F implies guard of G"
; when (if-tautologyp (if guard-f guard-g t)).  With B1 the false implication
;   (if (hide x) ((lambda (x) (if (hide x) t nil)) (if (consp x) (car x) nil)) t)
; is judged a tautology, so (memoize 'f :invoke 'g) is accepted with only the
; equality theorem; (f 5) then runs G's raw code outside G's guard and returns
; G's :exec value 1, while (f 5) = 2 logically.
; EXPECT-AFTER-FIX: MEMOIZE fails (missing guard-implication theorem).
(defun g (x)
  (declare (xargs :guard (let ((x (if (consp x) (car x) nil))) (if (hide x) t nil))
                  :guard-hints (("Goal" :expand ((:free (x) (hide x)))))))
  (mbe :logic (if (consp x) 1 2) :exec 1))
; Matt K. mod: Change the name f to f2 to avoid name conflict with earlier f.
(defun f2 (x)
  (declare (xargs :guard (hide x)))
  (if (consp x) 1 2))
(defthm f-is-g (equal (f2 x) (g x)) :rule-classes nil)
(must-fail ; This must-fail wrapper was added by Matt K.
(memoize 'f2 :invoke 'g)
)
(defthm bad26 (equal (f2 5) 2) :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e f2)))))
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad27 (equal (f2 5) 1) :rule-classes nil)
)
(must-fail ; This must-fail wrapper was added by Matt K.
(defthm contradiction26 nil :rule-classes nil :hints (("Goal" :use (bad26 bad27))))
)
