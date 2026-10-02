; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Proof of nil: IEEE negative zero is observable through DF-STRING.
;
; Logically, dfs are rationals, so (df- (to-df 0)) is (df-round (- 0)) = 0 =
; (to-df 0), and DF-STRING is a function of that rational.  But in raw Lisp,
; (- 0.0d0) is -0.0d0, and DF-STRING prints it as "-0.0" rather than "0.0".
; Guard-verified 0-ary functions let the prover evaluate both in raw Lisp.

(in-package "ACL2")

(defun bad ()
  (declare (xargs :guard t))
  (df-string (df- (to-df 0))))

(defun good ()
  (declare (xargs :guard t))
  (df-string (to-df 0)))

(defthm bad-is-good
  (equal (bad) (good))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable (:e bad) (:e good) (:e df-string)
                                      (:e unary-df-) (:e to-df)))))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm bad-is-not-good
  (not (equal (bad) (good)))
  :rule-classes nil)
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (bad-is-good bad-is-not-good))))
)
