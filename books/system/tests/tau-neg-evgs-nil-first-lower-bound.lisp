; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-198 (lead F1-5833, stage-2 batch G59): the lower-bound mirror (collect-<?-k-x), with a conjunctive
; :tau-system rule.  Proves nil, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
;
(in-package "ACL2")
; mirror: lower bound (collect-<?-k-x)
(defun q (x) (and x (not (equal (fix x) 3)) t))
(defthm q-rule
  (implies (and (< 1 x)
                (not (equal x 3))
                (not (equal x nil)))
           (q x))
  :rule-classes :tau-system)
(in-theory (disable q))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma
  (implies (< 1 x) (q x))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use ((:instance lemma (x 3)))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
