; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; The proof-builder's apply-linear command relieves the hypotheses of a linear
; rule using the top-level hypotheses together with the IF tests governing the
; current subterm, but it then added the rule's conclusion as a top-level
; hypothesis, where those governors need not hold.  Now the hypothesis added is
; the implication from those governors to the conclusion.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun k14f (x)
  (if (consp x) -1 1))

(defthm k14f-neg
  (implies (consp x)
           (< (k14f x) 0))
  :rule-classes :linear)

(in-theory (disable k14f (:e k14f) k14f-neg))

; Before the fix, the following false theorem was proved: after diving to the
; first (k14f x), which is governed by (consp x), apply-linear added the
; hypothesis (< (k14f x) 0) to the top level, where (consp x) need not hold.

(must-fail
 (encapsulate
   ()
   (defthm k14f-neg-bad
     (if (consp x)
         (< (k14f x) 0)
       (< (k14f x) 0))
     :instructions ((:dive 2 1) (:apply-linear k14f-neg) :top :s-prop)
     :rule-classes nil)
   (defthm nil-proved
     nil
     :hints (("Goal"
              :use (:instance k14f-neg-bad (x 0))
              :in-theory (enable (:e k14f))))
     :rule-classes nil)))

; Apply-linear still works under governors, where it now adds the hypothesis
; (implies (consp x) (< (k14f x) 0)).

(defthm k14f-neg-governed
  (if (consp x)
      (< (k14f x) 0)
    t)
  :instructions ((:dive 2 1) (:apply-linear k14f-neg) :top :bash)
  :rule-classes nil)

; A governor that is also a top-level hypothesis is not repeated in the new
; hypothesis, which is simply (< (k14f x) 0).

(defthm k14f-neg-hyp
  (implies (consp x)
           (if (consp x)
               (< (k14f x) 0)
             t))
  :instructions (:promote (:dive 2 1) (:apply-linear k14f-neg) :top :s-prop)
  :rule-classes nil)
