; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-203 route: the built-in defchoose witness APPLY$-EQUIVALENCE-WITNESS has no body but its axiom mentions apply$, so a function calling it is accepted as G1.
;
; G188 (lead F2-140.A): proof of NIL through the built-in defchoose witness
; APPLY$-EQUIVALENCE-WITNESS (no user encapsulate or defchoose).
; defwarrant classifies F as G1 because bad-ancestor1 (apply.lisp) walks only
; bodies, and the built-in witness has no body; its constraint mentions apply$:
; if fn1 and fn2 differ on some args, they differ on (w fn1 fn2).  F agrees with
; CONSP exactly at (car (w 'f 'consp)) and differs everywhere else, so with F's
; warrant the witness axiom fails.  Same root cause as S-203 (a fix that only
; looks at user-introduced constrained functions would miss this built-in one;
; untame-apply$ and the built-in scions' warrants/witnesses are other bodiless
; built-ins whose constraints mention apply$-userfn or badge-userfn).
; Proves nil by ld and certifies (no trust tags) on SBCL and CCL at 16dbd4bd56
; (/work/acl2-new6) and 21aaad6 (acl2-sbcl, acl2-ccl).
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

(defun f (x)
  (if (equal x (car (apply$-equivalence-witness 'f 'consp)))
      (consp x)
    (not (consp x))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defwarrant f) ; accepted as G1, badge (APPLY$-BADGE 1 1 . T)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm warrant-false (not (apply$-warrant-f))
  :hints (("Goal"
           :use ((:instance apply$-equivalence-necc
                            (fn1 'f) (fn2 'consp)
                            (args (list (list (car (apply$-equivalence-witness 'f 'consp))))))
                 (:instance apply$-f
                            (args (list (list (car (apply$-equivalence-witness 'f 'consp))))))
                 (:instance apply$-f
                            (args (apply$-equivalence-witness 'f 'consp))))
           :in-theory (e/d (f apply$-equivalence) ((:e f) apply$-f apply$-equivalence-necc))))
  :rule-classes nil)

(defevaluator g188-ev g188-ev-lst ((if a b c)))

(defun g188-cp (cl)
  (if (apply$-warrant-f) nil (list cl)))

(defthm g188-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (g188-ev (conjoin-clauses (g188-cp cl)) a))
           (g188-ev (disjoin cl) a))
  :hints (("Goal" :use warrant-false))
  :rule-classes :clause-processor)

(defthm nil-proved nil
  :hints (("Goal" :clause-processor (g188-cp clause)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
