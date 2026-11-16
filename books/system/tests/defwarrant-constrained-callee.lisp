; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-203 (lead F8-354, stage-2 batch G61): defwarrant's apply$-reachability check follows bodies only, so
; a function calling a function constrained in terms of apply$ gets a provably false warrant.  Proves nil
; and certifies, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.  Control: with H defined (not
; constrained), defwarrant refuses F.
;
; G61 (lead F8-354.A): proof of NIL, no trust tags; certifies.
;
; defwarrant classifies f as G1 ("apply$ not reachable", no further
; conditions) because bad-ancestor1 (apply.lisp ~1192) walks only BODIES:
; for a constrained function such as h below, (body 'h nil wrld) is nil, so
; the apply$ call in h's constraint is never seen.  But h is constrained in
; terms of apply$, so f is not definable before apply$ in the model of the
; Essay on Admitting a Model for Apply$, and its warrant can be false: with
; x = '(f), the constraint and the warrant give
;   (apply$ 'f '((f))) = (f '(f)) = (h '(f)) = (not (apply$ 'f '((f)))).
; A clause processor, run with attachments (warrants are attached to
; true-apply$-warrant), then proves nil, as in S-36/S-171.
;
; Verified 2026-10-21 by ld on master 15e42ee881 (/work/acl2-new4 saved_acl2
; SBCL and ccl-saved_acl2 CCL), master 9a589490e6 (/work/acl2-new3 SBCL, CCL)
; and 21aaad6 (acl2-sbcl, acl2-ccl); certify-book succeeds on 15e42ee881 and
; 21aaad6, SBCL and CCL.
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

(encapsulate ((h (x) t))
  (local (defun h (x) (if (consp x) (not (apply$ (car x) (list x))) nil)))
  (defthm h-constraint
    (implies (consp x) (equal (h x) (not (apply$ (car x) (list x)))))
    :rule-classes nil))

(defun f (x) (h x))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defwarrant f) ; accepted with badge (APPLY$-BADGE 1 1 . T)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm warrant-false (not (apply$-warrant-f))
  :hints (("Goal" :use ((:instance h-constraint (x '(f)))
                        (:instance apply$-f (args (list '(f)))))
                  :in-theory (e/d (f) ((:e f) apply$-f)))))

(defevaluator g61-ev g61-ev-lst ((if a b c)))

(defun g61-cp (cl)
  (if (apply$-warrant-f) nil (list cl)))

(defthm g61-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (g61-ev (conjoin-clauses (g61-cp cl)) a))
           (g61-ev (disjoin cl) a))
  :hints (("Goal" :use warrant-false))
  :rule-classes :clause-processor)

(defthm nil-proved nil
  :hints (("Goal" :clause-processor (g61-cp clause)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
