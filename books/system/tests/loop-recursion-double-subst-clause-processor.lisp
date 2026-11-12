; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-36: Incomplete fix of the loop$-recursion double substitution admits non-terminating functions (clause processor route)
; ACL2 Soundness Review, issue S-36.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; Batch N2 (lead F12-131, commit 6cc670aadd).  Proof of nil, no ttags,
; certifiable.  Same root cause as the R10 candidate F3-209.A
; (issues/candidates/R10-loop-recursion-double-subst.lisp): 6cc670aadd fixed
; only one of the places where termination-machine-rec applies ALIST a second
; time to loop$ scion calls that all-loop$-scion-quote-lambdas(-lst) has
; already instantiated.  Here the remaining site in the lambda-application
; case (default ruler-extenders, :lambdas not included) is hit: for F below the
; measure conjecture mentions (member-equal nv0 (cddr x)) although the loop$
; target is (cdr x), so F is admitted though (f (list a b)) calls
; (f (list 'a b)) and hence (f '(a b)) calls itself.
;
; New here: the false warrant gives nil directly through a clause processor,
; with no DO loop$ and no metafunction.  Clause processors are evaluated with
; attachments allowed, and every warrant function is attached to
; true-apply$-warrant, so (apply$-warrant-f) evaluates to T even though
; (not (apply$-warrant-f)) is a theorem.  chk-meta-fn-attachments does not
; object because apply$-warrant-f is not ancestral in the evaluator.
;
; Tested on ACL2 master 21aaad6: ld and certify-book with SBCL and CCL.
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defun f (x)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (if (and (consp x) (consp (cdr x)) (atom (cddr x)))
      (let ((x (cdr x)))
        (let ((z (loop$ for e in x sum (f (list 'a e)))))
          (+ 1 z)))
    0))
)

; Matt K. mod: Now that the defun of f fails (above), I am commenting out the
; remaining events.
#|
(defwarrant f)

(defthm f-step
  (implies (warrant f)
           (equal (f (list a b)) (+ 1 (f (list 'a b)))))
  :hints (("Goal" :expand ((f (list a b)))))
  :rule-classes nil)

(defthm warrant-f-false
  (not (warrant f))
  :hints (("Goal" :use ((:instance f-step (a 'a))) :in-theory (disable f)))
  :rule-classes nil)

(defevaluator evl evl-list ((if x y z)))

(defun cp (cl)
  (if (apply$-warrant-f) nil (list cl)))

(defthm cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses (cp cl)) a))
           (evl (disjoin cl) a))
  :hints (("Goal" :use warrant-f-false))
  :rule-classes :clause-processor)

(defthm contradiction nil
  :hints (("Goal" :clause-processor (cp clause)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
