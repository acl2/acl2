; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-36 (route :plain loop$ target): when the loop$ target is itself a recursive loop$ in the body of a LET, the LET alist is applied three times, so the measure conjecture is vacuous and a non-terminating function is admitted.
; Expected: proves nil (prints NIL-PROVED) on SBCL and CCL; certifies with no trust tags.
;
; G121 (lead F1-3073.A): further evidence for S-36, on the :plain loop$-target
; call site.  Proof of nil, no ttags, no skip-proofs.
;
; The outer loop$'s target is itself a loop$ that recurses.  The outer sum$
; call is the body of a LET, so termination-machine-rec (induct.lisp) reaches
; it with alist ((x . (cdr x))).  In the :plain case, TARGET is already
; (sublis-var alist (fargn body 2)); then (all-loop$-scion-quote-lambdas
; target alist) instantiates it a second time and the call of
; termination-machine-rec-for-list passes ALIST, which instantiates it a third
; time.  The measure conjecture is about (member-equal nv1 (cdddr x)), which is
; vacuous here, instead of (member-equal nv1 (cdr x)).  So F is admitted
; though (f '(a b)) is defined as 1 + (f '(a b)).
;
; Note for the S-36 fix: passing NIL instead of ALIST to
; termination-machine-rec-for-list at this call site still leaves two
; substitutions ((cddr x), also vacuous here); TARGET must not be passed to
; all-loop$-scion-quote-lambdas with ALIST (use (fargn body 2) with ALIST, or
; TARGET with NIL).
(in-package "ACL2")
(include-book "projects/apply/top" :dir :system)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defun f (x)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (if (and (consp x) (consp (cdr x)) (atom (cddr x)))
      (let ((x (cdr x)))
        (loop$ for e in (loop$ for d in x collect (f (list 'a d)))
               sum (+ 1 e)))
    0))
)

; Matt K. mod: Now that the defun of f fails (above), I am commenting out the
; remaining events.
#|
(defwarrant f)

(defthm f-step
  (implies (warrant f)
           (equal (f (list 'a b)) (+ 1 (f (list 'a b)))))
  :hints (("Goal" :use ((:instance (:definition f) (x (list 'a b))))
           :in-theory (disable f (:e f))))
  :rule-classes nil)

(defthm warrant-f-false
  (not (warrant f))
  :hints (("Goal" :use ((:instance f-step (b 'b)))
           :in-theory (disable f (:e f))))
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

(defthm nil-proved nil
  :hints (("Goal" :clause-processor (cp clause)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
