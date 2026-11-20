; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-202 (lead F8-354, stage-2 batch G61): warrant-function-namep maps ACL2-USER::APPLY$-WARRANT-SUM$
; back to SUM$ (imported) and so treats a user's constrained function of that name as SUM$'s warrant;
; defattach to true-apply$-warrant then skips its constraint.  Proves nil and certifies, no trust tags:
; SBCL and CCL at 21aaad6 and 947ff84343.  Control: a name that maps to no warranted function, and the
; defattach fails.
;
; G61 (lead F8-354.A, found while working on F8-326 defpkg): proof of NIL, no
; trust tags, no defpkg, no include-book; certifies.
;
; warrant-function-namep (translate.lisp ~4510) decides that WARRANT-FN is a
; warrant by stripping the prefix "APPLY$-WARRANT-" and interning the rest in
; the package of WARRANT-FN (warrant-name-inverse), then asking whether that
; symbol has a warrant.  It never checks that (warrant-name fn) is WARRANT-FN.
; Through package imports the two differ: ACL2-USER imports ACL2::SUM$ (it is
; in *acl2-exports*) but not ACL2::APPLY$-WARRANT-SUM$, so the fresh symbol
; ACL2-USER::APPLY$-WARRANT-SUM$ maps back to ACL2::SUM$, which has a built-in
; warrant.  So any constrained function named ACL2-USER::APPLY$-WARRANT-SUM$ is
; treated as a warrant: defattach accepts true-apply$-warrant as its attachment
; and defattach-constraint-rec (other-events.lisp ~31296) skips its constraint
; ("The attachment trivially satisfies the required constraints").  The
; evaluation theory is then inconsistent, and a clause processor (run with
; attachments) proves nil.  The same works with a user package that imports a
; warranted function's name but not its warrant name, e.g.
; (defpkg "Q" '(acl2::g)), (defwarrant g), and Q::APPLY$-WARRANT-G
; (~/acl2-work/G61/wfake1.lisp).
;
; Verified 2026-10-21 by ld on master 15e42ee881 (/work/acl2-new4 saved_acl2
; SBCL and ccl-saved_acl2 CCL), master 9a589490e6 (/work/acl2-new3 SBCL, CCL)
; and 21aaad6 (acl2-sbcl, acl2-ccl); certify-book succeeds on 15e42ee881 SBCL
; and CCL and on 21aaad6 SBCL and CCL, and (include-book "wfake2") followed by
; (thm nil :hints (("Goal" :use bad))) succeeds.
(in-package "ACL2")

(encapsulate (((acl2-user::apply$-warrant-sum$) => *))
  (local (defun acl2-user::apply$-warrant-sum$ () nil))
  (defthm fake-warrant-nil (not (acl2-user::apply$-warrant-sum$))
    :rule-classes nil))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
; Accepted without proving the constraint (not (true-apply$-warrant)).
(defattach acl2-user::apply$-warrant-sum$ true-apply$-warrant)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defevaluator g61-ev g61-ev-lst ((if a b c)))

(defun g61-cp (cl)
  (if (acl2-user::apply$-warrant-sum$) nil (list cl)))

(defthm g61-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (g61-ev (conjoin-clauses (g61-cp cl)) a))
           (g61-ev (disjoin cl) a))
  :hints (("Goal" :use fake-warrant-nil))
  :rule-classes :clause-processor)

; The clause processor runs with attachments, so it returns nil.
(defthm nil-proved nil
  :hints (("Goal" :clause-processor (g61-cp clause)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
