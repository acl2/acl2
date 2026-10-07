; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 44: inverse-polys' bounds-polys2 of the negative-upper-bound branch
; (non-linear.lisp:647-662) derives  var [<,<=] (/ inv-var-lbd)  from
; inv-var-lbd, but passes VAR-LBD-REL (:659) as the new poly's relation where
; it must pass INV-VAR-LBD-REL.  The ttree it passes IS inv-var-lbd-ttree, so
; the code knows which bound it is using and takes the other one's strictness.
; Its correctly-coded sibling, bounds-polys4 of the positive branch (:602),
; passes inv-var-lbd-rel.
;
; Independent of Finding 43: here both reciprocated bounds are negative, so
; Finding 43's sign condition is satisfied.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; FALSE: the hypothesis pins x = -1, so (/ x) = -1 and the conclusion is
; (<= -1 -5) = NIL.
(must-fail
 (local
  (defthm bogus-strict-reciprocal-bound
    (implies (and (rationalp x) (equal (* -2 x) 2))
             (<= (/ x) -5))
    :hints (("Goal" :nonlinearp t))
    :rule-classes nil)))

; The isolating measurement: flipping only the strictness of the conclusion --
; which is what determines var-lbd-rel after negation -- must NOT change
; provability once the right relation variable is passed.  Today the <= form
; above is proved and this < form is not; after the fix neither is.
(must-fail
 (local
  (defthm bogus-strict-reciprocal-bound-strict
    (implies (and (rationalp x) (equal (* -2 x) 2))
             (< (/ x) -5))
    :hints (("Goal" :nonlinearp t))
    :rule-classes nil)))
