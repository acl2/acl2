; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book directly illustrates the bug involving production of a bad Lisp
; object by code-char, which was fixed by avoiding the export of
; acl2::code-char from the "COMMON-LISP" package and defining acl2::code-char
; in raw Lisp to cause an error for a guard-violating argument.

; I gave Claude the following prompt:

#|
Please prove nil from the following events.
(defstobj st fld)
(defun g (state)
  (declare (xargs :stobjs state :mode :program))
  (with-global-stobj
    st
    (st)
    (update-fld (code-char 300) st)))
(make-event (pprogn (g state)
                    (value '(value-triple (fld st)))))
|#

; Here is Claude's solution.

(in-package "ACL2")

; The user's events: G is :program mode, so raw CODE-CHAR runs with no guard
; check, and the live stobj ST ends up holding a character whose code is 300.
(defstobj st fld)

(defun g (state)
  (declare (xargs :stobjs state :mode :program))
  (with-global-stobj
    st
    (st)
    (update-fld (code-char 300) st)))

; Added by Matt Kaufmann after the bug fix:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. after the bug fix.
(make-event (pprogn (g state)
                    (value '(value-triple (fld st)))))
)

; A clause processor that reads ST.  Logically, CHAR-CODE is always below 256
; (axiom CHAR-CODE-LINEAR), so CP-BAD always returns the clause list (LIST CL) and is trivially
; correct.  (It returns (MV NIL CLAUSES ST), as a clause processor taking a
; stobj must.)  But it is guard-verified, so the prover runs its raw Lisp code on
; the live ST, where the character code is 300, and so CP-BAD returns the empty clause
; list: "no goals left".
(defevaluator cp-ev cp-ev-list ((if a b c)))

(defun cp-bad (cl hint st)
  (declare (xargs :stobjs st :guard t) (ignore hint))
  (mv nil
      (if (and (characterp (fld st))
               (not (< (char-code (fld st)) 256)))
          nil
        (list cl))
      st))

(defthm cp-bad-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (cp-ev (conjoin-clauses (clauses-result (cp-bad cl hint st))) a))
           (cp-ev (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail ; This must-fail wrapper was added by Matt K. after the bug fix.
(defthm contradiction
  nil
  :hints (("Goal" :clause-processor (cp-bad clause nil st)))
  :rule-classes nil)
)
