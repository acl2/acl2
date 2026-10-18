; Copyright (C) 2026, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This books is based on code-char-300.lisp.  In this case, the bug involved
; production of a bad Lisp object by expt, which was fixed by avoiding the
; export of acl2::expt from the "COMMON-LISP" package and defining acl2::expt
; in raw Lisp to cause an error for a non-integer exponent.

(in-package "ACL2")

(defstobj st fld)

(defun g (state)
  (declare (xargs :stobjs state :mode :program))
  (with-global-stobj
    st
    (st)
    (update-fld (expt 2 1/2) st)))

(include-book "std/testing/must-fail" :dir :system)

(must-fail
(make-event (pprogn (g state)
                    (value '(value-triple (fld st)))))
)

(defevaluator cp-ev cp-ev-list ((if a b c)))

(defun cp-bad (cl hint st)
  (declare (xargs :stobjs st :guard t) (ignore hint))
  (mv nil
      (if (and (acl2-numberp (fld st))
               (not (real/rationalp (realpart (fld st))))
               (not (real/rationalp (imagpart (fld st))))
               (not (real/rationalp (fld st))))
          nil
        (list cl))
      st))

(defthm cp-bad-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (cp-ev (conjoin-clauses (clauses-result (cp-bad cl hint st))) a))
           (cp-ev (disjoin cl) a))
  :rule-classes :clause-processor)

(must-fail ; Needed must-fail after the bug was fixed.
(defthm contradiction
  nil
  :hints (("Goal" :clause-processor (cp-bad clause nil st)))
  :rule-classes nil)
)
