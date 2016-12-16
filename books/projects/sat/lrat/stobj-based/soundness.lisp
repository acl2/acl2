; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This work is based on Nathan Wetzler's RAT checker work in ACL2 community
; books directory books/projects/sat/proof-checker-itp13/.  Here we accommodate
; a more recent input proof format to speed up unit propagation and add
; deletion (to obtain a DRAT checker).

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.

(in-package "ACL2")

(include-book "lrat-checker")
(local (include-book "../list-based/soundness"))
(local (include-book "equiv"))

; The following is to be proved in equiv.lisp.
(defthm refutation-p-equiv
  (implies (and (formula-p formula)
                (refutation-p$ proof formula))
           (refutation-p proof formula)))

(defthm main-theorem-stobj-based
  (implies (and (formula-p formula)
                (refutation-p$ proof formula))
           (not (satisfiable formula)))
  :hints (("Goal"
           :in-theory '(refutation-p-equiv)
           :use main-theorem-list-based)))
