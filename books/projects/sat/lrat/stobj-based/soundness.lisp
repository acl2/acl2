; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ./README.

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.

(in-package "LRAT")

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
