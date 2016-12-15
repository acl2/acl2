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

(include-book "lrat-parser")

(defun lrat-check-fn (cnf-file lrat-file incomplete-okp state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val state)
    (verify-lrat-proof-fn cnf-file lrat-file incomplete-okp state)
    (cond ((and (null erp)
                (eq val t))
           (pprogn (princ$ "s VERIFIED" (standard-co state) state)
                   (prog2$ (exit 0)
                           (mv erp val state))))
          (t
           (pprogn (princ$ "s FAILED" (standard-co state) state)
                   (prog2$ (exit 1)
                           (mv erp val state)))))))

(defmacro lrat-check (cnf-file lrat-file &optional incomplete-okp)
  `(lrat-check-fn ,cnf-file ,lrat-file ,incomplete-okp state))
