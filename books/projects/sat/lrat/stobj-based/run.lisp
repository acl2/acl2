; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

; This modification of the list-based lrat-checker.lisp uses stobjs to speed up
; the handling of assignments, in particular, evaluation of literals and
; clauses.

(in-package "LRAT")

(include-book "lrat-parser")

(defun lrat-check-fn (cnf-file lrat-file incomplete-okp state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val state)
    (time$ (verify-lrat-proof-fn cnf-file lrat-file incomplete-okp state))
    (cond ((and (null erp)
                (eq val t))
           (pprogn (princ$ "s VERIFIED" (standard-co state) state)
                   (newline (standard-co state) state)
                   (prog2$ (exit 0)
                           (mv erp val state))))
          (t
           (pprogn (princ$ "s FAILED" (standard-co state) state)
                   (newline (standard-co state) state)
                   (prog2$ (exit 1)
                           (mv erp val state)))))))

; Note that lrat::lrat-check and acl2::lrat-check are the same symbol.
(defmacro lrat-check (cnf-file lrat-file &optional incomplete-okp)
  `(lrat-check-fn ,cnf-file ,lrat-file ,incomplete-okp state))
