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

(in-package "LRAT")

(include-book "incremental")

(defun lrat-check-fn (cnf-file lrat-file incomplete-okp state)

; We use 1,000,000 for the chunk-size.

  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp s state)
    (getenv$ "LRAT_CHUNK_SIZE" state)
    (let ((chunk-size (or (and (null erp)
                               (stringp s)
                               (acl2::decimal-string-to-number s (length s) 0))
                          1000000)))
      (mv-let (erp val state)
        (time$ (incl-verify-proof cnf-file lrat-file
                                  :incomplete-okp incomplete-okp
                                  :chunk-size chunk-size
                                  :debug t))
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
                               (mv erp val state)))))))))

; Note that lrat::lrat-check and acl2::lrat-check are the same symbol.
(defmacro lrat-check (cnf-file lrat-file &optional incomplete-okp)

; We use 1,000,000 for the chunk-size.

  `(lrat-check-fn ,cnf-file ,lrat-file ,incomplete-okp state))
