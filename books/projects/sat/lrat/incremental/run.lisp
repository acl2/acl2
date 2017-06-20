; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "LRAT")

(include-book "soundness")
(include-book "print-formula")

(defun lrat-check-fn (cnf-file clrat-file incomplete-okp state)

; See lrat-check.

  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp s state)
    (getenv$ "LRAT_CHUNK_SIZE" state)
    (let ((chunk-size
           (or (and (null erp)
                    (stringp s)
                    (acl2::decimal-string-to-number s (length s) 0))
               1000000)))
      (mv-let (erp s state)
        (getenv$ "LRAT_PRINT_FORMULA" state)
        (let ((formula-file (and (null erp)
                                 (not (equal s ""))
                                 s)))
          (mv-let (erp formula state)
            (time$ (proved-formula cnf-file clrat-file
                                   chunk-size
                                   t ; debug
                                   incomplete-okp 'lrat-check state))
            (cond ((and (null erp) ; always true
                        formula)
                   (pprogn (princ$ "s VERIFIED" (standard-co state) state)
                           (newline (standard-co state) state)
                           (er-progn
                            (cond (formula-file
                                   (print-formula formula
; Header was omitted historically; we preserve that for now (as expected in
; a diff-based script elsewhere).
                                                  :header-p nil
; Standard output for t or T.
                                                  :filename
                                                  (and (not (member-equal
                                                             formula-file
                                                             '("t" "T")))
                                                       formula-file)))
                                  (t (value nil)))
                            (prog2$ (exit 0)
                                    (mv erp t state)))))
                  (t
                   (pprogn (princ$ "s FAILED" (standard-co state) state)
                           (newline (standard-co state) state)
                           (prog2$ (exit 1)
                                   (mv erp nil state)))))))))))

(defmacro lrat-check (cnf-file clrat-file &optional incomplete-okp)

; Note that lrat::lrat-check and acl2::lrat-check are the same symbol.

; This wrapper for proved-formula passes along this call's parameters and uses
; t for the value of debug.  It also sets chunk-size to 1,000,000 by default,
; but that can be overridden by giving environment variable LRAT_CHUNK_SIZE a
; numeric value.  If proved-formula returns a verified formula, then if
; environment variable LRAT_PRINT_FORMULA is assigned a filename, the formula
; will be written to that filename (without the "p" or comment lines) -- unless
; the value of LRAT_PRINT_FORMULA is "t" or "T", in which case the formula will
; be written to standard output.

  `(lrat-check-fn ,cnf-file ,clrat-file ,incomplete-okp state))
