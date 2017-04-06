; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ./README.

(in-package "LRAT")

(include-book "../stobj-based/lrat-parser")

(include-book "lrat-checker")

(defun lrat-verify-proof-fn (cnf-file lrat-file incomplete-okp state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((er formula) (time$ (parse-cnf-file cnf-file state)))
       ((er proof) (time$ (parse-lrat-file lrat-file state))))
    (value (time$ (lrat-valid-proofp$-top formula proof incomplete-okp)))))

(defmacro lrat-verify-proof (cnf-file lrat-file
                                        &optional (incomplete-okp 'nil))
  `(lrat-verify-proof-fn ,cnf-file ,lrat-file ,incomplete-okp state))

(defmacro acl2::lrat-verify-proof (&rest args)
  `(lrat-verify-proof ,@args))
