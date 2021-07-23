; Utilities about remove-guard-holders
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/remove-guard-holders-lemmas" :dir :system) ;provides most of what we need

;(include-book "tools/flag" :dir :system)
;(make-flag remove-guard-holders1) ;might want this

(defthm pseudo-termp-of-remove-guard-holders-weak
  (implies (pseudo-termp term)
           (pseudo-termp (remove-guard-holders-weak term lamp))))

(in-theory (disable remove-guard-holders-weak))

;;;
;;; remove-guard-holders-and-clean-up-lambdas
;;;

(defun remove-guard-holders-and-clean-up-lambdas (term)
  (declare (xargs :guard (pseudo-termp term)))
  (remove-guard-holders-weak term t))

(defthm pseudo-termp-of-remove-guard-holders-and-clean-up-lambdas
  (implies (pseudo-termp term)
           (pseudo-termp (remove-guard-holders-and-clean-up-lambdas term))))
