; A utility for fixing up IGNORE and IGNORABLE declares.
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also fixup-ignores.lisp

(include-book "declares0")
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)

;; Returns a new list of declares, with exactly the right IGNORE declares wrt FORMALS and BODY.
(defun fixup-ignores-for-translated-body (declares formals body)
  (declare (xargs :guard (and (all-declarep declares)
                              (symbol-listp formals)
                              (pseudo-termp body))))
  (let* ((formals-mentioned (free-vars-in-term body))
         (ignored-formals (set-difference-eq formals formals-mentioned))
         ;; Remove any existing ignore declares (we will put in the right ones):
         (declares (remove-declares 'ignore declares))
         ;; Also remove any ignorable declares, since we are setting the ignores to be exactly what we need:
         (declares (remove-declares 'ignorable declares))
         (declares (if ignored-formals
                       (add-declare-arg `(ignore ,@ignored-formals) declares)
                     declares)))
    declares))
