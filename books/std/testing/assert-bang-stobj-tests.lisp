; Standard Testing Library
;
; Copyright (C) 2017 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert-bang-stobj")

(include-book "must-fail")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test-stobj example from David Rager.
(local
 (encapsulate
  ()

  (defstobj foo field1 field2)

  (defun test-stobj (x foo)
    (declare (xargs :stobjs foo))
    (let ((foo (update-field1 17 foo)))
      (update-field2 x foo)))

; Passes.
  (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                   (mv (equal (field1 foo)
                              17)
                       foo))
                 foo)

  (must-fail
   (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                    (mv (equal (field1 foo)
                               14)
                        foo))
                  foo))
  ))
