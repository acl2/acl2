; Tests of substitute-constants-in-lambdas2.lisp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-constants-in-lambdas2")
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

(defund test-substitute-constants-in-lambdas2 (term wrld)
  (declare (xargs :mode :program))
  (let* ((term (translate-term term 'test-substitute-constants-in-lambdas2 wrld))
         (result (substitute-constants-in-lambdas2 term))
         (result (untranslate result 'nil wrld)))
    result))

(assert-equal (test-substitute-constants-in-lambdas2 '(let ((x 2)) (+ x y)) (w state))
              '(let nil (+ 2 y)) ; todo: improve!
              )

(assert-equal (test-substitute-constants-in-lambdas2 '(let ((x 2)) (let ((z w)) (+ x y z))) (w state))
              '(let nil (let ((z w)) (+ 2 y z))) ; todo: improve!
              )
