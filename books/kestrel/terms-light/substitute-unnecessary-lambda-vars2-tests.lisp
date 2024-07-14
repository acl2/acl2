; Tests of substitute-unnecessary-lambda-vars2.lisp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-unnecessary-lambda-vars2")
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

(defun substitute-unnecessary-lambda-vars-in-term2-translated (term print hands-off-fns wrld)
  (declare (xargs :guard (true-listp hands-off-fns) :mode :program))
  (let* ((term (translate-term term 'test-subst-var-deep-fn wrld))
         (result (substitute-unnecessary-lambda-vars-in-term2 term print hands-off-fns))
         (result (untranslate result 'nil wrld)))
    result))

(assert-equal (substitute-unnecessary-lambda-vars-in-term2-translated '(let ((x 4)) (< x 5)) nil nil (w state))
              '(let nil (< 4 5)) ; todo: improve, at least as an option
              )

;; ok except for the "let nil"
(assert-equal (substitute-unnecessary-lambda-vars-in-term2-translated '(let* ((z z2)) (list x y z)) t nil (w state))
              '(let nil (list x y z2))
              )

;; todo: why didn't the Y get removed?
(assert-equal (substitute-unnecessary-lambda-vars-in-term2-translated '(let* ((y y2) (z z2)) (list x y z)) t nil (w state))
              '(let nil (let ((y y2)) (list x y z2)))
              )

;; todo: why didn't the Y get removed?
(assert-equal (substitute-unnecessary-lambda-vars-in-term2-translated '(let* ((x 4) (y y2) (z z2)) (list x y z)) nil nil (w state))
              '(let nil (let* ((x 4) (y y2)) (list x y z2)))
              )

;; example showing where we could do better (x could be eliminated in the inner lambda)
(assert-equal (substitute-unnecessary-lambda-vars-in-term2-translated '(let* ((x 4) (y y2) (z z2)) (list x y y z z)) nil nil (w state))
              '(let nil
                 (let ((y y2) (x 4))
                   (let ((z z2)) (list x y y z z)))))
