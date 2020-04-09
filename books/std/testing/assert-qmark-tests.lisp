; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert-qmark")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (assert? t 444) 444)

(assert-equal (assert? t 444 'my-ctx "my msg") 444)

(assert-equal (assert? t 444 'my-ctx (msg "my ~@0" "msg")) 444)

(assert-equal (let ((x 4) (y 3)) (assert? (> x y) 444)) 444)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (progn (value-triple (assert? nil 444))))

(must-fail
 (progn (value-triple (assert? nil 444 'my-ctx "my msg"))))

(must-fail
 (progn (value-triple (assert? nil 444 'my-ctx (msg "my ~@0" "msg")))))

(must-fail
 (progn (value-triple (let ((x 4) (y 3)) (assert? (< x y) 444)))))
