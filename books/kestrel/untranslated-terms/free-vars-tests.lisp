; Tests for free-vars.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "free-vars")
(include-book "std/testing/assert-equal" :dir :system)

(assert-equal (free-vars-in-untranslated-term$ 'x (w state)) '(x))
(assert-equal (free-vars-in-untranslated-term$ '(let ((z (+ x))) (+ y z)) (w state)) '(x y))
