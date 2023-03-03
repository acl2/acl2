; Tests for theory-hints.lisp.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "theory-hints")
(include-book "tools/rulesets" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

(def-ruleset foo '(posp endp))
(def-ruleset bar '(natp))

(assert-equal
 (add-enable*/disable*-to-hints '(("Goal" :in-theory (enable remove-duplicates-equal)))
                                '(foo natp)
                                '(bar len))
 '(("Goal"
    :in-theory
    (set-difference-theories (union-theories (expand-ruleset '(foo natp) world)
                                             (enable remove-duplicates-equal))
                             (expand-ruleset '(bar len) world)))))

;; test with no existing hint for Goal
(assert-equal
 (add-enable*/disable*-to-hints nil
                                '(foo natp)
                                '(bar len))
 '(("Goal" :in-theory (e/d* (foo natp) (bar len)))))
