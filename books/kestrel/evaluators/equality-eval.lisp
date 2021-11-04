; An evaluator that knows about equal, eql, eq, etc.
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")

;; An evaluator that knows about various equality tests (as well as IF and NOT).
(defevaluator+ equality-eval if equal eql eq not)
