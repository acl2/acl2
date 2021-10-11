; A trivial evaluator that knows about no functions
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")

;; TODO: Should we use -ev or -eval or -evl for evaluator names?
(defevaluator+ empty-eval) ; an evaluator with no built-in functions
