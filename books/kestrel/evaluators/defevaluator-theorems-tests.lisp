; Tests of defevaluator-theorems.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")
(include-book "defevaluator-theorems")

(defevaluator+ myev binary-*)

(defevaluator-theorems myev myev-list)
