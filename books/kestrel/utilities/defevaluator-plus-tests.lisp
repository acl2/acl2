; A nicer interface to defevaluator
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")
(include-book "kestrel/utilities/deftest" :dir :system)

(deftest
  (defevaluator+ myev binary-*)
  ;; expected result:
  (must-be-redundant (defevaluator+ myev binary-*))
  (defthm test (equal (myev '(binary-* '2 x) '((x . 3))) 6)))
