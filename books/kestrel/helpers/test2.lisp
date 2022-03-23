; A test of the proof helper tool (depends on doing generalization)
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "helper")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(defstub foo (x y) t)

;tool needs to prove nat-listp-when-pos-listp (or use :forward-chaining rules)
(must-fail
 (defthm nat-listp-of-foo-when-pos-listp-of-foo
   (implies (pos-listp (foo x y))
            (nat-listp (foo x y)))))

(help-with
 (defthm nat-listp-of-foo-when-pos-listp-of-foo
   (implies (pos-listp (foo x y))
            (nat-listp (foo x y)))))

(must-be-redundant
 (defthm nat-listp-of-foo-when-pos-listp-of-foo
   (implies (pos-listp (foo x y))
            (nat-listp (foo x y)))))
