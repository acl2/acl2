; A test of the proof helper tool
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: INCOMPLETE

(include-book "helper")
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

(defstub foo (x y) t)

;; (defaxiom pos-listp-of-foo
;;   ;; arg names not the same as in the theorem below:
;;   (pos-listp (foo a1 a2)))

;; ;tool needs to prove nat-listp-when-pos-listp (or use :forward-chaining rules)
;; (must-fail
;;  (defthm nat-listp-of-foo
;;    (nat-listp (foo x y))))

;; (help-with
;;  (defthm nat-listp-of-foo
;;    (nat-listp (foo x y))))

;; (must-be-redundant
;;  (defthm nat-listp-of-foo
;;    (nat-listp (foo x y))))
