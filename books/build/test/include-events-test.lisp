(in-package "ACL2")

(include-book "build/include-events" :dir :system)

(include-events "include-events-test1.lisp")
(include-events "build/test/include-events-test3.lisp" :dir :system)

(defun baz (x) (foo (bar x)))
