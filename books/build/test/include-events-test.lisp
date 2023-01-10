(in-package "ACL2")

(include-book "build/include-events" :dir :system)

(acl2::include-events "include-events-test1.lisp")
(include-book-events "build/test/include-events-test3" :dir :system)

(defun baz (x) (foo (bar x)))
