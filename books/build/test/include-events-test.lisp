(in-package "ACL2")

(include-book "build/include-events" :dir :system)

(acl2::include-events "include-events-subdir/include-events-test1")
(include-src-events "build/test/include-events-subdir/include-events-test3.lisp" :dir :system)

(defun baz (x) (foo (bar x)))
