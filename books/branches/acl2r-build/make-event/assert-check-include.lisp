; Here we make sure that we can include assert-check.

(in-package "ACL2")

(include-book "assert-check")

; Check that inclusion of assert-check went to the end.
(make-event
 '(value-triple (assert-check-end 3)))
