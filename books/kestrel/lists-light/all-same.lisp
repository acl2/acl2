(in-package "ACL2")

(include-book "all-equal-dollar")

;todo: disable
(defun all-same (lst)
  (declare (xargs :guard (true-listp lst)))
  (or (atom lst)
      (all-equal$ (car lst) (cdr lst))))

(defthm booleanp-of-all-same
  (booleanp (all-same lst)))
