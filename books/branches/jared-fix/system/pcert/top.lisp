(in-package "ACL2")

(progn (make-event '(make-event '(defun r1 (x) x)))
       (defun r2 (x) x))

(include-book "mid")
