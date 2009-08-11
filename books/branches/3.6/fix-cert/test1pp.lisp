(in-package "ACL2")

(defttag :test1pp)

(make-event
  '(defun test1pp (test-pkg::x)
     (1+ test-pkg::x)))
