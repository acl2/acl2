(in-package "ACL2")

(defttag :test1bb)

(make-event
  '(defun test1bb (test-pkg::x)
     (1+ test-pkg::x)))
