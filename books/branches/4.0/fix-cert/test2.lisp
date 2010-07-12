(in-package "ACL2")

(defttag :test2)

(make-event
  '(defun test2 (test-pkg::x)
     (1+ test-pkg::x)))
