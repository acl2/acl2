(in-package "ACL2")

(defttag :test1pb)

(make-event
  '(defun test1pb (test-pkg::x)
     (1+ test-pkg::x)))
