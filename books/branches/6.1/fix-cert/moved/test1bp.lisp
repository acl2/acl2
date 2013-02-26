(in-package "ACL2")

(defttag :test1bp)

(make-event
  '(defun test1bp (test-pkg::x)
     (1+ test-pkg::x)))
