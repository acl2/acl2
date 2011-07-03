(in-package "ACL2")

(include-book "test1b" :ttags :all)

(defttag :test1)

(make-event
  '(defun test1 (test-pkg::x)
     (cons (test1p test-pkg::x)
           (test1b test-pkg::x))))
