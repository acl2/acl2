(in-package "ACL2")

(include-book "test1bb" :ttags :all)

(defttag :test1b)

(make-event
  '(defun test1b (test-pkg::x)
     (cons (test1bp test-pkg::x)
           (test1bb test-pkg::x))))
