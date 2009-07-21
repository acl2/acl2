(in-package "ACL2")

(include-book "test1pb" :ttags :all)

(defttag :test1p)

(make-event
  '(defun test1p (test-pkg::x)
     (cons (test1pp test-pkg::x)
           (test1pb test-pkg::x))))
