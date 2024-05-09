(in-package :cl-user)
(defpackage smart-buffer-test-asd
  (:use :cl :asdf))
(in-package :smart-buffer-test-asd)

(defsystem smart-buffer-test
  :depends-on (:smart-buffer
               :babel
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "smart-buffer"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove.asdf) c)
                    (asdf:clear-system c)))
