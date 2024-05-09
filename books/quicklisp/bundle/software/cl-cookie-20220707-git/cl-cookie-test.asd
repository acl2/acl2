#|
  This file is a part of cl-cookie project.
  Copyright (c) 2015 Eitaro Fukamachi (e.arrows@gmail.com)
|#

(in-package :cl-user)
(defpackage cl-cookie-test-asd
  (:use :cl :asdf))
(in-package :cl-cookie-test-asd)

(defsystem cl-cookie-test
  :author "Eitaro Fukamachi"
  :license "BSD 2-Clause"
  :depends-on (:cl-cookie
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "cl-cookie"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove-asdf) c)
                    (asdf:clear-system c)))
