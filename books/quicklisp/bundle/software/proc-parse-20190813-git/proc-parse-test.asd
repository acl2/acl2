#|
  This file is a part of proc-parse project.
  Copyright (c) 2015 Eitaro Fukamachi (e.arrows@gmail.com)
|#

(in-package :cl-user)
(defpackage proc-parse-test-asd
  (:use :cl :asdf))
(in-package :proc-parse-test-asd)

(defsystem proc-parse-test
  :author "Eitaro Fukamachi"
  :license "BSD 2-Clause"
  :depends-on (:proc-parse
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "proc-parse"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove-asdf) c)
                    (asdf:clear-system c)))
