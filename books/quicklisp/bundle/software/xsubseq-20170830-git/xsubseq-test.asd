#|
  This file is a part of xsubseq project.
  Copyright (c) 2014 Eitaro Fukamachi (e.arrows@gmail.com)
|#

(in-package :cl-user)
(defpackage xsubseq-test-asd
  (:use :cl :asdf))
(in-package :xsubseq-test-asd)

(defsystem xsubseq-test
  :author "Eitaro Fukamachi"
  :license "BSD 2-Clause"
  :depends-on (:xsubseq
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "xsubseq")
                 (:file "benchmark"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove-asdf) c)
                    (asdf:clear-system c)))
