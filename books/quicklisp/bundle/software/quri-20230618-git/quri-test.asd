#|
  This file is a part of quri project.
  Copyright (c) 2014 Eitaro Fukamachi (e.arrows@gmail.com)
|#

(defsystem quri-test
  :author "Eitaro Fukamachi"
  :license "BSD 3-Clause"
  :depends-on (:quri
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "quri")
                 (:test-file "parser")
                 (:test-file "decode")
                 (:test-file "encode")
                 (:test-file "domain")
                 (:test-file "etld")
                 (:file "benchmark"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove-asdf) c)
                    (asdf:clear-system c)))
