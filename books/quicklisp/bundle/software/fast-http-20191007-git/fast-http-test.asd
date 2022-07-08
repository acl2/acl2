#|
  This file is a part of fast-http project.
  URL: http://github.com/fukamachi/fast-http
  Copyright (c) 2014 Eitaro Fukamachi <e.arrows@gmail.com>
|#

(in-package :cl-user)
(defpackage fast-http-test-asd
  (:use :cl :asdf))
(in-package :fast-http-test-asd)

(defsystem fast-http-test
  :depends-on (:fast-http
               :babel
               :cl-syntax-interpol
               :xsubseq
               :prove)
  :components ((:module "t"
                :components
                ((:test-file "parser" :depends-on ("test-utils"))
                 (:test-file "fast-http" :depends-on ("test-utils"))
                 (:test-file "multipart-parser" :depends-on ("test-utils"))
                 (:test-file "util")
                 (:file "test-utils")
                 (:file "benchmark"))))

  :defsystem-depends-on (:prove-asdf)
  :perform (test-op :after (op c)
                    (funcall (intern #.(string :run-test-system) :prove.asdf) c)
                    (asdf:clear-system c)))
