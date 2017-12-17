#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :cl-user)
(defpackage bt-semaphore-test-asd
  (:use :cl :asdf))
(in-package :bt-semaphore-test-asd)

(defsystem bt-semaphore-test
  :author "Ralph Möritz"
  :license "MIT"
  :depends-on (:bt-semaphore
               :clunit)
  :components ((:module "t"
                :serial t
                :components
                ((:file "package")
                 (:file "semaphore"))))
  :perform (load-op :after (op c) (asdf:clear-system c)))
