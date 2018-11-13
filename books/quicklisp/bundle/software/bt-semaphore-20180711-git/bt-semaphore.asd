#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :cl-user)
(defpackage bt-semaphore-asd
  (:use :cl :asdf))
(in-package :bt-semaphore-asd)

(defsystem bt-semaphore
  :version "0.6.3"
  :author "Ralph Möritz"
  :license "MIT"
  :depends-on (:bordeaux-threads)
  :components ((:module "src"
                :serial t
                :components
                ((:file "package")
                 (:file "semaphore"))))
  :description "A simple semaphore class for bordeaux-threads inspired by SBCL's semaphore."
  :long-description
  #.(with-open-file (stream (merge-pathnames
                             #p"README.md"
                             (or *load-pathname* *compile-file-pathname*))
                            :if-does-not-exist nil
                            :direction :input)
      (when stream
        (let ((seq (make-array (file-length stream)
                               :element-type 'character
                               :fill-pointer t)))
          (setf (fill-pointer seq) (read-sequence seq stream))
          seq)))
  :in-order-to ((test-op (load-op bt-semaphore-test))))
