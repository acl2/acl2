#|
  This file is a part of fast-http project.
  URL: http://github.com/fukamachi/fast-http
  Copyright (c) 2014 Eitaro Fukamachi <e.arrows@gmail.com>
|#

(in-package :cl-user)
(defpackage fast-http-asd
  (:use :cl :asdf))
(in-package :fast-http-asd)

(defsystem fast-http
  :name "Fast HTTP Parser"
  :description "A fast HTTP protocol parser in Common Lisp"
  :version "0.2.0"
  :author "Eitaro Fukamachi"
  :license "MIT"
  :depends-on (:alexandria
               :cl-utilities
               :proc-parse
               :babel
               :xsubseq
               #+fast-http-debug
               :log4cl

               :smart-buffer)
  :components ((:module "src"
                :components
                ((:file "fast-http" :depends-on ("http" "parser" "multipart-parser" "byte-vector" "error"))
                 (:file "http")
                 (:file "parser" :depends-on ("http" "error" "byte-vector" "util"))
                 (:file "multipart-parser" :depends-on ("parser" "byte-vector" "error"))
                 (:file "byte-vector")
                 (:file "error")
                 (:file "util" :depends-on ("error")))))
  :long-description
  #.(with-open-file (stream (merge-pathnames
                             #p"README.markdown"
                             (or *load-pathname* *compile-file-pathname*))
                            :if-does-not-exist nil
                            :direction :input)
      (when stream
        (let ((seq (make-array (file-length stream)
                               :element-type 'character
                               :fill-pointer t)))
          (setf (fill-pointer seq) (read-sequence seq stream))
          seq)))
  :in-order-to ((test-op (test-op fast-http-test))))

;; XXX: On ECL, it fails if loading a FASL file of parser.lisp.
;;   This is an ugly workaround for now, as I don't get why it happens.
#+ecl
(defmethod asdf:perform :after ((op asdf:load-op) (c (eql (asdf:find-system :fast-http))))
  (load (asdf:system-relative-pathname :fast-http #P"src/parser.lisp")))
