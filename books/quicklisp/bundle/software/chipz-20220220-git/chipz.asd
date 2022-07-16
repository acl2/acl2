; -*- mode: lisp -*-
(cl:defpackage :chipz-system
  (:use :cl :asdf)
  (:export #:gray-streams))
(cl:in-package :chipz-system)

(defclass txt-file (doc-file) ((type :initform "txt")))
(defclass css-file (doc-file) ((type :initform "css")))

(eval-when (:compile-toplevel :load-toplevel :execute)
  #+(or sbcl lispworks openmcl cmu allegro clisp ecl genera clasp)
  (pushnew 'chipz-system:gray-streams cl:*features*))

(asdf:defsystem :chipz
  :version "0.8"
  :author "Nathan Froyd <froydnj@gmail.com>"
  :maintainer "Nathan Froyd <froydnj@gmail.com>"
  :description "A library for decompressing deflate, zlib, and gzip data"
  :license "BSD style"
  :components ((:static-file "NEWS")
               (:static-file "LICENSE")
               (:static-file "TODO")
               (:file "package")
               (:module "doc"
                        :components
                        ((:html-file "index")
                         (:txt-file "chipz-doc")
                         (:css-file "style")))
               (:file "constants" :depends-on ("package"))
               (:file "types-and-tables" :depends-on ("constants"))
               (:file "crc32" :depends-on ("types-and-tables"))
               (:file "adler32" :depends-on ("types-and-tables"))
               (:file "conditions" :depends-on ("package"))
               (:file "dstate" :depends-on ("package"))
               (:file "inflate-state" :depends-on ("dstate" "crc32" "adler32"))
               (:file "gzip" :depends-on ("inflate-state" "conditions"))
               (:file "zlib" :depends-on ("inflate-state" "conditions"))
               (:file "inflate" :depends-on ("inflate-state"
                                             "gzip" "zlib"
                                             "conditions"))
               (:file "bzip2" :depends-on ("dstate" "constants"))
               (:file "decompress" :depends-on ("inflate-state"
                                                "inflate" "bzip2"))
               #+chipz-system:gray-streams
               (:file "stream" :depends-on ("inflate-state" "inflate"))

               #-chipz-system:gray-streams
               (:file "stream-fallback" :depends-on ("package"))))
