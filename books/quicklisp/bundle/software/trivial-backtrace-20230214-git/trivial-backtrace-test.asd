(defpackage #:trivial-backtrace-test-system (:use #:asdf #:cl))
(in-package #:trivial-backtrace-test-system)

(defsystem trivial-backtrace-test
  :author "Gary Warren King <gwking@metabang.com>"
  :maintainer "Gary Warren King <gwking@metabang.com>"
  :licence "MIT Style License; see file COPYING for details"
  :components ((:module 
		"setup"
		:pathname "test/"
		:components ((:file "packages")
			     (:file "test-setup"
				    :depends-on ("packages"))))
	       (:module 
		"test"
		:pathname "test/"
		:depends-on ("setup")
		:components ((:file "tests"))))  
  :depends-on (:lift :trivial-backtrace))



