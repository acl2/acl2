(in-package #:common-lisp-user)

(defpackage #:trivial-backtrace
  (:use #:common-lisp)
  (:export #:print-backtrace
	   #:print-backtrace-to-stream
	   #:print-condition
	   #:*date-time-format*


	   #:backtrace-string
	   #:map-backtrace))

