(in-package #:common-lisp-user)

(defpackage #:trivial-backtrace-system (:use #:asdf #:cl))
(in-package #:trivial-backtrace-system)

(defsystem trivial-backtrace
  :version "1.1.0"
  :author "Gary Warren King <gwking@metabang.com> and contributors"
  :maintainer "Gary Warren King <gwking@metabang.com> and contributors"
  :licence "MIT Style license "
  :description "trivial-backtrace"
  :depends-on ()
  :components
  ((:static-file "COPYING")
   (:module 
    "setup"
    :pathname "dev/"
    :components ((:file "packages")))
   (:module 
    "dev"
    :depends-on ("setup")
    :components ((:file "utilities")
		 (:file "backtrace")
		 (:file "map-backtrace")
		 (:file "fallback" :depends-on ("backtrace" "map-backtrace")))))
  :in-order-to ((test-op (load-op trivial-backtrace-test)))
  :perform (test-op :after (op c)
		    (funcall
		     (intern (symbol-name '#:run-tests) :lift)
		     :config :generic)))

(defmethod operation-done-p 
           ((o test-op)
            (c (eql (find-system 'trivial-backtrace))))
  (values nil))
