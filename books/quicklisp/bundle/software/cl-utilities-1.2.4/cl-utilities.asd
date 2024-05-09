;; -*- Lisp -*-

(defpackage #:cl-utilities-system
  (:use #:common-lisp #:asdf))

(in-package #:cl-utilities-system)

(defsystem cl-utilities
    :author "Maintained by Peter Scott"
    :components ((:file "package")
		 (:file "split-sequence" :depends-on ("package"))
		 (:file "extremum" :depends-on ("package"
						"with-unique-names"
						"once-only"))
		 (:file "read-delimited" :depends-on ("package"))
		 (:file "expt-mod" :depends-on ("package"))
		 (:file "with-unique-names" :depends-on ("package"))
		 (:file "collecting" :depends-on ("package"
						  "with-unique-names"
						  "compose"))
		 (:file "once-only" :depends-on ("package"))
		 (:file "rotate-byte" :depends-on ("package"))
		 (:file "copy-array" :depends-on ("package"))
		 (:file "compose" :depends-on ("package"))))

;; Sometimes we can accelerate byte rotation on SBCL by using the
;; SB-ROTATE-BYTE extension. This loads it.
#+sbcl
(eval-when (:compile-toplevel :load-toplevel :execute)
  (handler-case (progn
		  (require :sb-rotate-byte)
		  (pushnew :sbcl-uses-sb-rotate-byte *features*))
    (error () (delete :sbcl-uses-sb-rotate-byte *features*))))