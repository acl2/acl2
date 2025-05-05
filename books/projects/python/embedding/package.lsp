(load "~/quicklisp/setup.lisp")
(ql:quickload :trivia)

(defpackage :acl2s-python-types
  (:use :cl :acl2 :acl2s :trivia)
  (:import-from :acl2 #:defconst))
