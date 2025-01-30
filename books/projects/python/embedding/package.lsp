(load "~/quicklisp/setup.lisp")
(ql:quickload :trivia)

(defpackage :wgdt
  (:use :cl :acl2 :acl2s :trivia)
  (:import-from :acl2 #:defconst))
