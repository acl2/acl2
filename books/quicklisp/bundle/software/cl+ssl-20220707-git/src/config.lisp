(in-package :cl-user)

(defpackage :cl+ssl/config
  (:use :common-lisp)
  (:export #:define-libssl-path
           #:define-libcrypto-path))

(in-package :cl+ssl/config)

(defvar *libssl-override* nil)
(defvar *libcrypto-override* nil)

(defmacro define-libssl-path (path)
  "Define the path where libssl resides to be PATH (not evaluated). This
macroshould be used before loading CL+SSL.

For instance, this defines libssl as \"/opt/local/lib/libssl.dylib\":

    (ql:quickload :cl+ssl/config)
    (cl+ssl:define-libssl-path \"/opt/local/lib/libssl.dylib\")
    (ql:quickload :cl+ssl)"
  `(progn
     (cffi:define-foreign-library libssl (t ,path))
     (setq *libssl-override* t)))

(defmacro define-libcrypto-path (path)
  "Define the path where libcrypto resides to be PATH (not evaluated). This
macro should be used before loading CL+SSL."
  `(progn
     (cffi:define-foreign-library libcrypto (t ,path))
     (setq *libcrypto-override* t)))
