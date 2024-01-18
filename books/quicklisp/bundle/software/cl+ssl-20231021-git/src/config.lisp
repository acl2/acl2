;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(in-package :cl-user)

(defpackage :cl+ssl/config
  (:documentation "By default cl+ssl searches for OpenSSL shared libraries
in platform-dependent default locations.

To explicitly specify what to load, use the cl+ssl/config
module before loading cl+ssl:

    (ql:quickload \"cl+ssl/config\")
    (cl+ssl/config:define-libssl-path \"/opt/local/lib/libssl.dylib\")
    (cl+ssl/config:define-libcrypto-path \"/opt/local/lib/libcrypto.dylib\")
    (ql:quickload \"cl+ssl\")

The PATH parameter of those two macros is not evaluated.
This is dictated by CFFI. So either use a literal
or compute it at the macro-expansion time.

You may need to rebuild cl+ssl for the changed paths to have effect.
This depends on CFFI and the FFI implementation of your Lisp.
")
  (:export #:define-libssl-path
           #:define-libcrypto-path)
  (:use :common-lisp))

(in-package :cl+ssl/config)

(defvar *libssl-override* nil)
(defvar *libcrypto-override* nil)

(defmacro define-libssl-path (path)
  "Define the path where libssl resides to be PATH (not evaluated). This
macro should be used before loading CL+SSL.
"
  `(progn
     (cffi:define-foreign-library libssl (t ,path))
     (setq *libssl-override* t)))

(defmacro define-libcrypto-path (path)
  "Define the path where libcrypto resides to be PATH (not evaluated). This
macro should be used before loading CL+SSL.
"
  `(progn
     (cffi:define-foreign-library libcrypto (t ,path))
     (setq *libcrypto-override* t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The above package replaces now _deprecated_ *FEATURES* flag
;; :CL+SSL-FOREIGN-LIBS-ALREADY-LOADED
;;
;; The flag allows user to load himself the
;; libssl / libcrypto (and libeay32 on Windows),
;; thus choosing the foreigh library(-ies) path and version to load.
;;
;; You will probably need to recompile CL+SSL for the feature to take
;; effect.
;;
;; If specified, neither loading of the cl+ssl ASDF system nor
;; (cl+ssl:reload) try to load the foreign libraries, assuming
;; user has loaded them already.
;;
;; The _deprecated_ usage example:
;;
;;     (cffi:load-foreign-library "libssl.so.1.0.0")
;;
;;     (let ((*features* (cons :cl+ssl-foreign-libs-already-loaded
;;                             *features*)))
;;
;;     (ql:quickload :a-system-which-depends-on-cl+ssl)
;;
;;     ;; or just load cl+ssl
;;     (ql:quickload :cl+ssl))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
