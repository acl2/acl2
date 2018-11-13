;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(defpackage :openssl-1.1.0
  (:nicknames :ossl-1.1.0 :ossl110)
  (:use :common-lisp)
  (:export #:ssl-ctx-set-default-verify-dir
           #:ssl-ctx-set-default-verify-file))

(in-package :openssl-1.1.0)

;; TODO: factor out define-ssl-function into a common dependency from ffi.lisp
;; and use it here. Or just move these functions to ffi.lisp if enough time passes
;; and OpenSSL 1.1 or later is available universally.

(cffi:defcfun ("SSL_CTX_set_default_verify_dir" ssl-ctx-set-default-verify-dir)
    :int
  (ctx :pointer))

(cffi:defcfun ("SSL_CTX_set_default_verify_file" ssl-ctx-set-default-verify-file)
    :int
  (ctx :pointer))

