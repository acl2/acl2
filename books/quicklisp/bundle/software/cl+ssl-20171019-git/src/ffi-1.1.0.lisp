;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(defpackage :openssl-1.1.0
  (:nicknames :ossl-1.1.0 :ossl110)
  (:use :common-lisp)
  (:export #:ssl-ctx-set-default-verify-dir
           #:ssl-ctx-set-default-verify-file))

(cffi:defcfun ("SSL_CTX_set_default_verify_dir" ssl-ctx-set-default-verify-dir)
    :int
  (ctx :pointer))

(cffi:defcfun ("SSL_CTX_set_default_verify_file" ssl-ctx-set-default-verify-file)
    :int
  (ctx :pointer))

