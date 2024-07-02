;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(in-package :cl+ssl.test)

(in-suite :cl+ssl)

(test compat-openssl-version
  (is-true (integerp (cl+ssl::compat-openssl-version))))
