;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl-user)

(defpackage :cl+ssl.test
  (:use :cl
        :5am))

(in-package :cl+ssl.test)

(def-suite :cl+ssl
  :description "Main test suite for CL+SSL")
