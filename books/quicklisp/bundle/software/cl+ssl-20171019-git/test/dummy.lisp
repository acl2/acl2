;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(in-suite :cl+ssl)

(test (sanity-check.1 :compile-at :definition-time)
  (is-true t "SANITY CHECK: T isn't T"))

(test (sanity-check.2 :compile-at :definition-time)
  (is-false nil "SANITY CHECK: NIL isn't NIL"))
