;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

(defconstant +initial-buffer-size+ 2048)

(declaim
 (inline
  make-buffer
  buffer-length
  buffer-elt
  set-buffer-elt
  s/b-replace
  b/s-replace))
