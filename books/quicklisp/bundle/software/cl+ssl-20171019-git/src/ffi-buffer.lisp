;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

#+xcvb (module (:depends-on ("package")))

(in-package :cl+ssl)

(defun make-buffer (size)
  (cffi-sys::make-shareable-byte-vector size))

(defun buffer-length (buf)
  (length buf))

(defun buffer-elt (buf index)
  (elt buf index))
(defun set-buffer-elt (buf index val)
  (setf (elt buf index) val))
(defsetf buffer-elt set-buffer-elt)

(defun s/b-replace (seq buf &key (start1 0) end1 (start2 0) end2)
  (replace seq buf :start1 start1 :end1 end1 :start2 start2 :end2 end2))
(defun b/s-replace (buf seq &key (start1 0) end1 (start2 0) end2)
  (replace buf seq :start1 start1 :end1 end1 :start2 start2 :end2 end2))

(defmacro with-pointer-to-vector-data ((ptr buf) &body body)
  `(cffi-sys::with-pointer-to-vector-data (,ptr ,buf)
    ,@body))
