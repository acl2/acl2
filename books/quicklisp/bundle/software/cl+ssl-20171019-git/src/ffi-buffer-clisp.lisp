;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

#+xcvb (module (:depends-on ("package" "reload" "conditions" "ffi" "ffi-buffer-all")))

(in-package :cl+ssl)

(defun make-buffer (size)
  (cffi-sys:%foreign-alloc size))

(defun buffer-length (buf)
  (declare (ignore buf))
  +initial-buffer-size+)

(defun buffer-elt (buf index)
  (ffi:memory-as buf 'ffi:uint8 index))
(defun set-buffer-elt (buf index val)
  (setf (ffi:memory-as buf 'ffi:uint8 index) val))
(defsetf buffer-elt set-buffer-elt)

(declaim
 (inline calc-buf-end))

;; to calculate non NIL value of the buffer end index
(defun calc-buf-end (buf-start seq seq-start seq-end)
  (+ buf-start
     (- (or seq-end (length seq))
        seq-start)))

(defun s/b-replace (seq buf &key (start1 0) end1 (start2 0) end2)
  (when (null end2)
    (setf end2 (calc-buf-end start2 seq start1 end1)))
  (replace
   seq
   (ffi:memory-as buf (ffi:parse-c-type `(ffi:c-array ffi:uint8 ,(- end2 start2))) start2)
   :start1 start1
   :end1 end1))

(defun as-vector (seq)
  (if (typep seq 'vector)
      seq
      (make-array (length seq) :initial-contents seq :element-type '(unsigned-byte 8))))

(defun b/s-replace (buf seq &key (start1 0) end1 (start2 0) end2)
  (when (null end1)
    (setf end1 (calc-buf-end start1 seq start2 end2)))
  (setf
   (ffi:memory-as buf (ffi:parse-c-type `(ffi:c-array ffi:uint8 ,(- end1 start1))) start1)
   (as-vector (subseq seq start2 end2)))
  seq)

(defmacro with-pointer-to-vector-data ((ptr buf) &body body)
  `(let ((,ptr ,buf))
    ,@body))
