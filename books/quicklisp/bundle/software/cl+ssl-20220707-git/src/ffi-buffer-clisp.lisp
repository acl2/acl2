;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

;;;; CLISP speedup comments by Pixel / pinterface, 2007,
;;;; copied from https://code.kepibu.org/cl+ssl/
;;;;
;;;; ## Speeding Up clisp
;;;; cl+ssl has some serious speed issues on CLISP. For small requests,
;;;; it's not enough to worry about, but on larger requests the speed
;;;; issue can mean the difference between a 15 second download and a 15
;;;; minute download. And that just won't do!
;;;;
;;;; ### What Makes cl+ssl on clisp so slow?
;;;; On clisp, cffi's with-pointer-to-vector-data macro uses copy-in,
;;;; copy-out semantics, because clisp doesn't offer a with-pinned-object
;;;; facility or some other way of getting at the pointer to a simple-array.
;;;; Very sad, I know. In addition to being a leaky abstraction, wptvd is really slow.
;;;;
;;;; ### How to Speed Things Up?
;;;; The simplest thing that can possibly work: break the abstraction.
;;;; I introduce several new functions (buffer-length, buffer-elt, etc.)
;;;; and use those wherever an ssl-stream-*-buffer happens to be used,
;;;; in place of the corresponding sequence functions.
;;;; Those buffer-* functions operate on clisp's ffi:pointer objects,
;;;; resulting in a tremendous speedup--and probably a memory leak or two.
;;;;
;;;; ### This Is Not For You If...
;;;; While I've made an effort to ensure this patch doesn't break other
;;;; implementations, if you have code which relies on ssl-stream-*-buffer
;;;; returning an array you can use standard CL functions on, it will break
;;;; on clisp under this patch. But you weren't relying on cl+ssl
;;;; internals anyway, now were you?

#+xcvb (module (:depends-on ("package" "reload" "conditions" "ffi" "ffi-buffer-all")))

(in-package :cl+ssl)

(defclass clisp-ffi-buffer ()
  ((size
    :initarg :size
    :accessor clisp-ffi-buffer-size)
   (pointer
    :initarg :pointer
    :accessor clisp-ffi-buffer-pointer)))

(defun make-buffer (size)
  (make-instance 'clisp-ffi-buffer
                 :size size
                 :pointer (cffi-sys:%foreign-alloc size)))

(defun buffer-length (buf)
  (clisp-ffi-buffer-size buf))

(defun buffer-elt (buf index)
  (ffi:memory-as (clisp-ffi-buffer-pointer buf) 'ffi:uint8 index))
(defun set-buffer-elt (buf index val)
  (setf (ffi:memory-as (clisp-ffi-buffer-pointer buf) 'ffi:uint8 index) val))
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
   (ffi:memory-as (clisp-ffi-buffer-pointer buf)
                  (ffi:parse-c-type `(ffi:c-array ffi:uint8 ,(- end2 start2)))
                  start2)
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
   (ffi:memory-as (clisp-ffi-buffer-pointer buf)
                  (ffi:parse-c-type `(ffi:c-array ffi:uint8 ,(- end1 start1)))
                  start1)
   (as-vector (subseq seq start2 end2)))
  seq)

(defmacro with-pointer-to-vector-data ((ptr buf) &body body)
  `(let ((,ptr (clisp-ffi-buffer-pointer ,buf)))
    ,@body))
