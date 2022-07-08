;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; misc.lisp --- Various helper functions.
;;;
;;; Copyright (C) 2006-2007, Stelian Ionescu  <stelian.ionescu-zeus@poste.it>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(in-package #:osicat-posix)

;;;; Misc

(defun fd-open-p (fd)
  (handler-case
      (progn (fstat fd) t)
    (ebadf () nil)))

(defmacro repeat-upon-condition ((&rest conditions) &body body)
  (with-unique-names (block-name)
    `(loop :named ,block-name :do
       (ignore-some-conditions ,conditions
         (return-from ,block-name (progn ,@body))))))

(defmacro repeat-upon-eintr (&body body)
  `(repeat-upon-condition (eintr) ,@body))

(defmacro repeat-decreasing-timeout
    ((timeout-var timeout &optional (block-name nil blockp)) &body body)
  (unless (find timeout-var (flatten body))
    (warn "You probably want to use ~S inside the body ~A" timeout-var body))
  (unless blockp (setf block-name (gensym "BLOCK")))
  (with-unique-names (deadline temp-timeout)
    `(let* ((,timeout-var ,timeout)
            (,deadline (when ,timeout-var
                         (+ ,timeout-var (get-monotonic-time)))))
       (loop :named ,block-name :do
         ,@body
           (when ,deadline
             (let ((,temp-timeout (- ,deadline (get-monotonic-time))))
               (setf ,timeout-var
                     (if (plusp ,temp-timeout)
                         ,temp-timeout
                         0))))))))

(defmacro repeat-upon-condition-decreasing-timeout
    (((&rest conditions) timeout-var timeout &optional (block-name nil blockp)) &body body)
  (unless blockp (setf block-name (gensym "BLOCK")))
  `(repeat-decreasing-timeout (,timeout-var ,timeout ,block-name)
     (ignore-some-conditions ,conditions
       (return-from ,block-name (progn ,@body)))))
