;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; package.lisp --- Package definition.
;;;
;;; Copyright (c) 2007, Luis Oliveira  <loliveira@common-lisp.net>
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

(in-package #:cl-user)

(defpackage #:osicat-windows
  (:use #:common-lisp #:cffi #:osicat-sys)
  (:nicknames #:win)
  (:export
   #:+error-file-not-found+
   #:+error-success+
   #:+generic-all+
   #:+generic-execute+
   #:+generic-read+
   #:+generic-wrtie+
   #:close-handle
   #:create-file
   #:create-hard-link
   #:create-symbolic-link
   #:file-information-creation-time
   #:file-information-file-attributes
   #:file-information-file-index
   #:file-information-last-access-time
   #:file-information-last-write-time
   #:file-information-number-of-links
   #:file-information-volume-serial-number
   #:find-close
   #:find-data-file-name
   #:find-data-file-attributes
   #:find-first-file
   #:find-next-file
   #:get-file-information-by-handle
   #:get-file-type
   #:get-final-path-name-by-handle
   #:get-symbolic-link-target-by-handle
   #:handle-is-symbolic-link-p
   #:query-performance-counter
   #:win32-error
   #:with-create-file))
