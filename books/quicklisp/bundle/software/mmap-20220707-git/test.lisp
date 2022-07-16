#|
 This file is a part of mmap
 (c) 2017 Shirakumo http://tymoon.eu (shinmera@tymoon .eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defpackage #:mmap-test
  (:nicknames #:org.shirakumo.fraf.trial.mmap.test)
  (:use :cl :parachute))
(in-package #:org.shirakumo.fraf.trial.mmap.test)

(defvar *this* #.(or *compile-file-pathname* *load-pathname*
                     (error "COMPILE-FILE or LOAD this file.")))

(define-test mmap)

(define-test read-file
  :parent mmap
  (let (mmapped read)
    (finish
     (setf read (alexandria:read-file-into-string *this* :external-format :utf-8)))
    (finish
     (mmap:with-mmap (addr fd size *this*)
       (setf mmapped (cffi:foreign-string-to-lisp addr :count size :encoding :utf-8))))
    (is string= read mmapped)))
