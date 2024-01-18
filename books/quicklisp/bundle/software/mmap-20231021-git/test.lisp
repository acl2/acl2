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

#+unix
(define-test read-fd
  :parent mmap
  (let (fd mmapped read)
    (finish
      (setf read (alexandria:read-file-into-string *this* :external-format :utf-8)))
    (of-type unsigned-byte
             (setf fd (mmap::u-open (uiop:native-namestring *this*) '(:read))))
    (finish
      (mmap:with-mmap (addr fd* size fd :size (length read) :dont-close t)
        (setf mmapped (cffi:foreign-string-to-lisp addr :count size :encoding :utf-8))))
    (is = 0 (mmap::u-close fd))
    (is string= read mmapped)))
