;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(defun full-cert-path (name)
  (merge-pathnames (concatenate 'string
                                "test/certs/"
                                name)
                   (asdf:component-pathname (asdf:find-system :cl+ssl.test))))

(defun load-cert(name)
  (let ((full-path (full-cert-path name)))
    (unless (probe-file full-path)
      (error "Unable to find certificate ~a~%Full path: ~a" name full-path))
    (cl+ssl:decode-certificate-from-file full-path)))

(defmacro with-cert ((name var) &body body)
  `(let* ((,var (load-cert ,name)))
     (when (cffi:null-pointer-p ,var)
       (error "Unable to load certificate: ~a" ,name))
     (unwind-protect
          (progn ,@body)
       (cl+ssl::x509-free ,var))))
