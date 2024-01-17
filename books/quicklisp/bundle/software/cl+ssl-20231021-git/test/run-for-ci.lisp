;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

;;;; This script is intended to be LOAD'ed to execute tests
;;;; in the CI environment, like GitHub Actions.
;;;;
;;;; As input it accepts some environment variables, see the code.
;;;; Logs it's actions to standard output.
;;;; Exit code of the script indicates test success = 0 or failure = 1.

(unless (uiop:getenvp "OPENSSL")
  (error "The OPENSSL environment variable is required"))
(unless (uiop:getenvp "BITS")
  (error "The BITS environment variable is required"))
(unless (uiop:getenvp "OPENSSL_RELEASES_BIN_DIR")
  (error "The OPENSSL_RELEASES_BIN_DIR environment variable is required"))

(when (uiop:getenvp "READTABLE_CASE_INVERT")
  (format t "changing readtable-case to :invert~%")
  (setq *readtable*
        (let ((rt (copy-readtable)))
          (setf (readtable-case rt) :invert)
          rt)))

(format t "(lisp-implementation-type): ~A~%" (lisp-implementation-type))
(format t "(lisp-implementation-version): ~A~%" (lisp-implementation-version))
(format t "*features*: ~A~%" *features*)
(format t "(asdf:asdf-version): ~A~%" (asdf:asdf-version))
(format t "(funcall asdf::*output-translation-function* \"/a/b.lisp\"): ~A~%"
        (funcall asdf::*output-translation-function* "/a/b.lisp"))

;;; make sure ASDF will find the cl+ssl version from this repository

(defparameter *this-dir*
  (make-pathname :name nil :type nil :defaults *load-truename*))
(defparameter *parent-dir*
  ;; Maybe getting parent dir this way is not not portable,
  ;; but should work for Linux.
  ;; TODO: probably use the portable code from cl-fad:pathname-parent-directory
  ;;     https://github.com/edicl/cl-fad/blob/3f4d32d3aa1093966046d001411a852eb8f4b535/fad.lisp#L328
  (merge-pathnames "../" *this-dir*))
(pushnew *parent-dir*  asdf:*central-registry* :test #'equal)

#+abcl
(progn
  (format t "Loading abcl-asdf and switching maven repo URL to HTTPS (see https://github.com/armedbear/abcl/issues/151)~%")
  (require :abcl-contrib)
  (format t "abcl-contrib loaded...~%")
  (require :abcl-asdf)
  (format t "abcl-asdf loaded...~%")
  (format t "*features*: ~A~%" *features*)
  (setf (symbol-value (read-from-string "abcl-asdf::*default-repository*"))
        "https://repo1.maven.org/maven2/")
  (format t "abcl-asdf::*default-repository* assigned the HTTPS URL.~%"))

(ql:quickload :cffi)
(format t "cffi loaded.~%")

(ql:quickload :cl+ssl/config)
(format t "cl+ssl/config loaded.~%")


(let* ((openssl (uiop:getenv "OPENSSL"))
       (bits (uiop:getenv "BITS"))
       (openssl-releases-bin-dir (uiop:getenv "OPENSSL_RELEASES_BIN_DIR"))
       (lib-dir (format nil
                        "~A/~A-~Abit/lib~A"
                        openssl-releases-bin-dir
                        openssl
                        bits
                        (if (and (string= "64" bits)
                                 (search "openssl-3." openssl))
                            "64"
                            ""))))
  (defparameter *libcrypto.so* (concatenate 'string  lib-dir "/libcrypto.so"))
  (defparameter *libssl.so* (concatenate 'string lib-dir "/libssl.so")))

(let ((lib-load-mode (uiop:getenvp "LIB_LOAD_MODE")))
  (cond ((string= "new" lib-load-mode)
         (cl+ssl/config:define-libcrypto-path #.*libcrypto.so*)
         (cl+ssl/config:define-libssl-path #.*libssl.so*))
        ((string= "old" lib-load-mode)
         (cffi:load-foreign-library *libcrypto.so*)
         (format t "libcrypto.so loaded.~%")
         (cffi:load-foreign-library *libssl.so*)
         (format t "libssl.so loaded.~%")
         (pushnew :cl+ssl-foreign-libs-already-loaded *features*))
        (t
         (format t "Unexpected LIB_LOAD_MODE value: ~A~%" lib-load-mode)
         (uiop:quit 1))))

;;; load cl+ssl separately from cl+ssl.test only because cl+ssl.test can not be loaded in the :invert readtable-case due to its dependency ironclad, as of 2019-10-20
(format t
        "Loading cl+ssl from ~A~%"
        (asdf:system-source-file (asdf:find-system :cl+ssl)))
(ql:quickload :cl+ssl :verbose t)
(format t "cl+ssl loaded.~%")

(when (uiop:getenvp "READTABLE_CASE_INVERT")
  (format t "restoring readtable-case to :upcase before loading cl+ssl.test~%")
  (setf (readtable-case *readtable*) :upcase))
(ql:quickload :cl+ssl.test)

(format t "(cl+ssl::compat-openssl-version): ~A~%" (cl+ssl::compat-openssl-version))

;; Since we load customly built openssl libs, it may not find the path
;; to trusted root serts on our system. Let's configure this path, as
;; we have it on my Ubunto and in the CI docker image.
(cl+ssl:ensure-initialized) ; needed to set the *ssl-global-context*
(cl+ssl::ssl-ctx-set-verify-location cl+ssl::*ssl-global-context* "/etc/ssl/certs/")

(let ((results
        #+ sbcl
        (coveralls:with-coveralls (:exclude "test")
          (5am:run :cl+ssl))
        #- sbcl
        (5am:run :cl+ssl)
        ))
  (5am:explain! results)
  (unless (5am:results-status results)
    (uiop:quit 1)))

(uiop:quit 0)
