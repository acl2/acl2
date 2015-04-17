;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

#+xcvb (module (:depends-on ((:when (:featurep :sbcl) (:require :sb-posix)))))

(in-package :cl-user)

(defpackage :cl+ssl
  (:use :common-lisp :trivial-gray-streams)
  (:export #:*default-cipher-list*
           #:ensure-initialized
           #:reload
           #:stream-fd
           #:make-ssl-client-stream
           #:make-ssl-server-stream
           #:use-certificate-chain-file
           #:random-bytes
           #:ssl-check-verify-p
           #:ssl-load-global-verify-locations
           #:ssl-set-global-default-verify-paths
           #:ssl-error-verify
           #:ssl-error-stream
           #:ssl-error-code))
