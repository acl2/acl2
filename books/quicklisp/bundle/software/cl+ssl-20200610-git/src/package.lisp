;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
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
           #:*make-ssl-client-stream-verify-default*
           #:make-ssl-server-stream
           #:use-certificate-chain-file
           #:random-bytes
           ;; DEPRECATED.
           ;; Use the (MAKE-SSL-CLIENT-STREAM .. :VERIFY ?) to enable/disable verification.
           ;; MAKE-CONTEXT also allows to enab/disable verification.
           #:ssl-check-verify-p
           #:ssl-load-global-verify-locations
           #:ssl-set-global-default-verify-paths
           #:ssl-error-verify
           #:ssl-error-stream
           #:ssl-error-code
           #:ssl-error-initialize
           #:ssl-ctx-free

           #:with-pem-password

           #:+ssl-verify-none+
           #:+ssl-verify-peer+
           #:+ssl-verify-fail-if-no-peer-cert+
           #:+ssl-verify-client-once+

           #:+ssl-op-no-sslv2+
           #:+ssl-op-no-sslv3+
           #:+ssl-op-no-tlsv1+
           #:+ssl-op-no-tlsv1-1+
           #:+ssl-op-no-tlsv1-2+

           #:+ssl-sess-cache-off+
           #:+ssl-sess-cache-client+
           #:+ssl-sess-cache-server+
           #:+ssl-sess-cache-both+
           #:+ssl-sess-cache-no-auto-clear+
           #:+ssl-sess-cache-no-internal-lookup+
           #:+ssl-sess-cache-no-internal-store+
           #:+ssl-sess-cache-no-internal+
           
           #:make-context
           #:with-global-context

           ;; x509 stuff
           #:decode-certificate-from-file
           #:decode-certificate
           #:ssl-stream-x509-certificate

           ;; hostname-verification
           #:verify-hostname))
