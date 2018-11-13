;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(def-suite :cl+ssl.sni :in :cl+ssl
  :description "Server Name Indications tests")

(in-suite :cl+ssl.sni)

(defun make-request-to-sni-test-server (sni-enabled)
  (usocket:with-client-socket (socket stream "sni.velox.ch" 443
                                      :element-type '(unsigned-byte 8))
    (let* ((ssl-stream (cl+ssl:make-ssl-client-stream stream
                                                      :hostname (if sni-enabled "sni.velox.ch")))
           (char-stream (flexi-streams:make-flexi-stream ssl-stream
                                                         :external-format '(:utf-8 :eol-style :crlf)))
           (reply-buf (make-string 1000)))
      (unwind-protect
           (progn
             (format char-stream "GET / HTTP/1.1~%")
             (format char-stream "Host: sni.velox.ch~%~%")
             (finish-output char-stream)
             (read-sequence reply-buf char-stream)
             reply-buf)
        (close ssl-stream)))))

(defun sni-test-request-succeeded-p (response)
  (search "Great!" response))

(defun sni-test-request-failed-p (response)
  (search "Unfortunately" response))

;; Disable the SNI tests because sni.velox.ch was shut down and we
;; haven't found a replacement.
;;
;; (test (sni.disabled :compile-at :definition-time)
;;   (is-true (sni-test-request-failed-p (make-request-to-sni-test-server nil))
;;            "Request to SNI test server should've failed because SNI was disabled"))
;;
;; (test (sni.enabled :compile-at :definition-time)
;;   (is-true (sni-test-request-succeeded-p (make-request-to-sni-test-server t))
;;            "Request to SNI test server should've succeseeded because SNI was enabled"))
