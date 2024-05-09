;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

#+openmcl
(defmethod stream-deadline ((stream ccl::basic-stream))
  (ccl::ioblock-deadline (ccl::stream-ioblock stream t)))
#+openmcl
(defmethod stream-deadline ((stream t))
  nil)

;;; Waiting for output to be possible

#+clozure-common-lisp
(defun milliseconds-until-deadline (deadline stream)
  (let* ((now (get-internal-real-time)))
    (if (> now deadline)
        (error 'ccl::communication-deadline-expired :stream stream)
        (values
         (round (- deadline now) (/ internal-time-units-per-second 1000))))))

#+clozure-common-lisp
(defun output-wait (stream fd deadline)
  (unless deadline
    (setf deadline (stream-deadline (ssl-stream-socket stream))))
  (let* ((timeout
          (if deadline
              (milliseconds-until-deadline deadline stream)
              nil)))
    (multiple-value-bind (win timedout error)
        (ccl::process-output-wait fd timeout)
      (unless win
        (if timedout
            (error 'ccl::communication-deadline-expired :stream stream)
            (ccl::stream-io-error stream (- error) "write"))))))

(defun seconds-until-deadline (deadline)
  (/ (- deadline (get-internal-real-time))
     internal-time-units-per-second))

#+sbcl
(defun output-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
         ;; *deadline* is handled by wait-until-fd-usable automatically,
         ;; but we need to turn a user-specified deadline into a timeout
         (when deadline
           (seconds-until-deadline deadline))))
    (sb-sys:wait-until-fd-usable fd :output timeout)))

#+allegro
(eval-when (:compile-top-level :load-top-level :execute)
  (require :process))

#+allegro
(defun output-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
         (when deadline
           (seconds-until-deadline deadline))))
    (mp:process-wait-with-timeout "cl+ssl waiting for output"
                                  timeout
                                  'excl:write-no-hang-p
                                  fd)))

#-(or clozure-common-lisp sbcl allegro)
(defun output-wait (stream fd deadline)
  (declare (ignore stream fd deadline))
  ;; This situation means that the lisp set our fd to non-blocking mode,
  ;; and streams.lisp didn't know how to undo that.
  (warn "cl+ssl::output-wait is not implemented for this lisp, but a non-blocking stream is encountered"))


;;; Waiting for input to be possible

#+clozure-common-lisp
(defun input-wait (stream fd deadline)
  (unless deadline
    (setf deadline (stream-deadline (ssl-stream-socket stream))))
  (let* ((timeout
          (if deadline
              (milliseconds-until-deadline deadline stream)
              nil)))
    (multiple-value-bind (win timedout error)
        (ccl::process-input-wait fd timeout)
      (unless win
        (if timedout
            (error 'ccl::communication-deadline-expired :stream stream)
            (ccl::stream-io-error stream (- error) "read"))))))

#+sbcl
(defun input-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
         ;; *deadline* is handled by wait-until-fd-usable automatically,
         ;; but we need to turn a user-specified deadline into a timeout
         (when deadline
           (seconds-until-deadline deadline))))
    (sb-sys:wait-until-fd-usable fd :input timeout)))

#+allegro
(defun input-wait (stream fd deadline)
  (declare (ignore stream))
  (let ((timeout
         (when deadline
           (max 0 (seconds-until-deadline deadline)))))
    (mp:wait-for-input-available fd
                                 :timeout timeout
                                 :whostate "cl+ssl waiting for input")))

#+lispworks
(defun input-wait (stream fd deadline)
  (declare (ignore fd))

  (let* ((timeout
           (when deadline
             (max 0 (seconds-until-deadline deadline)))))
    (system:wait-for-input-streams (list (ssl-stream-socket stream))
                                   :timeout timeout
                                   :wait-reason "cl+ssl waiting for input")))

#-(or clozure-common-lisp sbcl allegro lispworks)
(defun input-wait (stream fd deadline)
  (declare (ignore stream fd deadline))
  ;; This situation means that the lisp set our fd to non-blocking mode,
  ;; and streams.lisp didn't know how to undo that.
  (warn "cl+ssl::input-wait is not implemented for this lisp, but a non-blocking stream is encountered"))

;;; Funcall wrapper

(declaim (inline ensure-ssl-funcall))
(defun ensure-ssl-funcall (stream success-test func handle &rest other-args)
  (loop
     (let ((ret
            (let ((*bio-socket* (ssl-stream-socket stream))) ;for Lisp-BIO callbacks
              (apply func handle other-args))))
       (when (funcall success-test ret)
         (return ret))
       (let ((error (ssl-get-error handle ret)))
         (case error
           (#.+ssl-error-want-read+
            (input-wait stream
                        (ssl-get-fd handle)
                        (ssl-stream-deadline stream)))
           (#.+ssl-error-want-write+
            (output-wait stream
                         (ssl-get-fd handle)
                         (ssl-stream-deadline stream)))
           (t
            (ssl-signal-error handle func error ret)))))))

(declaim (inline nonblocking-ssl-funcall))
(defun nonblocking-ssl-funcall (stream success-test func handle &rest other-args)
  (loop
     (let ((ret
            (let ((*bio-socket* (ssl-stream-socket stream))) ;for Lisp-BIO callbacks
              (apply func handle other-args))))
       (when (funcall success-test ret)
         (return ret))
       (let ((error (ssl-get-error handle ret)))
         (case error
           ((#.+ssl-error-want-read+ #.+ssl-error-want-write+)
            (return ret))
           (t
            (ssl-signal-error handle func error ret)))))))

