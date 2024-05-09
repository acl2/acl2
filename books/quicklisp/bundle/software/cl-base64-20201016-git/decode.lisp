;;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          encode.lisp
;;;; Purpose:       cl-base64 encoding routines
;;;; Programmer:    Kevin M. Rosenberg
;;;; Date Started:  Dec 2002
;;;;
;;;; $Id$
;;;;
;;;; This file implements the Base64 transfer encoding algorithm as
;;;; defined in RFC 1521 by Borensten & Freed, September 1993.
;;;; See: http://www.ietf.org/rfc/rfc1521.txt
;;;;
;;;; Based on initial public domain code by Juri Pakaste <juri@iki.fi>
;;;;
;;;; Copyright 2002-2003 Kevin M. Rosenberg
;;;; Permission to use with BSD-style license included in the COPYING file
;;;; *************************************************************************

(in-package #:cl-base64)

(define-condition base64-error (error)
  ((input
    :initarg :input
    :reader base64-error-input)
   (position
    :initarg :position
    :reader base64-error-position
    :type unsigned-byte)))

(define-condition bad-base64-character (base64-error)
  ((code :initarg :code :reader bad-base64-character-code))
  (:report (lambda (condition stream)
             (format stream "Bad character ~S at index ~D of ~S"
                     (code-char (bad-base64-character-code condition))
                     (base64-error-position condition)
                     (base64-error-input condition)))))

(define-condition incomplete-base64-data (base64-error)
  ()
  (:report (lambda (condition stream)
             (format stream "Unexpected end of Base64 data at index ~D of ~S"
                     (base64-error-position condition)
                     (base64-error-input condition)))))

(deftype array-index (&optional (length array-dimension-limit))
  `(integer 0 (,length)))

(deftype array-length (&optional (length array-dimension-limit))
  `(integer 0 ,length))

(deftype character-code ()
  `(integer 0 (,char-code-limit)))

(defmacro etypecase/unroll ((var &rest types) &body body)
  #+sbcl `(etypecase ,var
            ,@(loop for type in types
                    collect `(,type ,@body)))
  #-sbcl `(locally
              (declare (type (or ,@types) ,var))
            ,@body))

(defmacro let/typed ((&rest vars) &body body)
  `(let ,(loop for (var value) in vars
               collect (list var value))
     (declare ,@(loop for (var nil type) in vars
                      when type
                        collect (list 'type type var)))
     ,@body))

(defmacro define-base64-decoder (hose sink)
  `(defun ,(intern (format nil "~A-~A-~A-~A" '#:base64 hose '#:to sink))
       (input &key (table +decode-table+)
                   (uri nil)
                   ,@(when (eq sink :stream) `(stream))
                   (whitespace :ignore))
     ,(format nil "~
Decode Base64 ~(~A~) to ~(~A~).

TABLE is the decode table to use.  Two decode tables are provided:
+DECODE-TABLE+ (used by default) and +URI-DECODE-TABLE+.  See
MAKE-DECODE-TABLE.

For backwards-compatibility the URI parameter is supported.  If it is
true, then +URI-DECODE-TABLE+ is used, and the value for TABLE
parameter is ignored.

WHITESPACE can be one of:

  :ignore - Whitespace characters are ignored (default).
  :signal - Signal a BAD-BASE64-CHARACTER condition using SIGNAL.
  :error  - Signal a BAD-BASE64-CHARACTER condition using ERROR."
              hose sink)
     (declare (optimize (speed 3) (safety 1))
              (type decode-table table)
              (type ,(ecase hose
                       (:stream 'stream)
                       (:string 'string))
                    input))
     (let/typed ((decode-table (if uri +uri-decode-table+ table)
                               decode-table)
                 ,@(ecase sink
                     (:stream)
                     (:usb8-array
                      (ecase hose
                        (:stream
                         `((result (make-array 1024
                                 :element-type '(unsigned-byte 8)
                                               :adjustable t
                                               :fill-pointer 0)
                                   (array (unsigned-byte 8) (*)))))
                        (:string
                         `((result (make-array (* 3 (ceiling (length input) 4))
                                               :element-type '(unsigned-byte 8))
                                   (simple-array (unsigned-byte 8) (*)))
                           (rpos 0 array-index)))))
                          (:string
                      (case hose
                      (:stream
                         `((result (make-array 1024
                                               :element-type 'character
                                               :adjustable t
                                               :fill-pointer 0)
                                   (array character (*)))))
                        (:string
                         `((result (make-array (* 3 (ceiling (length input) 4))
                                               :element-type 'character)
                                   (simple-array character (*)))
                           (rpos 0 array-index)))))
                     (:integer
                      `((result 0 unsigned-byte)))))
       (flet ((bad-char (pos code &optional (action :error))
                (let ((args (list 'bad-base64-character
                                  :input input
                                  :position pos
                                  :code code)))
                  (ecase action
                    (:error
                     (apply #'error args))
                    (:cerror
                     (apply #'cerror "Ignore the error and continue." args))
                    (:signal
                     (apply #'signal args)))))
              (incomplete-input (pos)
                (error 'incomplete-base64-data :input input :position pos)))
         ,(let ((body
                  `(let/typed ((ipos 0 array-index)
                               (bitstore 0 (unsigned-byte 24))
                               (bitcount 0 (integer 0 14))
                               (svalue -1 (signed-byte 8))
                               (padchar 0 (integer 0 3))
                               (code 0 fixnum))
                     (loop
                       ,@(ecase hose
                           (:string
                            `((if (< ipos length)
                                  (setq code (char-code (aref input ipos)))
                                  (return))))
                           (:stream
                            `((let ((char (read-char input nil nil)))
                                (if char
                                    (setq code (char-code char))
                                    (return))))))
             (cond
                           ((or (< 127 code)
                                (= -1 (setq svalue (aref decode-table code))))
                            (bad-char ipos code))
                           ((= -2 svalue)
                            (cond ((<= (incf padchar) 2)
                                   (unless (<= 2 bitcount)
                                     (bad-char ipos code))
                                   (decf bitcount 2))
                                  (t
                                   (bad-char ipos code))))
                           ((= -3 svalue)
                            (ecase whitespace
                              (:ignore
                               ;; Do nothing.
                               )
                              (:error
                               (bad-char ipos code :error))
                              (:signal
                               (bad-char ipos code :signal))))
                           ((not (zerop padchar))
                            (bad-char ipos code))
                           (t
                            (setf bitstore (logior (the (unsigned-byte 24)
                                                        (ash bitstore 6))
                                svalue))
                (incf bitcount 6)
                (when (>= bitcount 8)
                  (decf bitcount 8)
                              (let ((byte (logand (the (unsigned-byte 24)
                                                       (ash bitstore (- bitcount)))
                                                  #xFF)))
                                (declare (type (unsigned-byte 8) byte))
                                ,@(ecase sink
                           (:usb8-array
                                     (ecase hose
                                       (:string
                                        `((setf (aref result rpos) byte)
                                          (incf rpos)))
                           (:stream
                                        `((vector-push-extend byte result)))))
                     (:string
                                     (ecase hose
                          (:string
                                        `((setf (schar result rpos)
                                                (code-char byte))
                                          (incf rpos)))
                                       (:stream
                                        `((vector-push-extend (code-char byte)
                                                              result)))))
                                    (:integer
                                     `((setq result
                                             (logior (ash result 8) byte))))
                                    (:stream
                                     '((write-char (code-char byte) stream)))))
                              (setf bitstore (logand bitstore #xFF)))))
                         (incf ipos))
                     (unless (zerop bitcount)
                       (incomplete-input ipos))
                     ,(ecase sink
                        ((:string :usb8-array)
                         (ecase hose
                            (:string
                            `(if (= rpos (length result))
                                 result
                                 (subseq result 0 rpos)))
                            (:stream
                            `(copy-seq result))))
                        (:integer
                         'result)
                        (:stream
                         'stream)))))
            (ecase hose
              (:string
               `(let ((length (length input)))
                  (declare (type array-length length))
                  (etypecase/unroll (input simple-base-string
                                           simple-string
                                           string)
                    ,body)))
              (:stream
               body)))))))

(define-base64-decoder :string :usb8-array)
(define-base64-decoder :string :string)
(define-base64-decoder :string :integer)
(define-base64-decoder :string :stream)

(define-base64-decoder :stream :usb8-array)
(define-base64-decoder :stream :string)
(define-base64-decoder :stream :integer)
(define-base64-decoder :stream :stream)

;; input-mode can be :string or :stream
;; input-format can be :character or :usb8
