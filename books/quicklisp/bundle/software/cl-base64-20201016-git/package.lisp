;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          package.lisp
;;;; Purpose:       Package definition for cl-base64
;;;; Programmer:    Kevin M. Rosenberg
;;;; Date Started:  Dec 2002
;;;;
;;;; $Id$
;;;;
;;;; *************************************************************************

(defpackage #:cl-base64
  (:nicknames #:base64)
  (:use #:cl)
  (:export #:base64-stream-to-integer
           #:base64-stream-to-string
           #:base64-stream-to-stream
           #:base64-stream-to-usb8-array
           #:base64-string-to-integer
           #:base64-string-to-string
           #:base64-string-to-stream
           #:base64-string-to-usb8-array
           #:string-to-base64-string
           #:string-to-base64-stream
           #:usb8-array-to-base64-string
           #:usb8-array-to-base64-stream
           #:stream-to-base64-string
           #:stream-to-base64-stream
           #:integer-to-base64-string
           #:integer-to-base64-stream

           ;; Conditions.
           #:base64-error
           #:bad-base64-character
           #:incomplete-base64-data

           ;; For creating custom encode/decode tables.
           #:make-decode-table
           #:+decode-table+
           #:+uri-decode-table+
           ;; What's the point of exporting these?
           #:*uri-encode-table*
           #:*uri-decode-table*
           ))

(in-package #:cl-base64)

(eval-when (:compile-toplevel :load-toplevel :execute)
(defvar *encode-table*
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")
(declaim (type simple-string *encode-table*))

(defvar *uri-encode-table*
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_")
(declaim (type simple-string *uri-encode-table*))

(defvar *pad-char* #\=)
(defvar *uri-pad-char* #\.)
(declaim (type character *pad-char* *uri-pad-char*))

  (deftype decode-table () '(simple-array (signed-byte 8) (128)))
  (defun make-decode-table (encode-table pad-char
                            &key (whitespace-chars
                                  '(#\Linefeed #\Return #\Space #\Tab)))
    (assert (< (length encode-table) 128)
            (encode-table)
            "Encode table too big: ~S" encode-table)
    (let ((dt (make-array 128 :element-type '(signed-byte 8)
                              :initial-element -1)))
      (declare (type decode-table dt))
      (loop for char across encode-table
            for index upfrom 0
            do (setf (aref dt (char-code char)) index))
      (setf (aref dt (char-code pad-char)) -2)
      (loop for char in whitespace-chars
            do (setf (aref dt (char-code char)) -3))
      dt)))

(defconstant +decode-table+
  (if (boundp '+decode-table+)
      (symbol-value '+decode-table+)
      (make-decode-table *encode-table* *pad-char*)))
(defvar *decode-table* +decode-table+ "Deprecated.")
(declaim (type decode-table +decode-table+ *decode-table*))

(defconstant +uri-decode-table+
  (if (boundp '+uri-decode-table+)
      (symbol-value '+uri-decode-table+)
      (make-decode-table *uri-encode-table* *uri-pad-char*)))
(defvar *uri-decode-table* +uri-decode-table+ "Deprecated.")
(declaim (type decode-table +uri-decode-table+ *uri-decode-table*))
