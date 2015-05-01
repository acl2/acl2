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

;;;; Extended by Kevin M. Rosenberg <kevin@rosenberg.net>:
;;;;   - .asd file
;;;;   - numerous speed optimizations
;;;;   - conversion to and from integers
;;;;   - Renamed functions now that supporting integer conversions
;;;;   - URI-compatible encoding using :uri key
;;;;
;;;; $Id$

(in-package #:cl-base64)

(defun round-next-multiple (x n)
  "Round x up to the next highest multiple of n."
  (declare (fixnum n)
           (optimize (speed 3) (safety 0) (space 0)))
  (let ((remainder (mod x n)))
    (declare (fixnum remainder))
    (if (zerop remainder)
        x
        (the fixnum (+ x (the fixnum (- n remainder)))))))

(defmacro def-*-to-base64-* (input-type output-type)
  `(defun ,(intern (concatenate 'string (symbol-name input-type)
                                (symbol-name :-to-base64-)
                                (symbol-name output-type)))
    (input
        ,@(when (eq output-type :stream)
                '(output))
        &key (uri nil) (columns 0))
     "Encode a string array to base64. If columns is > 0, designates
maximum number of columns in a line and the string will be terminated
with a #\Newline."
     (declare ,@(case input-type
                      (:string
                       '((string input)))
                      (:usb8-array
                       '((type (array (unsigned-byte 8) (*)) input))))
              (fixnum columns)
              (optimize (speed 3) (safety 0) (space 0)))
     (let ((pad (if uri *uri-pad-char* *pad-char*))
           (encode-table (if uri *uri-encode-table* *encode-table*)))
       (declare (simple-string encode-table)
                (character pad))
       (let* ((string-length (length input))
              (complete-group-count (truncate string-length 3))
              (remainder (nth-value 1 (truncate string-length 3)))
              (padded-length (* 4 (truncate (+ string-length 2) 3)))
              ,@(when (eq output-type :string)
                      '((num-lines (if (plusp columns)
                                       (truncate (+ padded-length (1- columns)) columns)
                                       0))
                        (num-breaks (if (plusp num-lines)
                                        (1- num-lines)
                                        0))
                        (strlen (+ padded-length num-breaks))
                        (result (make-string strlen))
                        (ioutput 0)))
              (col (if (plusp columns)
                       0
                       (the fixnum (1+ padded-length)))))
         (declare (fixnum string-length padded-length col
                          ,@(when (eq output-type :string)
                                  '(ioutput)))
                  ,@(when (eq output-type :string)
                          '((simple-string result))))
         (labels ((output-char (ch)
                    (if (= col columns)
                        (progn
                          ,@(case output-type
                                  (:stream
                                   '((write-char #\Newline output)))
                                 (:string
                                  '((setf (schar result ioutput) #\Newline)
                                    (incf ioutput))))
                          (setq col 1))
                     (incf col))
                 ,@(case output-type
                         (:stream
                          '((write-char ch output)))
                         (:string
                          '((setf (schar result ioutput) ch)
                            (incf ioutput)))))
               (output-group (svalue chars)
                 (declare (fixnum svalue chars))
                 (output-char
                  (schar encode-table
                         (the fixnum
                           (logand #x3f
                                   (the fixnum (ash svalue -18))))))
                 (output-char
                  (schar encode-table
                         (the fixnum
                           (logand #x3f
                                        (the fixnum (ash svalue -12))))))
                 (if (> chars 2)
                     (output-char
                      (schar encode-table
                             (the fixnum
                               (logand #x3f
                                       (the fixnum (ash svalue -6))))))
                     (output-char pad))
                   (if (> chars 3)
                       (output-char
                        (schar encode-table
                               (the fixnum
                                 (logand #x3f svalue))))
                       (output-char pad))))
        (do ((igroup 0 (the fixnum (1+ igroup)))
             (isource 0 (the fixnum (+ isource 3))))
            ((= igroup complete-group-count)
             (cond
               ((= remainder 2)
                (output-group
                 (the fixnum
                     (+
                      (the fixnum
                        (ash
                         ,(case input-type
                                (:string
                                 '(char-code (the character (char input isource))))
                                (:usb8-array
                                 '(the fixnum (aref input isource))))
                         16))
                      (the fixnum
                        (ash
                         ,(case input-type
                                (:string
                                 '(char-code (the character (char input
                                                                  (the fixnum (1+ isource))))))
                                (:usb8-array
                                 '(the fixnum (aref input (the fixnum
                                                            (1+ isource))))))
                         8))))
                 3))
               ((= remainder 1)
                (output-group
                 (the fixnum
                   (ash
                    ,(case input-type
                           (:string
                            '(char-code (the character (char input isource))))
                           (:usb8-array
                            '(the fixnum (aref input isource))))
                    16))
                 2)))
             ,(case output-type
                    (:string
                     'result)
                    (:stream
                     'output)))
          (declare (fixnum igroup isource))
          (output-group
           (the fixnum
             (+
              (the fixnum
                (ash
                 (the fixnum
                 ,(case input-type
                        (:string
                         '(char-code (the character (char input isource))))
                        (:usb8-array
                         '(aref input isource))))
                 16))
              (the fixnum
                (ash
                 (the fixnum
                   ,(case input-type
                          (:string
                           '(char-code (the character (char input
                                                            (the fixnum (1+ isource))))))
                        (:usb8-array
                         '(aref input (1+ isource)))))
                 8))
              (the fixnum
                ,(case input-type
                       (:string
                        '(char-code (the character (char input
                                                         (the fixnum (+ 2 isource))))))
                       (:usb8-array
                        '(aref input (+ 2 isource))))
                )))
           4)))))))

(def-*-to-base64-* :string :string)
(def-*-to-base64-* :string :stream)
(def-*-to-base64-* :usb8-array :string)
(def-*-to-base64-* :usb8-array :stream)


(defun integer-to-base64-string (input &key (uri nil) (columns 0))
  "Encode an integer to base64 format."
  (declare (integer input)
           (fixnum columns)
           (optimize (speed 3) (space 0) (safety 0)))
  (let ((pad (if uri *uri-pad-char* *pad-char*))
        (encode-table (if uri *uri-encode-table* *encode-table*)))
    (declare (simple-string encode-table)
             (character pad))
    (let* ((input-bits (integer-length input))
           (byte-bits (round-next-multiple input-bits 8))
           (padded-bits (round-next-multiple byte-bits 6))
           (remainder-padding (mod padded-bits 24))
           (padding-bits (if (zerop remainder-padding)
                             0
                             (- 24 remainder-padding)))
           (padding-chars (/ padding-bits 6))
           (padded-length (/ (+ padded-bits padding-bits) 6))
           (last-line-len (if (plusp columns)
                              (- padded-length (* columns
                                                  (truncate
                                                   padded-length columns)))
                              0))
           (num-lines (if (plusp columns)
                          (truncate (+ padded-length (1- columns)) columns)
                          0))
           (num-breaks (if (plusp num-lines)
                           (1- num-lines)
                           0))
           (strlen (+ padded-length num-breaks))
           (last-char (1- strlen))
           (str (make-string strlen))
           (col (if (zerop last-line-len)
                     columns
                    last-line-len)))
      (declare (fixnum padded-length num-lines col last-char
                       padding-chars last-line-len))
      (unless (plusp columns)
        (setq col -1)) ;; set to flag to optimize in loop

      (dotimes (i padding-chars)
        (declare (fixnum i))
        (setf (schar str (the fixnum (- last-char i))) pad))

      (do* ((strpos (- last-char padding-chars) (1- strpos))
            (int (ash input (/ padding-bits 3))))
           ((minusp strpos)
            str)
        (declare (fixnum strpos) (integer int))
        (cond
          ((zerop col)
           (setf (schar str strpos) #\Newline)
           (setq col columns))
          (t
           (setf (schar str strpos)
                 (schar encode-table (the fixnum (logand int #x3f))))
           (setq int (ash int -6))
           (decf col)))))))

(defun integer-to-base64-stream (input stream &key (uri nil) (columns 0))
  "Encode an integer to base64 format."
  (declare (integer input)
           (fixnum columns)
           (optimize (speed 3) (space 0) (safety 0)))
  (let ((pad (if uri *uri-pad-char* *pad-char*))
        (encode-table (if uri *uri-encode-table* *encode-table*)))
    (declare (simple-string encode-table)
             (character pad))
    (let* ((input-bits (integer-length input))
           (byte-bits (round-next-multiple input-bits 8))
           (padded-bits (round-next-multiple byte-bits 6))
           (remainder-padding (mod padded-bits 24))
           (padding-bits (if (zerop remainder-padding)
                             0
                             (- 24 remainder-padding)))
           (padding-chars (/ padding-bits 6))
           (padded-length (/ (+ padded-bits padding-bits) 6))
           (strlen padded-length)
           (nonpad-chars (- strlen padding-chars))
           (last-nonpad-char (1- nonpad-chars))
           (str (make-string strlen)))
      (declare (fixnum padded-length last-nonpad-char))
      (do* ((strpos 0 (the fixnum (1+ strpos)))
            (int (ash input (/ padding-bits 3)) (ash int -6))
            (6bit-value (the fixnum (logand int #x3f))
                        (the fixnum (logand int #x3f))))
           ((= strpos nonpad-chars)
            (let ((col 0))
              (declare (fixnum col))
              (dotimes (i nonpad-chars)
                (declare (fixnum i))
                (write-char (schar str i) stream)
                (when (plusp columns)
                  (incf col)
                  (when (= col columns)
                    (write-char #\Newline stream)
                    (setq col 0))))
              (dotimes (ipad padding-chars)
                (declare (fixnum ipad))
                (write-char pad stream)
                (when (plusp columns)
                  (incf col)
                  (when (= col columns)
                    (write-char #\Newline stream)
                    (setq col 0)))))
            stream)
        (declare (fixnum 6bit-value strpos)
                 (integer int))
        (setf (schar str (- last-nonpad-char strpos))
              (schar encode-table 6bit-value))
        ))))

