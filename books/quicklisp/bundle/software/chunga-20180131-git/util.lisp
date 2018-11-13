;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/util.lisp,v 1.12 2008/05/25 10:53:48 edi Exp $

;;; Copyright (c) 2006-2010, Dr. Edmund Weitz.  All rights reserved.

;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:

;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.

;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package :chunga)

#-:lispworks
(defmacro when-let ((var expr) &body body)
  "Evaluates EXPR, binds it to VAR, and executes BODY if VAR has
a true value."
  `(let ((,var ,expr))
     (when ,var ,@body)))

(defun ends-with-p (seq suffix &key (test #'char-equal))
  "Returns true if the sequence SEQ ends with the sequence
SUFFIX.  Individual elements are compared with TEST."
  (let ((mismatch (mismatch seq suffix :from-end t :test test)))
    (or (null mismatch)
        (= mismatch (- (length seq) (length suffix))))))

(defun make-keyword (string destructivep)
  "Converts the string STRING to a keyword where all characters are
uppercase or lowercase, taking into account the current readtable
case.  Destructively modifies STRING if DESTRUCTIVEP is true."
  (intern (funcall
           (if destructivep
             (if (eq (readtable-case *readtable*) :upcase)
               #'nstring-upcase
               #'nstring-downcase)
             (if (eq (readtable-case *readtable*) :upcase)
               #'string-upcase
               #'string-downcase))
           string)
          :keyword))

(defun read-char* (stream &optional (eof-error-p t) eof-value)
  "The streams we're dealing with are all binary with element type
\(UNSIGNED-BYTE 8) and we're only interested in ISO-8859-1, so we use
this to `simulate' READ-CHAR."
  (cond (*char-buffer*
         (prog1 *char-buffer*
           (setq *char-buffer* nil)))
        (t
         ;; this assumes that character codes are identical to Unicode code
         ;; points, at least for Latin1
         (let ((char-code (read-byte stream eof-error-p eof-value)))
           (and char-code
                (code-char char-code))))))

(defun unread-char* (char)
  "Were simulating UNREAD-CHAR by putting the character into
*CHAR-BUFFER*."
  ;; no error checking, only used internally
  (setq *char-buffer* char)
  nil)
  
(defun peek-char* (stream &optional eof-error-p eof-value)
  "We're simulating PEEK-CHAR by reading a character and putting it
into *CHAR-BUFFER*."
  ;; no error checking, only used internally  
  (setq *char-buffer* (read-char* stream eof-error-p eof-value)))

(defmacro with-character-stream-semantics (&body body)
  "Binds *CHAR-BUFFER* around BODY so that within BODY we can use
READ-CHAR* and friends \(see above) to simulate a character stream
although we're reading from a binary stream."
  `(let ((*char-buffer* nil))
     ,@body))
