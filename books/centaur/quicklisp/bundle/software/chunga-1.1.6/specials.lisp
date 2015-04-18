;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/specials.lisp,v 1.12 2008/05/24 03:06:22 edi Exp $

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

(defmacro define-constant (name value &optional doc)
  "A version of DEFCONSTANT for, cough, /strict/ CL implementations."
  ;; See <http://www.sbcl.org/manual/Defining-Constants.html>
  `(defconstant ,name (if (boundp ',name) (symbol-value ',name) ,value)
     ,@(when doc (list doc))))

#+:lispworks
(editor:setup-indent "define-constant" 1 2 4)

(defconstant +output-buffer-size+ 8192
  "Size of the initial output buffer for chunked output.")

(define-constant +crlf+
  (make-array 2 :element-type '(unsigned-byte 8)
              :initial-contents (mapcar 'char-code '(#\Return #\Linefeed)))
  "A 2-element array consisting of the character codes for a CRLF
sequence.")

(define-constant +hex-digits+ '#.(coerce "0123456789ABCDEF" 'list)
  "The hexadecimal digits.")

(defvar *current-error-message* nil
  "Used by the parsing functions in `read.lisp' as an
introduction to a standardized error message about unexpected
characters unless it is NIL.")

(defvar *current-error-function* nil
  "Used by the functions in `read.lisp' as a function to signal
errors about unexpected characters when *CURRENT-ERROR-MESSAGE*
is NIL.")

(defvar *accept-bogus-eols* nil
  "Some web servers do not respond with a correct CRLF line ending for
HTTP headers but with a lone linefeed or carriage return instead.  If
this variable is bound to a true value, READ-LINE* will treat a lone
LF or CR character as an acceptable end of line.  The initial value is
NIL.")

(defvar *treat-semicolon-as-continuation* nil
  "According to John Foderaro, Netscape v3 web servers bogusly split
Set-Cookie headers over multiple lines which means that we'd have to
treat Set-Cookie headers ending with a semicolon as incomplete and
combine them with the next header.  This will only be done if this
variable has a true value, though.")

(defvar *char-buffer* nil
  "A `buffer' for one character.  Used by PEEK-CHAR* and
UNREAD-CHAR*.")

(pushnew :chunga *features*)

;; stuff for Nikodemus Siivola's HYPERDOC
;; see <http://common-lisp.net/project/hyperdoc/>
;; and <http://www.cliki.net/hyperdoc>
;; also used by LW-ADD-ONS

(defvar *hyperdoc-base-uri* "http://weitz.de/chunga/")

(let ((exported-symbols-alist
       (loop for symbol being the external-symbols of :chunga
             collect (cons symbol
                           (concatenate 'string
                                        "#"
                                        (string-downcase symbol))))))
  (defun hyperdoc-lookup (symbol type)
    (declare (ignore type))
    (cdr (assoc symbol
                exported-symbols-alist
                :test #'eq))))
