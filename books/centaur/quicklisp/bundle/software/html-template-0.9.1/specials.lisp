;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: HTML-TEMPLATE; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/html-template/specials.lisp,v 1.24 2007/03/09 13:09:16 edi Exp $

;;; Copyright (c) 2003-2007, Dr. Edmund Weitz. All rights reserved.

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

(in-package #:html-template)

(defvar *find-string-hash* (make-hash-table :test #'equal)
  "Hash tables used internally by READ-UNTIL to cache offset arrays.")

(defvar *template-start-marker* "<!--"
  "The string template tags must start with")
(defvar *template-end-marker* "-->"
  "The string template tags must end with")

(defvar *printer-hash* (make-hash-table :test #'equal)
  "The cache for template printers.
Each entry is of the form (PRINTER . WRITE-DATE).")

(defvar *default-template-pathname* (make-pathname)
  "Each pathname is merged with this value before it is used by
CREATE-TEMPLATE-PRINTER.")

(defvar *default-template-output* *standard-output*
  "The output stream used by FILL-AND-PRINT-TEMPLATE when no STREAM
keyword was provided.")

(defvar *template-output* nil
  "The output stream that's used internally.")

(defvar *convert-nil-to-empty-string* t
  "Controls whether NIL values should resolve to empty strings or
raise an error.")

(defvar *format-non-strings* t
  "Controls whether TMPL_VAR will accept values which aren't
strings and convert them using \(FORMAT NIL \"~A\" ...).")

(defvar *sequences-are-lists* t
  "Controls whether TMPL_LOOP printers expect lists or vectors.")

(defvar *upcase-attribute-strings* t
  "Controls whether attribute strings associated with template tags
are upcased before they are interned.")

(defvar *no-cache-check* nil
  "Controls whether the FILE-WRITE-DATE check will be circumvented
when using FILL-AND-PRINT-TEMPLATE.")

(defvar *template-symbol-package* (find-package '#:keyword)
  "The package symbols are interned into.")

(defvar *ignore-empty-lines* nil
  "Controls whether template tags on their own lines produce empty
lines or not.")

(defvar *warn-on-creation* t
  "Controls whether a warning should be signaled if a new template
printer is created from a pathname argument.")

(defvar *current-line* 1
  "Internal line counter of the parser.")
(defvar *current-column* 0
  "Internal column counter of the parser.")

(defvar *included-files* nil
  "Internally used by CREATE-TEMPLATE-PRINTER-AUX to avoid infinite
TMPL_INCLUDE loops.")

(defvar *external-format* :default
  "The external format used when opening files.")

(defvar *value-access-function*
  (lambda (symbol values &optional in-loop-p)
    (let ((result (getf values symbol)))
      (cond ((and in-loop-p *sequences-are-lists*)
             (loop for element in result
                   when (and element (listp element))
                     ;; keep values from upper levels
                     collect (append element values)
                   else
                     collect element))
            (t result))))
  "The function which associates \(attribute) symbols with their
values.")

(defvar *call-template-access-function* #'car
  "Accessor function for extracting the called template from a
TMPL_CALL form.")

(defvar *call-value-access-function* #'cdr
  "Accessor function for extracting the values from a TMPL_CALL
form.")

(defvar *force-default* nil
  "The default value for the FORCE keyword argument to
CREATE-TEMPLATE-PRINTER.")

(defvar *string-modifier* 'escape-string-iso-8859-1
  "The function which is applied to strings which replace
TMPL_VAR tags.  Use #'CL:IDENTITY if you don't want to change the
strings.")

(defparameter *escape-char-p*
  #'(lambda (char)
      (or (find char "<>&'\"")
          (> (char-code char) 127)))
  "Used by ESCAPE-STRING to test whether a character should be escaped.")

;; stuff for Nikodemus Siivola's HYPERDOC
;; see <http://common-lisp.net/project/hyperdoc/>
;; and <http://www.cliki.net/hyperdoc>
;; also used by LW-ADD-ONS

(defvar *hyperdoc-base-uri* "http://weitz.de/html-template/")

(let ((exported-symbols-alist
       (loop for symbol being the external-symbols of :html-template
             collect (cons symbol
                           (concatenate 'string
                                        "#"
                                        (string-downcase symbol))))))
  (defun hyperdoc-lookup (symbol type)
    (declare (ignore type))
    (cdr (assoc symbol
                exported-symbols-alist
                :test #'eq))))
