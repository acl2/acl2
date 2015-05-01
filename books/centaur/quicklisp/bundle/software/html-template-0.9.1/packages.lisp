;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CL-USER; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/html-template/packages.lisp,v 1.19 2007/01/01 23:49:16 edi Exp $

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

(in-package :cl-user)

(defpackage :html-template
  (:nicknames :template)
  (:use :cl)
  (:export :*call-template-access-function*
	   :*call-values-access-function*
	   :*convert-nil-to-empty-string*
           :*default-template-output*
           :*default-template-pathname*
           :*escape-char-p*
           :*force-default*
           :*format-non-strings*
           :*ignore-empty-lines*
           :*no-cache-check*
           :*sequences-are-lists*
           :*string-modifier*
           :*template-end-marker*
           :*template-start-marker*
           :*template-symbol-package*
           :*upcase-attribute-strings*
           :*value-access-function*
           :*warn-on-creation*
           :clear-template-cache
           :create-template-printer
           :delete-from-template-cache
           :escape-string
           :escape-string-all
           :escape-string-iso-8859-1
           :escape-string-minimal
           :escape-string-minimal-plus-quotes
           :fill-and-print-template
           :template-error
           :template-invocation-error
           :template-missing-value-error
           :template-not-a-string-error
           :template-not-a-string-error-value
           :template-syntax-error
           :template-syntax-error-col
           :template-syntax-error-line
           :template-syntax-error-stream))

(pushnew :html-template *features*)