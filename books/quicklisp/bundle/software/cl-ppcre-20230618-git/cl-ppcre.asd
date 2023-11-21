;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CL-USER; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/cl-ppcre/cl-ppcre.asd,v 1.49 2009/10/28 07:36:15 edi Exp $

;;; This ASDF system definition was kindly provided by Marco Baringer.

;;; Copyright (c) 2002-2009, Dr. Edmund Weitz.  All rights reserved.

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

(defsystem :cl-ppcre
  :version "2.1.1"
  :description "Perl-compatible regular expression library"
  :author "Dr. Edi Weitz"
  :license "BSD"
  :serial t
  :components ((:file "packages")
               (:file "specials")
               (:file "util")
               (:file "errors")
               (:file "charset")
               (:file "charmap")
               (:file "chartest")
               (:file "lexer" :if-feature (:not :use-acl-regexp2-engine))
               (:file "parser" :if-feature (:not :use-acl-regexp2-engine))
               (:file "regex-class" :if-feature (:not :use-acl-regexp2-engine))
               (:file "regex-class-util" :if-feature (:not :use-acl-regexp2-engine))
               (:file "convert" :if-feature (:not :use-acl-regexp2-engine))
               (:file "optimize" :if-feature (:not :use-acl-regexp2-engine))
               (:file "closures" :if-feature (:not :use-acl-regexp2-engine))
               (:file "repetition-closures" :if-feature (:not :use-acl-regexp2-engine))
               (:file "scanner" :if-feature (:not :use-acl-regexp2-engine))
               (:file "api"))
  :in-order-to ((test-op (test-op :cl-ppcre/test))))

(defsystem :cl-ppcre/test
  :description "Perl-compatible regular expression library tests"
  :author "Dr. Edi Weitz"
  :license "BSD"
  :depends-on (:cl-ppcre :flexi-streams)
  :components ((:module "test"
                        :serial t
                        :components ((:file "packages")
                                     (:file "tests")
                                     (:file "perl-tests"))))
  :perform (test-op (o c)
             (funcall (intern (symbol-name :run-all-tests)
                              (find-package :cl-ppcre-test)))))
