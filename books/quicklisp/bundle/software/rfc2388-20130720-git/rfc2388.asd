;;;; -*- mode: LISP; -*-
;;;; Copyright (c) 2003 Janis Dzerins
;;;;
;;;; Redistribution and use in source and binary forms, with or without
;;;; modification, are permitted provided that the following conditions
;;;; are met:
;;;; 1. Redistributions of source code must retain the above copyright
;;;;    notice, this list of conditions and the following disclaimer.
;;;; 2. Redistributions in binary form must reproduce the above copyright
;;;;    notice, this list of conditions and the following disclaimer in the
;;;;    documentation and/or other materials provided with the distribution.
;;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;;;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;;;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;;;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;;;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;;;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;;;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;;;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;;;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;;;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(asdf:defsystem :rfc2388
  :author "Janis Dzerins <jonis@latnet.lv>"
  :version "1.5"
  :licence "Simplified BSD"
  :description "Implementation of RFC 2388"
  :long-description "
Contains an implementation of RFC 2388, which is used to process form data
posted with HTTP POST method using enctype \"multipart/form-data\"."
  :components ((:static-file "rfc2388.asd")
               (:file "rfc2388" :depends-on ("packages"))
               (:file "packages")))
