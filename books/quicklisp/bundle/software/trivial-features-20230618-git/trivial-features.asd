;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Package: ASDF; Base: 10; -*-
;;;; The above modeline is required for Genera. Do not change.
;;;
;;; trivial-features.asd --- ASDF system definition.
;;;
;;; Copyright (C) 2007, Luis Oliveira  <loliveira@common-lisp.net>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

#-(or sbcl clisp allegro openmcl mcl mkcl lispworks ecl cmu scl cormanlisp abcl xcl mocl clasp mezzano genera)
(error "Sorry, your Lisp is not supported.  Patches welcome.")

(defsystem trivial-features
  :description "Ensures consistent *FEATURES* across multiple CLs."
  :author "Luis Oliveira <loliveira@common-lisp.net>"
  :licence "MIT"
  :components
  ((:module src
    :serial t
    :components
    ((:file "tf-allegro" :if-feature :allegro)
     (:file "tf-clisp" :if-feature :clisp)
     (:file "tf-cmucl" :if-feature :cmu)
     (:file "tf-cormanlisp" :if-feature :cormanlisp)
     (:file "tf-ecl" :if-feature :ecl)
     (:file "tf-genera" :if-feature :genera)
     (:file "tf-lispworks" :if-feature :lispworks)
     (:file "tf-openmcl" :if-feature :openmcl)
     (:file "tf-mcl" :if-feature :mcl)
     (:file "tf-mkcl" :if-feature :mkcl)
     (:file "tf-sbcl" :if-feature :sbcl)
     (:file "tf-scl" :if-feature :scl)
     (:file "tf-abcl" :if-feature :abcl)
     (:file "tf-xcl" :if-feature :xcl)
     (:file "tf-mocl" :if-feature :mocl)
     (:file "tf-clasp" :if-feature :clasp)
     (:file "tf-mezzano" :if-feature :mezzano)))))

#-(or genera mezzano)
(defmethod perform ((o test-op) (c (eql (find-system 'trivial-features))))
  (operate 'load-op 'trivial-features-tests)
  (operate 'test-op 'trivial-features-tests))
