; ACL2 Quicklisp Interface
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

;; NOTE: Normal ACL2 users should never need to run this.
;;       See update-libs.sh for more information.

(when (find-package "QL")
  ;; Not clear that we need to do this, but probably a good idea.
  (error "Quicklisp already installed?  You probably need to temporarily ~
          remove Quicklisp from your Lisp-specific initialization file, ~
          such as ~~/.sbclrc or ~~/ccl-init.lisp."))

(load "quicklisp.lsp")

(quicklisp-quickstart:install
 :path "temp-quicklisp-inst"
 ;; If you are behind a proxy you may need to add, e.g.,
 ;;   :proxy "http://proxy.nbc.com:80"
 )

;; Possibly of interest, if we need to go "back in time" to a previous
;; distribution:
;;
;;   http://blog.quicklisp.org/2011/08/going-back-in-dist-time.html
;;
;;  (ql-dist:available-versions (ql-dist:dist "quicklisp"))
;;
;;  (ql-dist:install-dist
;;   "http://beta.quicklisp.org/dist/quicklisp/2015-03-02/distinfo.txt"
;;   :replace t)

(ql:bundle-systems (list "bordeaux-threads"
                         "bt-semaphore"
                         "cl-fad"
                         "hunchentoot"
                         "osicat"
                         "uiop"
                         "html-template"
                         "shellpool"
                         ;; "external-program" ; removed Nov 2017 to avoid GPL

; On Nov 3, 2017, David Rager attempted to update quicklisp.  The update seemed
; to fail, because CFFI needed Babel.  But, that dependency wasn't registered
; with the quicklisp system (or something to that effect).  As such, we
; maually include Babel.  After some amount of time passes, this is likely to
; get fixed.
                         "babel"
                         
                         )
                   :to "./bundle")

(quit)
