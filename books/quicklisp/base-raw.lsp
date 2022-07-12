; ACL2 Quicklisp Interface
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")


; It may be that we should do this for all Lisps instead of just Allegro.
#+(or allegro lispworks)
(load "bundle/asdf.lisp")

; Preload (i.e., compile) all Quicklisp libraries that we're making available.
; The goal here is to defeat build parallelism and ensure that the packages are
; loaded in a serial manner.  Otherwise, e.g., we can have two Quicklisp
; packages that are both being built at separate times in separate threads,
; crashing into each other's working space.

;; #-sbcl
(defmacro load-system-from-acl2-quicklisp-bundle (name)
  `(asdf:load-system ,name))

;; [westfold] This was fixed in 2016
;; #+sbcl
;; (defmacro load-system-from-acl2-quicklisp-bundle (name)
;;   ;; [Jared] Gross hack.
;;   ;;
;;   ;; Development versions of SBCL from 1.3.1.108-e9046da through at least SBCL
;;   ;; 1.3.1.185-bb7a213 seem to have a bug that is provoked by loading CL+SSL
;;   ;; (included via hunchentoot) when the optimize settings are set to a high
;;   ;; level, as they are in ACL2.  For details and status on this bug see
;;   ;; #1530390:
;;   ;;
;;   ;;    https://bugs.launchpad.net/sbcl/+bug/1530390
;;   ;;
;;   ;; As a workaround, if we are using SBCL, then explicitly set the compiler
;;   ;; policy to something less aggressive, which seems to avoid the problem.
;;   ;; When the SBCL bug is fixed, I think we should feel free to get rid of this
;;   ;; hack.
;;   `(cl:with-compilation-unit
;;      (:policy '(optimize (speed 1)
;;                          (space 1)
;;                          (safety 1)
;;                          (debug 1)
;;                          (compilation-speed 1)))
;;      (sb-ext:restrict-compiler-policy 'safety 1)
;;      (sb-ext:restrict-compiler-policy 'space 1)
;;      (sb-ext:restrict-compiler-policy 'speed 1)
;;      (sb-ext:restrict-compiler-policy 'debug 1)
;;      (sb-ext:restrict-compiler-policy 'compilation-speed 1)
;;      (asdf:load-system ,name)))

(load-system-from-acl2-quicklisp-bundle "bordeaux-threads")
(load-system-from-acl2-quicklisp-bundle "bt-semaphore")
(load-system-from-acl2-quicklisp-bundle "cl-fad")
;; (load-system-from-acl2-quicklisp-bundle "external-program") ; removed Nov 2017

; [Jared] it looks like there's a difference between how allegro prints numbers
; which causes some of the tests here to fail.  I'll need to update fastnumio
; to fix that.  For now just don't include it on Allegro.  Actually it looks
; like there may be bugs on CMUCL also.
#+(and (not cmucl)
       (not allegro))
(load-system-from-acl2-quicklisp-bundle "fastnumio")

(load-system-from-acl2-quicklisp-bundle "html-template")

#+cmucl
; [Jared] temporary workaround.  CL+SSL apparently fails to load on my system
; due to an incompatible OpenSSL version. See also:
;    https://github.com/cl-plus-ssl/cl-plus-ssl/issues/33
;
; Hopefully this will be fixed after the next Quicklisp release.
(push :hunchentoot-no-ssl *features*)


#-mswindows ;; [harshrc 2017-05-30] SSL library load error on Windows
(load-system-from-acl2-quicklisp-bundle "hunchentoot")

(load-system-from-acl2-quicklisp-bundle "osicat")
(load-system-from-acl2-quicklisp-bundle "shellpool")
(load-system-from-acl2-quicklisp-bundle "uiop")
