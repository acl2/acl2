; Copyright David Rager, 2013

; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

(in-package "ACL2")

(include-book "common")

(defmodules *multiply-modules*
  (vl::make-vl-loadconfig
   :start-files (list "multiply.v")))

(defmacro multiply-thm (n)
  (let* ((n-str (coerce (explode-nonnegative-integer n 10 nil)
                        'string))

         (constant-name ;;; defining a constant is a bit silly, but having this
                        ;;; intermediate artifact to view
          (intern$ (concatenate 'string
                                "*MULTIPLY-"
                                n-str
                                "-MODULE*")

                   "ACL2"))
         (thm-name
          (intern$ (concatenate 'string
                                "MULTIPLY-" n-str "-CORRECT")

                   "ACL2"))
        (module-name (concatenate 'string
                                  "multiply" n-str))
        (test-vector-name
         (intern$ (concatenate 'string
                               "MULTIPLY-" n-str "-TEST-VECTOR")

                  "ACL2"))


        (test-vector-autohyps-name
          (intern$ (concatenate 'string
                                (symbol-name test-vector-name)
                                "-AUTOHYPS")

                   "ACL2"))
        (test-vector-autoins-name
          (intern$ (concatenate 'string
                                (symbol-name test-vector-name)
                                "-AUTOINS")

                   "ACL2"))
        (g-bindings
         `(gl::auto-bindings (:mix (:nat a ,n)
                                   (:nat b ,n)))))

    `(progn
       (defconst ,constant-name
         (vl::vl-module->esim
          (vl::vl-find-module ,module-name (vl::vl-translation->mods *multiply-modules*))))



       (defstv ,test-vector-name
         :mod ,constant-name
         :inputs
         '(("abus"   a)
           ("bbus"   b))
         :outputs
         '(("out"    res)))

       (def-gl-thm ,thm-name
         :hyp (,test-vector-autohyps-name)
         :concl (equal (let* ((in-alist  (,test-vector-autoins-name))
                              (out-alist (stv-run (,test-vector-name) in-alist))
                              (res       (cdr (assoc 'res out-alist))))
                         res)
                       (mod (* a b) (expt 2 ,n)))
         :g-bindings ,g-bindings))))


(multiply-thm 1)
(multiply-thm 2)
(multiply-thm 3)
(multiply-thm 4)
(multiply-thm 8) ; took 1.57 seconds with glucose 2.2 on modern, yet slow, laptop
(multiply-thm 10) ; took 86.11 seconds with glucose 2.2 on modern, yet slow, laptop

#|

; These are left as benchmarks for the future

(multiply-thm 12)
(multiply-thm 16)
(multiply-thm 32)
(multiply-thm 64)
(multiply-thm 128)
(multiply-thm 256)
(multiply-thm 512)
|#
