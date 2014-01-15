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

(defmodules *divide-modules*
  (vl::make-vl-loadconfig
   :start-files (list "divide.v")))

(defmacro divide-thm (n)
  (let* ((n-str (str::natstr n))

         (constant-name ;;; defining a constant is a bit silly, but having this
                        ;;; intermediate artifact to view
          (intern$ (str::cat "*DIVIDE-" n-str "-MODULE*")
                   "ACL2"))

         (thm-name
          (intern$ (str::cat "DIVIDE-" n-str "-CORRECT")
                   "ACL2"))

         (module-name (str::cat "divide" n-str))

         (test-vector-name
          (intern$ (str::cat "DIVIDE-" n-str "-TEST-VECTOR")
                   "ACL2"))


         (test-vector-autohyps-name
          (intern$ (str::cat (symbol-name test-vector-name)
                             "-AUTOHYPS")
                   "ACL2"))

         (test-vector-autoins-name
          (intern$ (str::cat (symbol-name test-vector-name)
                             "-AUTOINS")
                   "ACL2"))

         (g-bindings
          `(gl::auto-bindings (:mix (:nat a ,n)
                                    (:nat b ,n)))))

    `(progn
       (defconst ,constant-name
         (vl::vl-module->esim
          (vl::vl-find-module ,module-name (vl::vl-translation->mods *divide-modules*))))



       (defstv ,test-vector-name
         :mod ,constant-name
         :inputs
         '(("abus"   a)
           ("bbus"   b))
         :outputs
         '(("out"    res)))

       (def-gl-thm ,thm-name
         :hyp (and (,test-vector-autohyps-name))
         :concl (equal (let* ((in-alist  (,test-vector-autoins-name))
                              (out-alist (stv-run (,test-vector-name) in-alist))
                              (res       (cdr (assoc 'res out-alist))))
                         res)
                       (if (equal b 0) 'X (floor a b)))
         :g-bindings ,g-bindings))))


(divide-thm 1)
(divide-thm 2)
(divide-thm 3)
(divide-thm 4)
(divide-thm 8)
(divide-thm 10) ; took 2.79 seconds with glucose 2.2 on modern, yet slow, laptop
; (divide-thm 12) ; ; took 14.59 seconds with glucose 2.2 on modern, yet slow, laptop

#|

; These are left as benchmarks for the future

(divide-thm 16)
(divide-thm 32)
(divide-thm 64)
(divide-thm 128)
(divide-thm 256)
(divide-thm 512)
|#
