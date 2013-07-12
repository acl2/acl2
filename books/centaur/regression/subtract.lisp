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

;; cert_param: (uses-glucose)

(in-package "ACL2")

(include-book "common")

(defmodules *subtract-modules*
  (vl::make-vl-loadconfig
   :start-files (list "subtract.v")))

(defmacro subtract-thm (n)
  (let* ((n-str (str::natstr n))

         (constant-name ;;; defining a constant is a bit silly, but having this
                        ;;; intermediate artifact to view
          (intern$ (str::cat "*SUBTRACT-" n-str "-MODULE*")

                   "ACL2"))

         (thm-name
          (intern$ (str::cat "SUBTRACT-" n-str "-CORRECT")

                   "ACL2"))

         (module-name (str::cat "subtract" n-str))

         (test-vector-name
          (intern$ (str::cat "SUBTRACT-" n-str "-TEST-VECTOR")
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
          (vl::vl-find-module ,module-name (vl::vl-translation->mods *subtract-modules*))))



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
                       (mod (- a b) (expt 2 ,n)))
         :g-bindings ,g-bindings))))


(subtract-thm 1)
(subtract-thm 2)
(subtract-thm 3)
(subtract-thm 4)
(subtract-thm 8)
(subtract-thm 16)
(subtract-thm 32)
(subtract-thm 64)
(subtract-thm 128)
(subtract-thm 256) ; took 7.82 seconds (with glucose 2.2)
; (subtract-thm 512) ; took 29.34 seconds (with glucose 2.2)
