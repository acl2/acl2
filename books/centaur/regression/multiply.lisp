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

; Modified by Jared Davis <jared@centtech.com> on 2013-12-17 after changes to
; improve compatibility between VL and GL multiplies, to verify the multipliers
; up through 64 bits.

(in-package "ACL2")

(include-book "common")

(defmodules *multiply-modules*
  (vl::make-vl-loadconfig
   :start-files (list "multiply.v")))

(defmacro multiply-thm (n)
  (let* ((n-str (str::natstr n))

         (constant-name ;;; defining a constant is a bit silly, but having this
                        ;;; intermediate artifact to view
          (intern$ (str::cat "*MULTIPLY-" n-str "-MODULE*")
                   "ACL2"))

         (thm-name
          (intern$ (str::cat "MULTIPLY-" n-str "-CORRECT")
                   "ACL2"))

         (module-name (str::cat "multiply" n-str))

         (test-vector-name
          (intern$ (str::cat "MULTIPLY-" n-str "-TEST-VECTOR")
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

; [Jared]: Previously the file stopped here with the following notes:
;
;   (multiply-thm 8) ; took 1.57 seconds with glucose 2.2 on modern, yet slow, laptop
;   (multiply-thm 10) ; took 86.11 seconds with glucose 2.2 on modern, yet slow, laptop
;
;   These are left as benchmarks for the future
;
;   (multiply-thm 12)
;   (multiply-thm 16)
;   (multiply-thm 32)
;   (multiply-thm 64)
;   (multiply-thm 128)
;   (multiply-thm 256)
;   (multiply-thm 512)

; But now VL generates multipliers that mimic GL's implementation of
; multiplication, so we can go much higher.  You may notice that the problems
; being given to the SAT solver are empty.  This is basically because the
; expressions for the spec and the expressions for the implementation end up
; being identical thanks to just the basic structural hashing and reductions in
; Hons AIGs and AIGNET.  In short, the AIG package basically solves the whole
; thing, and there's nothing for the SAT solver to do.

(multiply-thm 8)
(multiply-thm 10)
(multiply-thm 12)
(multiply-thm 16)
(multiply-thm 32)
(multiply-thm 64)

