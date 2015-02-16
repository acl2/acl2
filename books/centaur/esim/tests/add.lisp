; Copyright David Rager, 2013

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

(in-package "ACL2")

(include-book "common" :ttags :all)

(defmodules *add-modules*
  (vl2014::make-vl-loadconfig
   :start-files (list "add.v")))

(defmacro add-thm (n)
  (let* ((n-str (str::natstr n))

         (constant-name ;;; defining a constant is a bit silly, but having this
                        ;;; intermediate artifact to view
          (intern$ (str::cat "*ADD-" n-str "-MODULE*")
                   "ACL2"))

         (thm-name
          (intern$ (str::cat "ADD-" n-str "-CORRECT")
                   "ACL2"))

        (module-name (str::cat "add" n-str))

        (test-vector-name
         (intern$ (str::cat "ADD-" n-str "-TEST-VECTOR")
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
         (vl2014::vl-module->esim
          (vl2014::vl-find-module ,module-name
                              (vl2014::vl-design->mods
                               (vl2014::vl-translation->good *add-modules*)))))



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
                       (mod (+ a b) (expt 2 ,n)))
         :g-bindings ,g-bindings))))


(add-thm 1)
(add-thm 2)
(add-thm 3)
(add-thm 4)
(add-thm 8)
(add-thm 16)
(add-thm 32)
(add-thm 64)
(add-thm 128)
(add-thm 256) ; took 6.98 seconds (with glucose 2.2)
; (add-thm 512) ; took 26.33 seconds (with glucose 2.2)
