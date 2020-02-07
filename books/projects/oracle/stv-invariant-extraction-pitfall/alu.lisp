; ALU with a Doomsday Counter
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
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
; Original authors: Andrew Brock <andrew.brock@oracle.com>
;                   David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

(include-book "std/top" :dir :system)
(include-book "centaur/esim/defmodules" :dir :system)
(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

(def-gl-clause-processor my-glcp)

;; [Jared] Adding (comp t) after my-glcp to avoid stack overflow on GCL.
(comp t)

(value-triple (set-max-mem (expt 2 34)))

(defmodules *alu-translation*
  (vl2014::make-vl-loadconfig
   :start-files (list "alu.v")))

(defconst *doomsday-vl*
  (vl2014::vl-find-module "doomsday"
                          (vl2014::vl-design->mods
                           (vl2014::vl-translation->good *alu-translation*))))

(defconst *doomsday*
  (vl2014::vl-module->esim *doomsday-vl*))

; we only need a one-cycle stv
(defstv doomsday-run
  :short "runs the ALU"
  :long "<p>This STV runs the ALU for one cycle, allowing us to extract what
        looks a lot like a valid invariant</p>"
  :mod *doomsday*
  :inputs
  '(("clk" 0 ~)
    ("a" _ _ a _)
    ("b" _ _ b _)
    ("rst" 1 0 0 0))
  :outputs
  '(("ans" _ _ ans _))) ; [3:0]

(define doomsday-step ((a nibblep)
                       (b nibblep))
  :verify-guards nil
  (b* ((stout (stv-run (doomsday-run)
                       (LIST (cons 'a a)
                             (cons 'b b))))
       ((assocs ans) stout))
    ans))

(define doomsday-next ((a nibblep)
                       (b nibblep))
  :verify-guards nil
  (loghead 4 (+ a b)))

; Matt K. mod: Turn off warnings about "Fast alist discipline violated".  David
; Rager is aware of them but is not terribly concerned, and he has has approved
; this mod.
(local (set-slow-alist-action nil))

(def-gl-thm doomsday-adds
  :hyp (and (nibblep a)
            (nibblep b))
  :concl (equal (doomsday-step a b) (doomsday-next a b))
  :g-bindings (GL::AUTO-BINDINGS (:NAT a 4)
                                 (:NAT b 4)))
