; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.


; steps.lisp -- functions for stepping esim
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")


(include-book "esim-sexpr")


(defdoc esim-steps
  ":doc-section esim

Various stepping functions for esim.~/

Usage:
~bv[]
 (<step-fn> mod ins st)
~ev[]

where ~c[<step-fn>] is one of:
~bv[]
 esim-sexpr-steps
 esim-sexpr-probe-steps
 esim-sexpr-top-steps

 esim-faig-steps
 esim-faig-probe-steps
 esim-faig-top-steps
~ev[]

In each case, ~c[mod] is an esim module, ~c[ins] is a list of alists, and
~c[st] is a single alist.  These functions all simulate the module for ~c[n]
steps, where ~c[n] is the length of ~c[ins], beginning with initial state
~c[st], where the inputs for the ~c[k+1]st step are given by ~c[(nth k ins)].

The -probe- variants produce three outputs, each a list of alists: ~c[nsts],
~c[outs], and ~c[internals].  The non-probe variants only produce ~c[nsts] and
~c[outs].  Here ~c[nsts] is a list where ~c[(nth k nsts)] is an alist givng the
module state after ~c[k+1] steps, and similarly ~c[(nth k outs)] gives the
outputs, and in only the -top- variants additionally the top-level module's
internal signals, from the ~c[k+1]st step and ~c[(nth k internals)] gives the
internal signal settings after the ~c[k+1]st step.

The -sexpr- variants take and produce alists mapping signals to 4v-sexprs,
whereas the -faig- variants take and produce alists mapping signals to FAIGs.
~/~/")

(defmacro def-esim-step (name vals step)
  (b* ((step-vals (if (eql vals 3)
                      '(nst out internal)
                    '(nst out)))
       (rest-vals (if (eql vals 3)
                      '(nsts outs internals)
                    '(nsts outs)))
       (nil-vals (make-list vals))
       (ret-vals (pairlis$ (make-list vals :initial-element 'cons)
                           (pairlis$ step-vals
                                     (pairlis$ rest-vals
                                               nil-vals)))))
    `(defun ,name (mod ins st)
       ":doc-section esim-steps
       ESIM stepping function.~/
       See ~il[esim-steps].~/~/"
       (b* (((when (atom ins))
             (mv . ,nil-vals))
            ((mv . ,step-vals)
             (b* ((in (car ins))
                  ((with-fast in st)))
               (,step mod in st)))
            ((mv . ,rest-vals)
             (,name mod (cdr ins) nst)))
         (mv . ,ret-vals)))))

(def-esim-step esim-faig-probe-steps 3 esim-faig-probe-3v)
(def-esim-step esim-faig-new-probe-steps 3 esim-faig-new-probe-3v)
(def-esim-step esim-faig-top-steps 2 esim-faig-probe-top-3v)
(def-esim-step esim-faig-steps 2 esim-faig-3v)
(def-esim-step esim-sexpr-probe-steps 3 esim-sexpr-probe)
(def-esim-step esim-sexpr-new-probe-steps 3 esim-sexpr-new-probe)
(def-esim-step esim-sexpr-top-steps 2 esim-sexpr-probe-top)
(def-esim-step esim-sexpr-steps 2 esim-sexpr)
(def-esim-step esim-sexpr-simp-steps 2 esim-sexpr-simp)
(def-esim-step esim-sexpr-simp-new-probe-steps 3 esim-sexpr-simp-new-probe)

