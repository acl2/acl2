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

(defxdoc esim-steps
  :parents (esim)
  :short "Various stepping functions for esim."

  :long "<p>Usage</p>

@({
 (<step-fn> mod ins st)
})

<p>where @('<step-fn>') is one of:</p>

<ul>
<li>esim-sexpr-steps</li>
<li>esim-sexpr-probe-steps</li>
<li>esim-sexpr-top-steps</li>
<li>esim-faig-steps</li>
<li>esim-faig-probe-steps</li>
<li>esim-faig-top-steps</li>
</ul>

<p>In each case:</p>

<ul>
<li>@('mod') is an esim module</li>
<li>@('ins') is a list of alists</li>
<li>@('st') is a single alist</li>
</ul>

<p>These functions all simulate the module for @('n') steps, where @('n') is
the length of @('ins'), beginning with initial state @('st'), where the inputs
for the @('k+1')st step are given by @('(nth k ins)').</p>

<p>The @('-sexpr-') variants take and produce alists mapping signals to @(see
4v-sexprs).</p>

<p>The @('-faig-') variants take and produce alists mapping signals to @(see
faig)s.</li>

<p>The @('-probe-') variants produce three outputs, each a list of alists:
@('nsts'), @('outs'), and @('internals').  The non-probe variants only produce
@('nsts') and @('outs').</p>

<ul>

<li>@('nsts') is the list of next states, i.e., @('(nth k nsts)') is an
alist giving the module state after @('k+1') steps,</li>

<li>@('outs') is the list of outputs, i.e., @('(nth k outs)') gives the
outputs from the @('k+1')th step.  In the @('-top-') variants only, this
will also include the top-level module's internal signals.</li>

<li>@('internals') is the list of internal signals, i.e., @('(nth k
internals)') gives the internal signal settings after the @('k+1')st step.</li>

</ul>")

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
    `(define ,name (mod ins st)
       :parents (esim-steps)
       :short "ESIM stepping function."
       :long "<p>See @(see esim-steps).</p>"
       :enabled t ;; for backwards compatibility
       :verify-guards nil
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

