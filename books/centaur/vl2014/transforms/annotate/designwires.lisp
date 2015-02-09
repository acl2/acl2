; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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

(in-package "VL2014")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc designwires
  :parents (annotate)
  :short "Introduce @('VL_DESIGN_WIRE') annotations that say which wires/regs
were in the original Verilog modules."

  :long "<p>This transform is ordinarily run very early in the transformation
sequence by @(see annotate).  We simply extend every variable declaration with
a @('VL_DESIGN_WIRE') <see topic='@(url vl-atts-p)'>attribute</see>.  This
attribute can later be used to distinguish between:</p>

<ul>
<li>wires that are really present and visible in the design, and</li>
<li>wires that VL added in @(see transforms) like @(see split) and @(see
occform).</li>
</ul>

<p>That is, when temporary wires are added to the module by subsequent VL
transforms, they will not have this attribute.  Hence, you can check for this
attribute to tell whether a variable was in the original design.</p>")

(local (xdoc::set-default-parents designwires))

(define vl-vardecl-designwires ((x vl-vardecl-p))
  :returns (new-x vl-vardecl-p)
  :short "Add a @('VL_DESIGN_WIRE') attribute to a @(see vl-vardecl-p)."
  (b* (((vl-vardecl x) (vl-vardecl-fix x))
       ((when (assoc-equal "VL_DESIGN_WIRE" x.atts))
        ;; For idempotency, don't add it again.
        x)
       (atts (acons "VL_DESIGN_WIRE" nil x.atts)))
    (change-vl-vardecl x :atts atts)))

(defprojection vl-vardecllist-designwires ((x vl-vardecllist-p))
  :returns (new-x vl-vardecllist-p)
  (vl-vardecl-designwires x))

(define vl-module-designwires ((x vl-module-p))
  :returns (new-x vl-module-p)
  :short "Add a @('VL_DESIGN_WIRE') attribute to every net and reg declaration
in a module."
  (b* (((vl-module x) (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       (new-vardecls (vl-vardecllist-designwires x.vardecls)))
    (change-vl-module x :vardecls new-vardecls)))

(defprojection vl-modulelist-designwires ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-designwires x))

(define vl-design-designwires ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-designwires x.mods))))
