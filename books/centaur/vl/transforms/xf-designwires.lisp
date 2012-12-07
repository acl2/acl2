; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

(defxdoc designwires
  :parents (transforms)
  :short "Introduce @('VL_DESIGN_WIRE') annotations that say which wires/regs
were in the original Verilog modules."

  :long "<p>This transform lets you distinguish between:</p>

<ul>
<li>wires that are really present and visible in the design, and</li>
<li>wires that VL added in transforms like @(see split) and @(see occform).</li>
</ul>

<p>This transform should typically be run very early.  It just annotates every
net and reg declaration with a @('VL_DESIGN_WIRE') <see topic='@(url
vl-atts-p)'>attribute</see>.</p>

<p>When temporary wires are added to the module by subsequent VL transforms,
they will not have this attribute.  Hence, you can check for this attribute to
tell whether a wire was in the original design.</p>")

(define vl-netdecl-designwires ((x vl-netdecl-p))
  :returns (new-x vl-netdecl-p :hyp :fguard)
  :parents (designwires)
  :short "Add a @('VL_DESIGN_WIRE') attribute to a @(see vl-netdecl-p)."
  (b* (((vl-netdecl x) x)
       ((when (assoc-equal "VL_DESIGN_WIRE" x.atts))
        ;; For idempotency, don't add it again.
        x)
       (atts (acons "VL_DESIGN_WIRE" nil x.atts)))
    (change-vl-netdecl x :atts atts)))

(defprojection vl-netdecllist-designwires (x)
  (vl-netdecl-designwires x)
  :guard (vl-netdecllist-p x)
  :result-type vl-netdecllist-p
  :nil-preservingp nil
  :parents (designwires))

(define vl-regdecl-designwires ((x vl-regdecl-p))
  :returns (new-x vl-regdecl-p :hyp :fguard)
  :parents (designwires)
  :short "Add a @('VL_DESIGN_WIRE') attribute to a @(see vl-regdecl-p)."
  (b* (((vl-regdecl x) x)
       ((when (assoc-equal "VL_DESIGN_WIRE" x.atts))
        ;; For idempotency, don't add it again.
        x)
       (atts (acons "VL_DESIGN_WIRE" nil x.atts)))
    (change-vl-regdecl x :atts atts)))

(defprojection vl-regdecllist-designwires (x)
  (vl-regdecl-designwires x)
  :guard (vl-regdecllist-p x)
  :result-type vl-regdecllist-p
  :nil-preservingp nil
  :parents (designwires))

(define vl-module-designwires ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (designwires)
  :short "Add a @('VL_DESIGN_WIRE') attribute to every net and reg declaration
in a module."
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x))
    (change-vl-module x
                      :netdecls (vl-netdecllist-designwires x.netdecls)
                      :regdecls (vl-regdecllist-designwires x.regdecls)))
  ///
  (defthm vl-module->name-of-vl-module-designwires
    (equal (vl-module->name (vl-module-designwires x))
           (vl-module->name x))))

(defprojection vl-modulelist-designwires (x)
  (vl-module-designwires x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :nil-preservingp nil
  :parents (designwires)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-designwires
     (equal (vl-modulelist->names (vl-modulelist-designwires x))
            (vl-modulelist->names x)))))

