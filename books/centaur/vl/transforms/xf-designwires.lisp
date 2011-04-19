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
  :short "Introduce <tt>VL_DESIGN_WIRE</tt> annotations."

  :long "<p>In this transformation, we annotate every net and reg declaration
with a <tt>VL_DESIGN_WIRE</tt> attribute (see @(see attributes)).  Later, when
\"temporary\" wires are added to the module, they will not have this attribute.
The idea is to allow us to distinguish between (1) the wires that are really
present and visible in the design, and (2) the wires that VL has added during
transformations like @(see split) and @(see occform).</p>

<p>This transformation really should be run shortly <b>after</b> @(see
make-implicit-wires), since even implicit wires are visible in the
design.</p>")


(defsection vl-netdecl-designwires

  (defund vl-netdecl-designwires (x)
    (declare (xargs :guard (vl-netdecl-p x)))
    (let* ((old-atts (vl-netdecl->atts x))
           (new-atts (acons "VL_DESIGN_WIRE" nil old-atts)))
      (change-vl-netdecl x :atts new-atts)))

  (local (in-theory (enable vl-netdecl-designwires)))

  (defthm vl-netdecl-p-of-vl-netdecl-designwires
    (implies (force (vl-netdecl-p x))
             (vl-netdecl-p (vl-netdecl-designwires x)))))


(defprojection vl-netdecllist-designwires (x)
  (vl-netdecl-designwires x)
  :guard (vl-netdecllist-p x)
  :result-type vl-netdecllist-p
  :nil-preservingp nil)

(defsection vl-regdecl-designwires

  (defund vl-regdecl-designwires (x)
    (declare (xargs :guard (vl-regdecl-p x)))
    (let* ((old-atts (vl-regdecl->atts x))
           (new-atts (acons "VL_DESIGN_WIRE" nil old-atts)))
      (change-vl-regdecl x :atts new-atts)))

  (local (in-theory (enable vl-regdecl-designwires)))

  (defthm vl-regdecl-p-of-vl-regdecl-designwires
    (implies (force (vl-regdecl-p x))
             (vl-regdecl-p (vl-regdecl-designwires x)))))


(defprojection vl-regdecllist-designwires (x)
  (vl-regdecl-designwires x)
  :guard (vl-regdecllist-p x)
  :result-type vl-regdecllist-p
  :nil-preservingp nil)


(defsection vl-module-designwires

  (defund vl-module-designwires (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (old-netdecls (vl-module->netdecls x))
         (old-regdecls (vl-module->regdecls x))
         (new-netdecls (vl-netdecllist-designwires old-netdecls))
         (new-regdecls (vl-regdecllist-designwires old-regdecls)))
        (change-vl-module x
                          :netdecls new-netdecls
                          :regdecls new-regdecls)))

  (local (in-theory (enable vl-module-designwires)))

  (defthm vl-module-p-of-vl-module-designwires
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-designwires x))))

  (defthm vl-module->name-of-vl-module-designwires
    (equal (vl-module->name (vl-module-designwires x))
           (vl-module->name x))))


(defsection vl-modulelist-designwires
  :parents (designwires)
  :short "Add <tt>VL_DESIGN_WIRE</tt> annotations throughout a module list."
  :long "<p>This transformation is so simple that we just present its source
code below, in a top-down style.</p>"

  (defprojection vl-modulelist-designwires (x)
    (vl-module-designwires x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p
    :nil-preservingp nil)

  (local (in-theory (enable vl-modulelist-designwires)))

  (defthm vl-modulelist->names-of-vl-modulelist-designwires
    (equal (vl-modulelist->names (vl-modulelist-designwires x))
           (vl-modulelist->names x))))



