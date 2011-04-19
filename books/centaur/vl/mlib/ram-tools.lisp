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
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))

(defsection vl-rammodule-p
  :parents (rams)
  :short "Recognizes RAM modules."

  :long "<p>@(call vl-rammodule-p) determines whether a module is a RAM.  This
is done by looking for the <tt>VL_RAM</tt> attribute, which is set by VL's
parser when it creates RAM modules.</p>"

  (defund vl-rammodule-p (x)
    (declare (xargs :guard (vl-module-p x)))
    (if (assoc-equal "VL_RAM" (vl-module->atts x))
        t
      nil)))



(defsection vl-rammodule->addr-width
  :parents (rams vl-rammodule-p)
  :short "Get the address width from a RAM module."

  :long "<p>@(call vl-rammodule->addr-width) returns the number of address bits
for a RAM module.  This information is saved in the <tt>VL_RAM_ADDR_WIDTH</tt>
attribute when VL's parser creates RAM modules.</p>"

  (defund vl-rammodule->addr-width (x)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-rammodule-p x))))
    (b* ((expr (cdr (assoc-equal "VL_RAM_ADDR_WIDTH" (vl-module->atts x))))
         ((unless (and expr
                       (vl-expr-resolved-p expr)
                       (< 0 (vl-resolved->val expr))))
          (er hard? 'vl-rammodule->addr-width
              "Expected valid VL_RAM_ADDR_WIDTH attribute for RAM module ~s0."
              (vl-module->name x))
          1))
        (vl-resolved->val expr)))

  (local (in-theory (enable vl-rammodule->addr-width)))

  (defthm posp-of-vl-rammodule->addr-width
    (posp (vl-rammodule->addr-width x))
    :rule-classes :type-prescription))



(defsection vl-rammodule->data-width
  :parents (rams vl-rammodule-p)
  :short "Get the data width from a RAM module."

  :long "<p>@(call vl-rammodule->data-width) returns the width of each entry in
a RAM module.  This information is saved in the <tt>VL_RAM_DATA_WIDTH</tt>
attribute when VL's parser creates RAM modules.</p>"

  (defund vl-rammodule->data-width (x)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-rammodule-p x))))
    (b* ((expr (cdr (assoc-equal "VL_RAM_DATA_WIDTH" (vl-module->atts x))))
         ((unless (and expr
                       (vl-expr-resolved-p expr)
                       (< 0 (vl-resolved->val expr))))
          (er hard? 'vl-rammodule->data-width
              "Expected valid VL_RAM_DATA_WIDTH attribute for RAM module ~s0."
              (vl-module->name x))
          1))
        (vl-resolved->val expr)))

  (local (in-theory (enable vl-rammodule->data-width)))

  (defthm posp-of-vl-rammodule->data-width
    (posp (vl-rammodule->data-width x))
    :rule-classes :type-prescription))

