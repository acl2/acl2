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
(include-book "../mlib/modnamespace")
(include-book "../mlib/expr-tools")
(local (include-book "../util/arithmetic"))

(defsection vl-module-portcheck

  (defund vl-module-portcheck (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (decl-names (mergesort (vl-portdecllist->names x.portdecls)))
         (port-names (mergesort (vl-exprlist-names (remove nil (vl-portlist->exprs x.ports)))))
         ((unless (subset decl-names port-names))
          (b* ((w (make-vl-warning
                   :type :vl-port-mismatch
                   :msg "Missing port declarations for ~&0."
                   :args (list (difference decl-names port-names))
                   :fatalp t
                   :fn 'vl-check-ports-agree-with-portdecls)))
            (change-vl-module x :warnings (cons w x.warnings))))
         ((unless (subset port-names decl-names))
          (b* ((w (make-vl-warning
                   :type :vl-port-mismatch
                   :msg "Port declarations for non-ports: ~&0."
                   :args (list (difference port-names decl-names))
                   :fatalp t
                   :fn 'vl-check-ports-agree-with-portdecls)))
            (change-vl-module x :warnings (cons w x.warnings)))))
      x))

  (local (in-theory (enable vl-module-portcheck)))

  (defthm vl-module-p-of-vl-module-portcheck
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-portcheck x))))

  (defthm vl-module->name-of-vl-module-portcheck
    (equal (vl-module->name (vl-module-portcheck x))
           (vl-module->name x))))


(defsection vl-modulelist-portcheck

  (defprojection vl-modulelist-portcheck (x)
    (vl-module-portcheck x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (defthm vl-modulelist->names-of-vl-modulelist-portcheck
    (equal (vl-modulelist->names (vl-modulelist-portcheck x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))
