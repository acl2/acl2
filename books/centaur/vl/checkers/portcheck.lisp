; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(defsection portcheck
  :parents (checkers)
  :short "Trivial check to make sure that each module's ports agree with its
  port declarations.")

(local (xdoc::set-default-parents portcheck))

(define vl-module-portcheck ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard
                  "New version of @('x'), with at most some added warnings.")
  (b* (((vl-module x) x)
       (decl-names (mergesort (vl-portdecllist->names x.portdecls)))
       (port-names (mergesort (vl-exprlist-names (remove nil (vl-portlist->exprs x.ports)))))
       ((unless (subset decl-names port-names))
        (b* ((w (make-vl-warning
                 :type :vl-port-mismatch
                 :msg "Port declarations for non-ports: ~&0."
                 :args (list (difference decl-names port-names))
                 :fatalp t
                 :fn 'vl-check-ports-agree-with-portdecls)))
          (change-vl-module x :warnings (cons w x.warnings))))

       ((unless (subset port-names decl-names))
        (b* ((w (make-vl-warning
                 :type :vl-port-mismatch
                 :msg "Missing port declarations for ~&0."
                 :args (list (difference port-names decl-names))
                 :fatalp t
                 :fn 'vl-check-ports-agree-with-portdecls)))
          (change-vl-module x :warnings (cons w x.warnings)))))
    x))

(defprojection vl-modulelist-portcheck (x)
  (vl-module-portcheck x)
  :parents (portcheck)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-portcheck
  :short "Top-level @(see portcheck) check."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-portcheck x.mods))))

