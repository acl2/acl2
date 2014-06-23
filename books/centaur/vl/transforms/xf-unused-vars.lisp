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
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(include-book "../mlib/filter")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection elim-unused-vars
  :parents (transforms)
  :short "Remove any variable declarations that are never used.")

(local (xdoc::set-default-parents elim-unused-vars))

(define vl-module-elim-unused-vars ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)

       ((unless (consp x.vardecls))
        ;; Optimization.  Don't need to do anything if there aren't any
        ;; variables anyway.
        x)

       (used       (vl-exprlist-names (vl-module-allexprs x)))
       (new-vars   (vl-keep-vardecls used x.vardecls))

       ((when (same-lengthp new-vars x.vardecls))
        ;; Optimization.  Don't need to do anything more unless we threw out
        ;; some registers.
        x)

       (warnings        x.warnings)
       (old-varnames    (mergesort (vl-vardecllist->names x.vardecls)))
       (new-varnames    (mergesort (vl-vardecllist->names new-vars)))
       (unused-varnames (difference old-varnames new-varnames))
       (warnings        (if unused-varnames
                            (warn :type :vl-warn-unused-var
                                  :msg "In ~m0, eliminating spurious variables ~&1."
                                  :args (list (vl-module->name x) unused-varnames))
                          warnings))

       (new-x (change-vl-module x
                                :vardecls new-vars
                                :warnings warnings)))
    new-x))

(defprojection vl-modulelist-elim-unused-vars ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-elim-unused-vars x))

(define vl-design-elim-unused-vars
  :short "Top-level @(see elim-unused-vars) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x
                      :mods (vl-modulelist-elim-unused-vars x.mods))))


