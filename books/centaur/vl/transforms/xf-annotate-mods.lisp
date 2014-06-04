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
(include-book "xf-portdecl-sign")
(include-book "xf-argresolve")
(include-book "xf-orig")
(include-book "xf-designwires")
(include-book "xf-follow-hids")
(include-book "xf-resolve-indexing")
(include-book "xf-clean-warnings")
(include-book "cn-hooks")
(include-book "../checkers/duplicate-detect")
(include-book "../checkers/portcheck")
(include-book "../util/cwtime")

(define vl-annotate-design
  :parents (transforms)
  :short "Meta-transform.  Applies several basic, preliminary transforms to
          annotate the original modules in various ways."
  ((design vl-design-p))
  :returns (new-design vl-design-p)

  (b* ((design (xf-cwtime (vl-design-duplicate-detect design)
                          :name xf-duplicate-detect))
       (design (xf-cwtime (vl-design-portcheck design)
                          :name xf-portcheck))
       (design (xf-cwtime (vl-design-designwires design)
                          :name xf-mark-design-wires))
       (design (xf-cwtime (vl-design-portdecl-sign design)
                          :name xf-crosscheck-port-signedness))
       (design (xf-cwtime (vl-design-resolve-indexing design)
                          :name xf-resolve-indexing))
       (design (xf-cwtime (vl-design-argresolve design)
                          :name xf-argresolve))
       (design (xf-cwtime (vl-design-origexprs design)
                          :name xf-origexprs))
       (design (xf-cwtime (mp-verror-transform-hook design)
                          :name xf-mp-verror))
       (design (xf-cwtime (vl-design-clean-warnings design)
                          :name xf-clean-warnings)))

    design))

