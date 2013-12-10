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
(include-book "../checkers/duplicate-detect" )
(include-book "../checkers/portcheck" )
(include-book "../mlib/warnings" )
(include-book "../util/cwtime" )
(include-book "xf-designwires" )
(include-book "xf-portdecl-sign" )
(include-book "xf-argresolve" )
(include-book "xf-orig" )
(include-book "cn-hooks" )
(include-book "xf-follow-hids" )


(define vl-annotate-mods ((mods vl-modulelist-p))
  :returns (new-mods vl-modulelist-p :hyp :fguard)

; Annotations that will be done to form the "origmods" in the server

  (b* ((mods (xf-cwtime (vl-modulelist-duplicate-detect mods)
                        :name xf-duplicate-detect))

       (mods (xf-cwtime (vl-modulelist-portcheck mods)
                        :name xf-portcheck))

       (mods (xf-cwtime (vl-modulelist-designwires mods)
                        :name xf-mark-design-wires))

       (mods (xf-cwtime (vl-modulelist-portdecl-sign mods)
                        :name xf-crosscheck-port-signedness))

       (mods (xf-cwtime (vl-modulelist-argresolve mods)
                        :name xf-argresolve))

       (mods (xf-cwtime (vl-modulelist-origexprs mods)
                        :name xf-origexprs))

       (mods (xf-cwtime (mp-verror-transform-hook mods)
                        :name xf-mp-verror))

       (mods (xf-cwtime (vl-modulelist-clean-warnings mods)
                        :name xf-clean-warnings)))

    mods)

  ///

  (defthm vl-modulelist->names-of-vl-annotate-mods
    (equal (vl-modulelist->names (vl-annotate-mods mods))
           (vl-modulelist->names mods))))

