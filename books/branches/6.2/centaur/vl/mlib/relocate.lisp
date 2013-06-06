; VL Verilog Toolkit
; Copyright (C) 2008-2012 Centaur Technology
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

(defxdoc relocate
  :parents (mlib)
  :short "Functions to change the locations of various module elements."

  :long "<p>It is sometimes useful to move module elements to some new
location, e.g., when we are inlining elements from one module into another.
These are just some utilities to perform such relocations.</p>")

(defprojection vl-relocate-assigns (loc x)
  (change-vl-assign x :loc loc)
  :guard (and (vl-location-p loc)
              (vl-assignlist-p x))
  :result-type vl-assignlist-p
  :parents (relocate vl-assignlist-p))

(defprojection vl-relocate-modinsts (loc x)
  (change-vl-modinst x :loc loc)
  :guard (and (vl-location-p loc)
              (vl-modinstlist-p x))
  :result-type vl-modinstlist-p
  :parents (relocate vl-modinstlist-p))

(defprojection vl-relocate-gateinsts (loc x)
  (change-vl-gateinst x :loc loc)
  :guard (and (vl-location-p loc)
              (vl-gateinstlist-p x))
  :result-type vl-gateinstlist-p
  :parents (relocate vl-gateinstlist-p))

(defprojection vl-relocate-netdecls (loc x)
  (change-vl-netdecl x :loc loc)
  :guard (and (vl-location-p loc)
              (vl-netdecllist-p x))
  :result-type vl-netdecllist-p
  :parents (relocate vl-netdecllist-p))
