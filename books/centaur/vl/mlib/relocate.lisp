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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc relocate
  :parents (mlib)
  :short "Functions to change the locations of various module elements."

  :long "<p>It is sometimes useful to move module elements to some new
location, e.g., when we are inlining elements from one module into another.
These are just some utilities to perform such relocations.</p>")

(defprojection vl-relocate-assigns ((loc vl-location-p)
                                    (x   vl-assignlist-p))
  :parents (relocate vl-assignlist-p)
  :returns (new-x vl-assignlist-p)
  (change-vl-assign x :loc loc))

(defprojection vl-relocate-modinsts ((loc vl-location-p)
                                     (x   vl-modinstlist-p))
  :parents (relocate vl-modinstlist-p)
  :returns (new-x vl-modinstlist-p)
  (change-vl-modinst x :loc loc))

(defprojection vl-relocate-gateinsts ((loc vl-location-p)
                                      (x   vl-gateinstlist-p))
  :parents (relocate vl-gateinstlist-p)
  :returns (new-x vl-gateinstlist-p)
  (change-vl-gateinst x :loc loc))

(defprojection vl-relocate-netdecls ((loc vl-location-p)
                                     (x   vl-netdecllist-p))
  :parents (relocate vl-netdecllist-p)
  :returns (new-x vl-netdecllist-p)
  (change-vl-netdecl x :loc loc))

(defprojection vl-relocate-vardecls ((loc vl-location-p)
                                     (x   vl-vardecllist-p))
  :parents (relocate vl-vardecllist-p)
  :returns (new-x vl-vardecllist-p)
  (change-vl-vardecl x :loc loc))

(defprojection vl-relocate-portdecls ((loc vl-location-p)
                                      (x   vl-portdecllist-p))
  :parents (relocate vl-portdecllist-p)
  :returns (new-x vl-portdecllist-p)
  (change-vl-portdecl x :loc loc))

(defprojection vl-relocate-paramdecls ((loc vl-location-p)
                                       (x   vl-paramdecllist-p))
  :parents (relocate vl-paramdecllist-p)
  :returns (new-x vl-paramdecllist-p)
  (change-vl-paramdecl x :loc loc))

