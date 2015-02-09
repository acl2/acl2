; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
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

