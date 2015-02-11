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


