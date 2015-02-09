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
(include-book "argresolve")
;; not ready yet (include-book "increment-elim")
(include-book "designwires")
(include-book "make-implicit-wires")
(include-book "origexprs")
(include-book "portdecl-sign")
(include-book "resolve-indexing")
(include-book "udp-elim")
(include-book "../clean-warnings")
(include-book "../cn-hooks")
(include-book "../../lint/duplicate-detect")
(include-book "../../lint/portcheck")
(include-book "../../util/cwtime")

(defsection annotate
  :parents (transforms)
  :short "A first step in most transformation sequences.  Applies several
basic, preliminary transforms to normalize the original design.")

(local (xdoc::set-default-parents annotate))

(define vl-annotate-design
  :short "Top level @(see annotate) transform."
  ((design vl-design-p))
  :returns (new-design vl-design-p)

  (b* ((design (xf-cwtime (vl-design-make-implicit-wires design)
                          :name xf-make-implicit-wires))
       (design (xf-cwtime (vl-design-portdecl-sign design)
                          :name xf-portdecl-sign))
       (design (xf-cwtime (vl-design-udp-elim design)
                          :name xf-udp-elim))
       ;;(design (xf-cwtime (vl-design-increment-elim design)
       ;;                   :name xf-increment-elim))
       (design (xf-cwtime (vl-design-duplicate-detect design)
                          :name xf-duplicate-detect))
       (design (xf-cwtime (vl-design-portcheck design)
                          :name xf-portcheck))
       (design (xf-cwtime (vl-design-designwires design)
                          :name xf-mark-design-wires))
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

