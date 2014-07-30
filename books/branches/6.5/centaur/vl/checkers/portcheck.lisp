; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

