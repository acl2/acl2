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
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc elimalways
  :parents (always-top)
  :short "Add fatal @(see warnings) to any modules with @('always') blocks, and
throw away all @('always') blocks."

  :long "<p>This is typically the very last thing we do to process @('always')
blocks.  It is meant as a catch-all for @('always') blocks that are too complex
to handle.</p>")

(local (xdoc::set-default-parents elimalways))

(define vl-warn-about-bad-always-blocks ((x        vl-alwayslist-p)
                                         (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (always1 (vl-always-fix (car x)))
       (warnings (fatal :type :vl-bad-always
                        :msg "~a0: always block is not supported."
                        :args (list always1))))
    (vl-warn-about-bad-always-blocks (cdr x) warnings)))

(define vl-module-elimalways ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        x)
       (warnings (vl-warn-about-bad-always-blocks x.alwayses x.warnings)))
    (change-vl-module x
                      :alwayses nil
                      :warnings warnings)))

(defprojection vl-modulelist-elimalways ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-elimalways x))

(define vl-design-elimalways
  :short "Top-level @(see elimalways) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-elimalways x.mods))))
