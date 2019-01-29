; VL Verilog Toolkit - Timeunits Parsing
; Copyright (C) 2017 Apple, Inc.
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

(in-package "VL")
(include-book "../mlib/blocks")
(local (include-book "../util/arithmetic"))

(xdoc::set-default-parents vl-lint)

(defxdoc vl-alwaysstyle
  :short "Simple lint check for any uses of legacy style @('always')
statements, as opposed to the newer @('always_comb'), @('always_ff'), or
@('always_latch') versions.")

(define vl-always-check-style ((x        vl-always-p)
                               (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-always x))
       (warnings
        (if (vl-alwaystype-equiv x.type :vl-always)
            (warn :type :vl-warn-plain-always
                  :msg  "~a0: legacy style always block in use, instead of ~
                         always_comb, always_ff, or always_latch."
                  :args (list x))
          (ok)))
       (warnings
        (if (vl-alwaystype-equiv x.type :vl-always-latch)
            (warn :type :vl-warn-always-latch
                  :msg "~a0: always_latch block found."
                  :args (list x))
          (ok))))
    warnings))

(define vl-alwayslist-check-style ((x vl-alwayslist-p)
                                   (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-always-check-style (first x) warnings)))
    (vl-alwayslist-check-style (rest x) warnings)))

;; Need to properly iterate through generates,etc.

(def-genblob-transform vl-genblob-alwaysstyle ((warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  :no-new-x t
  :apply-to-generates vl-generates-alwaysstyle
  (b* (((vl-genblob x))
       (warnings (vl-warninglist-fix warnings))
       (warnings (vl-alwayslist-check-style x.alwayses warnings))
       (warnings (vl-generates-alwaysstyle x.generates warnings)))
    warnings))

(define vl-module-alwaysstyle ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((genblob (vl-module->genblob x))
       (warnings (vl-genblob-alwaysstyle genblob (vl-module->warnings x))))
    (change-vl-module x :warnings warnings)))

(define vl-interface-alwaysstyle ((x vl-interface-p))
  :returns (new-x vl-interface-p)
  (b* ((genblob (vl-interface->genblob x))
       (warnings (vl-genblob-alwaysstyle genblob (vl-interface->warnings x))))
    (change-vl-interface x :warnings warnings)))

(defprojection vl-modulelist-alwaysstyle ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-alwaysstyle x))

(defprojection vl-interfacelist-alwaysstyle ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-alwaysstyle x))

(define vl-design-alwaysstyle ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x)))
    (change-vl-design x
                      :mods (vl-modulelist-alwaysstyle x.mods)
                      :interfaces (vl-interfacelist-alwaysstyle x.interfaces))))
