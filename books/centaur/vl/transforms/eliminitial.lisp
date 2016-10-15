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
(include-book "../parsetree")
(include-book "../mlib/blocks")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc eliminitial
  :parents (transforms)
  :short "Throw away any @('initial') statements and add non-fatal @(see
warnings) to the affected modules."

  :long "<p>Initial statements can be important for simulation, but are
meaningless if we want to consider the post synthesis/build behavior of the
actual part.  Throwing them away, then, is basically reasonable for any
back-end tool that wants to analyze the behavior of the synthesized
modules.</p>

<p>This transform can be run at any time.  Back in VL2014 it was important to
run it somewhere before the old @(see vl2014::always-top) transform, since some
always-block code was reluctant to process modules with @('initial')
statements.  That probably doesn't matter anymore.</p>")

(local (xdoc::set-default-parents eliminitial))

(def-genblob-transform vl-genblob-eliminitial ((modname stringp)
                                               (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  ;; :verify-guards nil
  (b* (((vl-genblob x) x)
       (warnings
        (if x.initials
            (warn
             :type :vl-warn-initial
             :msg  "Dropped ~x0 initial statement~s1 from module ~m2.  (This is ~
                generally fine: initial statements are just test bench code ~
                that can be ignored when analyzing the module's behavior.)"
             :args (list (len x.initials)
                         (if (vl-plural-p x.initials) "s" "")
                         (string-fix modname)))
          (ok)))
       ((mv warnings generates)  (vl-generates-eliminitial  x.generates modname warnings)))
      (mv warnings
          (change-vl-genblob
           x
           :initials nil
           :generates generates)))
  :apply-to-generates vl-generates-eliminitial)



(define vl-module-eliminitial ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       (genblob (vl-module->genblob x))
       ((mv warnings new-genblob) (vl-genblob-eliminitial genblob
                                                          (vl-module->name x)
                                                          (vl-module->warnings x)))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module new-genblob x-warn)))

(defprojection vl-modulelist-eliminitial ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-eliminitial x))

(define vl-design-eliminitial
  :short "Top-level @(see eliminitial) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-eliminitial x.mods))))
