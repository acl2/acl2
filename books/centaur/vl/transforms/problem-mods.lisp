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
(local (include-book "../util/arithmetic"))

(defsection problem-modules
  :parents (transforms)
  :short "Eliminate modules that (the user says) cause problems."

  :long "<p>This is a trivial transform that simply adds fatal @(see warnings)
to any modules we are told are \"problem modules.\"</p>

<p>This is a barbaric but effective way to work around any modules that, e.g.,
expose some kind of programming problem with VL.</p>")

(local (xdoc::set-default-parents problem-modules))

(define vl-warn-problem-module
  :short "Add a fatal warning if this is a problem module."
  ((x        vl-module-p  "A module, perhaps a problem module.")
   (problems string-listp "A list of problem module names, supplied by the user."))
  :returns (new-x vl-module-p :hyp (force (vl-module-p x)))
  (b* (((unless (member-equal (vl-module->name x) problems))
        ;; Not a problem, nothing to do
        x)
       (warnings (vl-module->warnings x))
       (warnings
        (fatal :type :vl-problem-module
               :msg "~m0 was listed as a \"problem module\" by the VL user."
               :args (list (vl-module->name x)))))
    (change-vl-module x :warnings warnings)))

(defprojection vl-warn-problem-modulelist (x problems)
  (vl-warn-problem-module x problems)
  :guard (and (vl-modulelist-p x)
              (string-listp problems))
  :short "Extend @(see vl-warn-problem-modulelist) to a list of modules.")

(defthm vl-modulelist-p-of-vl-warn-problem-modulelist
  (implies (force (vl-modulelist-p x))
           (vl-modulelist-p (vl-warn-problem-modulelist x problems)))
  :hints(("Goal" :induct (len x))))

(define vl-design-problem-mods
  :short "Remove user-specified problem modules from the design."
  ((design   vl-design-p)
   (problems string-listp))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       ((vl-design design) design)
       (new-mods (vl-warn-problem-modulelist design.mods problems)))
    (change-vl-design design :mods new-mods)))

