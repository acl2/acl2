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
(include-book "../wf-reasonable-p")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc check-namespace
  :parents (lint)
  :short "A check for basic, incorrect constructs like name clashes."

  :long "<p>This is a like @(see vl-module-check-reasonable), but is more
appropriate for linting.  The main difference is that, here, we don't complain
about perfectly valid Verilog constructs merely because they aren't supported
by our transformation to @(see esim).  For instance, we don't support event
declarations in E, but that's no reason to complain about them when
linting.</p>")

(local (xdoc::set-default-parents check-namespace))

(define vl-module-check-namespace ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard "Perhaps extended with warnings.")
  (b* (((vl-module x) x)
       (warnings x.warnings)
       (pdnames     (vl-portdecllist->names x.portdecls))
       (pdnames-s   (mergesort pdnames))
       (namespace   (vl-module->modnamespace x))
       (namespace-s (mergesort namespace))
       (overlap     (intersect pdnames-s namespace-s))

       ((mv & warnings)
        (vl-portlist-reasonable-p-warn x.ports warnings))

       (warnings
        (if (mbe :logic (no-duplicatesp-equal namespace)
                 :exec (same-lengthp namespace namespace-s))
            warnings
          (cons (make-vl-warning :type :vl-namespace-error
                                 :msg "Illegal redefinition of ~&0."
                                 :args (list (duplicated-members namespace))
                                 :fatalp t
                                 :fn 'vl-module-check-namespace)
                warnings)))

       (palist (vl-portdecl-alist x.portdecls))
       (ialist (vl-moditem-alist x))
       ((mv & warnings)
        (vl-overlap-compatible-p-warn overlap x palist ialist warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-check-namespace (x)
  (vl-module-check-namespace x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-check-namespace ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x
                      :mods (vl-modulelist-check-namespace x.mods))))

