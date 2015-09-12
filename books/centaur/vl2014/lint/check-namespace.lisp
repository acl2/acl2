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
  :returns (new-x vl-module-p "Perhaps extended with warnings.")
  (b* (((vl-module x) x)
       (warnings x.warnings)

       ;; Clashing external port names?
       (portdupes (duplicated-members (remove nil (vl-portlist->names x.ports))))
       (warnings
        (if portdupes
            (fatal :type :vl-bad-ports
                   :msg "Duplicate port names: ~&0."
                   :args (list portdupes))
          warnings))

       ;; Clashing port decls?
       (pdnames     (vl-portdecllist->names x.portdecls))
       (pdnames-s   (mergesort pdnames))
       (warnings
        (if (mbe :logic (no-duplicatesp-equal pdnames)
                 :exec (same-lengthp pdnames pdnames-s))
            warnings
          (fatal :type :vl-bad-portdecls
                 :msg "Duplicate port declaration names: ~&0."
                 :args (list (duplicated-members pdnames)))))

       ;; Clashing internal names?
       (namespace   (vl-module->modnamespace x))
       (namespace-s (mergesort namespace))
       (warnings
        (if (mbe :logic (no-duplicatesp-equal namespace)
                 :exec (same-lengthp namespace namespace-s))
            warnings
          (fatal :type :vl-namespace-error
                 :msg "Illegal redefinition of ~&0."
                 :args (list (duplicated-members namespace)))))

       (overlap (intersect pdnames-s namespace-s))
       (palist  (vl-make-portdecl-alist x.portdecls))
       (ialist  (vl-make-moditem-alist x))
       ((mv & warnings)
        (vl-overlap-compatible-p-warn overlap x palist ialist warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-check-namespace ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-check-namespace x))

(define vl-design-check-namespace ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-check-namespace x.mods))))

