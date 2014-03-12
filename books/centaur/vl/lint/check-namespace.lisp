; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
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

       ((mv & warnings)
        (vl-overlap-compatible-p-warn overlap x warnings)))

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

