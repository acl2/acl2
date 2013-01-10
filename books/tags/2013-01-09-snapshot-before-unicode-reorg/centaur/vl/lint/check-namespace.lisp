; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

; This is a like vl-module-check-reasonable but is more appropriate for linting
; since it doesn't complain about perfectly valid things like signed regs and
; initial statements.

(defsection vl-module-check-namespace

  (defund vl-module-check-namespace (x)
    (declare (xargs :guard (vl-module-p x)))
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

  (local (in-theory (enable vl-module-check-namespace)))

  (defthm vl-module-p-of-vl-module-check-namespace
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-check-namespace x))))

  (defthm vl-module->name-of-vl-module-check-namespace
    (equal (vl-module->name (vl-module-check-namespace x))
           (vl-module->name x))))


(defsection vl-modulelist-check-namespace

  (defprojection vl-modulelist-check-namespace (x)
    (vl-module-check-namespace x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-check-namespace)))

  (defthm vl-modulelist->names-of-vl-modulelist-check-namespace
    (equal (vl-modulelist->names (vl-modulelist-check-namespace x))
           (vl-modulelist->names x))))


