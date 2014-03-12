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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

(defsection problem-modules
  :parents (transforms)
  :short "Eliminate modules (that the user) says cause problems."

  :long "<p>This is a trivial transform that simply adds a fatal @(see warning)
to any modules we are told are \"problem modules.\"</p>

<p>This is a barbaric but effective way to work around any modules that, e.g.,
expose some kind of programming problem with VL.</p>")

(local (xdoc::set-default-parents problem-modules))

(define vl-warn-problem-module
  :parents (vl-simplify)
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
  :parents (vl-simplify)
  :short "Extend @(see vl-warn-problem-modulelist) to a list of modules.")

(defthm vl-modulelist-p-of-vl-warn-problem-modulelist
  (implies (force (vl-modulelist-p x))
           (vl-modulelist-p (vl-warn-problem-modulelist x problems)))
  :hints(("Goal" :induct (len x))))

(define vl-design-problem-mods
  :parents (vl-simplify)
  :short "Remove user-specified problem modules from the design."
  ((design   vl-design-p)
   (problems string-listp))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       ((vl-design design) design)
       (new-mods (vl-warn-problem-modulelist design.mods problems)))
    (change-vl-design design :mods new-mods)))

