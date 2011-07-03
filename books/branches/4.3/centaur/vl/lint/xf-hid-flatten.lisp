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
(include-book "../transforms/xf-hid-elim")
(local (include-book "../util/arithmetic"))

; VL-Lint Only.
;
; We now introduce the VL-Lint version of HID elimination.
;
; The basic idea is to replace any hierarchical identifiers with flat wires of
; the appropriate size.  The HID elimination code isn't quite right for our
; purposes because it tries to introduce $externals modules, eliminate reset
; aliases, and so on.  But, it does nicely try to replace all HIDs it can and
; leaves any other HIDs alone.
;
; So, we use the same core algorithms.  Then we eventually go back and throw
; away any unresolved hids with our "toohard" transformation.  This localizes
; any disruption from malformed HIDs to the particular module elements that are
; affected, and is easy to code.

(defsection vl-module-hid-flatten

  (defund vl-module-hid-flatten (x mods modalist)
    "Returns X-PRIME"
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((vl-module x) x)

         (warnings x.warnings)
         (new-netdecls nil)
         ((mv warnings assigns new-netdecls)
          (vl-assignlist-hid-elim x.assigns mods modalist warnings new-netdecls))
         ((mv warnings modinsts new-netdecls)
          (vl-modinstlist-hid-elim x.modinsts mods modalist warnings new-netdecls))
         ((mv warnings gateinsts new-netdecls)
          (vl-gateinstlist-hid-elim x.gateinsts mods modalist warnings new-netdecls))
         ((mv warnings alwayses new-netdecls)
          (vl-alwayslist-hid-elim x.alwayses mods modalist warnings new-netdecls))
         ((mv warnings initials new-netdecls)
          (vl-initiallist-hid-elim x.initials mods modalist warnings new-netdecls))

         (new-netdecls
          ;; Crucial, to throw away duplicates.
          (mergesort new-netdecls)))

      (change-vl-module x
                        :netdecls (append-without-guard new-netdecls x.netdecls)
                        :warnings warnings
                        :assigns assigns
                        :modinsts modinsts
                        :gateinsts gateinsts
                        :alwayses alwayses
                        :initials initials)))

  (local (in-theory (enable vl-module-hid-flatten)))

  (defthm vl-module-p-of-vl-module-hid-flatten
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (vl-module-hid-flatten x mods modalist))))

  (defthm vl-module->name-of-vl-module-hid-flatten
    (equal (vl-module->name (vl-module-hid-flatten x mods modalist))
           (vl-module->name x))))


(defsection vl-modulelist-hid-flatten-aux

  (defprojection vl-modulelist-hid-flatten-aux (x mods modalist)
    (vl-module-hid-flatten x mods modalist)
    :guard (and (vl-modulelist-p x)
                (vl-modulelist-p mods)
                (equal modalist (vl-modalist mods)))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-hid-flatten-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-hid-flatten-aux
    (equal (vl-modulelist->names (vl-modulelist-hid-flatten-aux x mods modalist))
           (vl-modulelist->names x))))


(defsection vl-modulelist-hid-flatten

  (defund vl-modulelist-hid-flatten (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (ret      (vl-modulelist-hid-flatten-aux x x modalist))
         (-        (fast-alist-free modalist)))
      ret))

  (local (in-theory (enable vl-modulelist-hid-flatten)))

  (defthm vl-modulelist-p-of-vl-modulelist-hid-flatten
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-hid-flatten x))))

  (defthm vl-modulelist->names-of-vl-modulelist-hid-flatten
    (equal (vl-modulelist->names (vl-modulelist-hid-flatten x))
           (vl-modulelist->names x))))

