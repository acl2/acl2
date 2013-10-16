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
(include-book "mlib/range-tools")
(include-book "util/defwellformed")
(local (include-book "util/arithmetic"))



(defwellformed vl-portdecl-range-resolved-p (x)
  :guard (vl-portdecl-p x)
  :body (let ((range (vl-portdecl->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of portdecl ~s1: current range is ~x2."
                      (list (vl-portdecl->loc x)
                            (vl-portdecl->name x)
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-portdecl->range
  (implies (vl-portdecl-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-portdecl->range x)))
  :hints(("Goal" :in-theory (enable vl-portdecl-range-resolved-p))))

(defwellformed-list vl-portdecllist-ranges-resolved-p (x)
  :element vl-portdecl-range-resolved-p
  :guard (vl-portdecllist-p x))



(defwellformed vl-netdecl-range-resolved-p (x)
  :guard (vl-netdecl-p x)
  :body (let ((range (vl-netdecl->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of wire ~s1: current range is ~x2."
                      (list (vl-netdecl->loc x)
                            (vl-netdecl->name x)
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-netdecl->range
  (implies (vl-netdecl-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-netdecl->range x)))
  :hints(("Goal" :in-theory (enable vl-netdecl-range-resolved-p))))

(defwellformed-list vl-netdecllist-ranges-resolved-p (x)
  :element vl-netdecl-range-resolved-p
  :guard (vl-netdecllist-p x))

(defthm vl-range-resolved-p-of-vl-netdecl-range-of-vl-find-netdecl
  (implies (force (vl-netdecllist-ranges-resolved-p x))
           (vl-netdecl-range-resolved-p (vl-find-netdecl name x)))
  :hints(("Goal"
          :in-theory (enable vl-find-netdecl))))



(defwellformed vl-regdecl-range-resolved-p (x)
  :guard (vl-regdecl-p x)
  :body (let ((range (vl-regdecl->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of reg ~s1: current range is ~x2."
                      (list (vl-regdecl->loc x)
                            (vl-regdecl->name x)
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-regdecl->range
  (implies (vl-regdecl-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-regdecl->range x)))
  :hints(("Goal" :in-theory (enable vl-regdecl-range-resolved-p))))

(defwellformed-list vl-regdecllist-ranges-resolved-p (x)
  :element vl-regdecl-range-resolved-p
  :guard (vl-regdecllist-p x))

(defthm vl-range-resolved-p-of-vl-regdecl-range-of-vl-find-regdecl
  (implies (force (vl-regdecllist-ranges-resolved-p x))
           (vl-regdecl-range-resolved-p (vl-find-regdecl name x)))
  :hints(("Goal"
          :in-theory (enable vl-find-regdecl))))



(defwellformed vl-modinst-range-resolved-p (x)
  :guard (vl-modinst-p x)
  :body (let ((range (vl-modinst->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of modinst ~s1: current range is ~x2."
                      (list (vl-modinst->loc x)
                            (or (vl-modinst->instname x)
                                (cat "<unnamed instance of module "
                                     (vl-modinst->modname x)
                                     ">"))
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-modinst->range
  (implies (vl-modinst-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-modinst->range x)))
  :hints(("Goal" :in-theory (enable vl-modinst-range-resolved-p))))

(defwellformed-list vl-modinstlist-ranges-resolved-p (x)
  :element vl-modinst-range-resolved-p
  :guard (vl-modinstlist-p x))



(defwellformed vl-gateinst-range-resolved-p (x)
  :guard (vl-gateinst-p x)
  :body (let ((range (vl-gateinst->range x)))
          (@wf-assert (vl-maybe-range-resolved-p range)
                      :vl-range-unresolved
                      "~l0: failed to resolve range of gateinst ~s1: current range is ~x2."
                      (list (vl-gateinst->loc x)
                            (or (vl-gateinst->name x)
                                (cat "<unnamed gate of type "
                                     (symbol-name (vl-gateinst->type x))
                                     ">"))
                            range))))

(defthm vl-maybe-range-resolved-p-of-vl-gateinst->range
  (implies (vl-gateinst-range-resolved-p x)
           (vl-maybe-range-resolved-p (vl-gateinst->range x)))
  :hints(("Goal" :in-theory (enable vl-gateinst-range-resolved-p))))

(defwellformed-list vl-gateinstlist-ranges-resolved-p (x)
  :element vl-gateinst-range-resolved-p
  :guard (vl-gateinstlist-p x))




(defwellformed vl-module-ranges-resolved-p (x)
  :guard (vl-module-p x)
  :body
  (@wf-progn
   (@wf-call vl-portdecllist-ranges-resolved-p (vl-module->portdecls x))
   (@wf-call vl-netdecllist-ranges-resolved-p (vl-module->netdecls x))
   (@wf-call vl-regdecllist-ranges-resolved-p (vl-module->regdecls x))
   (@wf-call vl-modinstlist-ranges-resolved-p (vl-module->modinsts x))
   (@wf-call vl-gateinstlist-ranges-resolved-p (vl-module->gateinsts x))))

(defthm vl-portdecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-portdecllist-ranges-resolved-p (vl-module->portdecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-netdecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-netdecllist-ranges-resolved-p (vl-module->netdecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-regdecllist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-regdecllist-ranges-resolved-p (vl-module->regdecls x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-modinstlist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-modinstlist-ranges-resolved-p (vl-module->modinsts x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))

(defthm vl-gateinstlist-ranges-resolved-p-when-vl-module-ranges-resolved-p
  (implies (force (vl-module-ranges-resolved-p x))
           (vl-gateinstlist-ranges-resolved-p (vl-module->gateinsts x)))
  :hints(("Goal" :in-theory (enable vl-module-ranges-resolved-p))))



(defwellformed-list vl-modulelist-ranges-resolved-p (x)
  :element vl-module-ranges-resolved-p
  :guard (vl-modulelist-p x))



