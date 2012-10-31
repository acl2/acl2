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
(include-book "../mlib/namefactory")
(local (include-book "../util/arithmetic"))


(defxdoc addinstnames
  :parents (transforms)
  :short "Name any unnamed gate or module instances"

  :long "<p>This transformation does nothing more than generate a name for
every gate and module instance which are unnamed.  The names are safely
generated using a @(see vl-namefactory-p) and will have names such as
@('modinst_11') and @('gateinst_46').</p>

<p>This transform is curiously expensive.  My guess is that occform is putting
in a lot of gates that don't have names, so that almost all modules need to be
processed, and it gets expensive to compute the module namespaces for all of
the modules.</p>")



(defsection vl-modinst-addinstnames
  :parents (addinstnames)
  :short "Name a @(see vl-modinst-p), if necessary."

  :long "<p><b>Signature</b>: @(call vl-modinst-addinstnames) returns @('(mv
x-prime nf-prime)').</p>

<p>@('x') is a modinst which occurs within @('mod'), and @('nf') is a @(see
vl-namefactory-p) that allows us to generate unique names.</p>"

  (defund vl-modinst-addinstnames (x nf)
    "Returns (MV X-PRIME NF-PRIME)"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-namefactory-p nf))))
    (b* (((when (vl-modinst->instname x))
          ;; No need to generate a name.
          (mv x nf))
         ((mv new-name nf)
          (vl-namefactory-indexed-name "modinst" nf))
         (x-prime (change-vl-modinst x :instname new-name)))
        (mv x-prime nf)))

  (local (in-theory (enable vl-modinst-addinstnames)))

  (defthm vl-modinst-p-of-vl-modinst-addinstnames
    (implies (and (force (vl-modinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-modinst-p (mv-nth 0 (vl-modinst-addinstnames x nf)))))

  (defthm vl-namefactory-p-of-vl-modinst-addinstnames
    (implies (and (force (vl-modinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 1 (vl-modinst-addinstnames x nf))))))



(defsection vl-modinstlist-addinstnames
  :parents (addinstnames)
  :short "Extend @(see vl-modinst-addinstnames) across a list of module
instances."

  (defund vl-modinstlist-addinstnames (x nf)
    "Returns (MV X-PRIME NF-PRIME)"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-namefactory-p nf))))
    (b* (((when (atom x))
          (mv nil nf))
         ((mv new-car nf) (vl-modinst-addinstnames (car x) nf))
         ((mv new-cdr nf) (vl-modinstlist-addinstnames (cdr x) nf))
         (x-prime         (cons new-car new-cdr)))
        (mv x-prime nf)))

  (local (in-theory (enable vl-modinstlist-addinstnames)))

  (defthm vl-modinstlist-p-of-vl-modinstlist-addinstnames
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-modinstlist-p (mv-nth 0 (vl-modinstlist-addinstnames x nf)))))

  (defthm vl-namefactory-p-of-vl-modinstlist-addinstnames
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 1 (vl-modinstlist-addinstnames x nf))))))



(defsection vl-gateinst-addinstnames
  :parents (addinstnames)
  :short "Like @(see vl-modinst-addinstnames), but for gate instances."

  (defund vl-gateinst-addinstnames (x nf)
    "Returns (MV X-PRIME NF-PRIME)"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-namefactory-p nf))))
    (b* (((when (vl-gateinst->name x))
          ;; No need to generate a name.
          (mv x nf))
         ((mv new-name nf)
          (vl-namefactory-indexed-name "gateinst" nf))
         (x-prime (change-vl-gateinst x :name new-name)))
        (mv x-prime nf)))

  (local (in-theory (enable vl-gateinst-addinstnames)))

  (defthm vl-gateinst-p-of-vl-gateinst-addinstnames
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-gateinst-p (mv-nth 0 (vl-gateinst-addinstnames x nf)))))

  (defthm vl-namefactory-p-of-vl-gateinst-addinstnames
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 1 (vl-gateinst-addinstnames x nf))))))



(defsection vl-gateinstlist-addinstnames
  :parents (addinstnames)
  :short "Extend @(see vl-gateinst-addinstnames) across a list of gate
instances."

  (defund vl-gateinstlist-addinstnames (x nf)
    "Returns (MV X-PRIME NF-PRIME)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-namefactory-p nf))))
    (b* (((when (atom x))
          (mv nil nf))
         ((mv new-car nf) (vl-gateinst-addinstnames (car x) nf))
         ((mv new-cdr nf) (vl-gateinstlist-addinstnames (cdr x) nf))
         (x-prime         (cons new-car new-cdr)))
        (mv x-prime nf)))

  (local (in-theory (enable vl-gateinstlist-addinstnames)))

  (defthm vl-gateinstlist-p-of-vl-gateinstlist-addinstnames
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-gateinstlist-p (mv-nth 0 (vl-gateinstlist-addinstnames x nf)))))

  (defthm vl-namefactory-p-of-vl-gateinstlist-addinstnames
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (vl-namefactory-p (mv-nth 1 (vl-gateinstlist-addinstnames x nf))))))



(defund vl-modinstlist-all-named-p (x)
  (declare (xargs :guard (vl-modinstlist-p x)))
  (or (atom x)
      (and (vl-modinst->instname (car x))
           (vl-modinstlist-all-named-p (cdr x)))))

(defund vl-gateinstlist-all-named-p (x)
  (declare (xargs :guard (vl-gateinstlist-p x)))
  (or (atom x)
      (and (vl-gateinst->name (car x))
           (vl-gateinstlist-all-named-p (cdr x)))))


(defsection vl-module-addinstnames
  :parents (addinstnames)
  :short "Name any unnamed module and gate instances throughout a module."

  :long "<p><b>Signature:</b> @(call vl-module-addinstnames) returns
@('x-prime').</p>"

  (defund vl-module-addinstnames (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          x)
         (modinsts         (vl-module->modinsts x))
         (gateinsts        (vl-module->gateinsts x))
         (mods-namedp      (vl-modinstlist-all-named-p modinsts))
         (gates-namedp     (vl-gateinstlist-all-named-p gateinsts))
         ((when (and mods-namedp gates-namedp))
          ;; Optimization.  Avoid reconsing when possible.
          x)

         (nf  (vl-starting-namefactory x))
         ((mv modinsts nf)
          ;; Optimization.  Avoid reconsing when possible.
          (if mods-namedp
              (mv modinsts nf)
            (vl-modinstlist-addinstnames modinsts nf)))
         ((mv gateinsts nf)
          ;; Optimization.  Avoid reconsing when possible.
          (if gates-namedp
              (mv gateinsts nf)
            (vl-gateinstlist-addinstnames gateinsts nf)))
         (- (vl-free-namefactory nf)))
        (change-vl-module x
                          :modinsts modinsts
                          :gateinsts gateinsts)))

  (local (in-theory (enable vl-module-addinstnames)))

  (defthm vl-module-p-of-vl-module-addinstnames
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-addinstnames x))))

  (defthm vl-module->name-of-vl-module-addinstnames
    (equal (vl-module->name (vl-module-addinstnames x))
           (vl-module->name x))))



(defsection vl-modulelist-addinstnames
  :parents (addinstnames)
  :short "Extend @(see vl-module-addinstnames) across a module list."

  (defprojection vl-modulelist-addinstnames (x)
    (vl-module-addinstnames x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-addinstnames)))

  (defthm vl-modulelist->names-of-vl-modulelist-addinstnames
    (equal (vl-modulelist->names (vl-modulelist-addinstnames x))
           (vl-modulelist->names x))))
