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
(include-book "../mlib/find-module")
(local (include-book "../util/arithmetic"))

(defxdoc drop-blankports
  :parents (transforms)
  :short "A transformation which eliminates \"blank ports\" from modules,
and deletes all corresponding arguments from module instances."

  :long "<p>See @(see vl-port-p) and @(see vl-plainarg-p) for some discussion
about blank ports and arguments.  Blank ports are completely useless.  In this
transformation, we remove blank ports from modules and simultaneously remove
all corresponding arguments from all instances of the module.</p>

<p>This transformation only expects to deal with plain argument lists, so it
should be run only after @(see argresolve).  There are no other requirements
for using it.</p>")

(defsection vl-plainarglist-drop-blankports

  (defund vl-plainarglist-drop-blankports (args ports)
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-portlist-p ports)
                                (same-lengthp args ports))))
    (cond ((atom args)
           nil)
          ((vl-port->expr (car ports))
           (cons (car args)
                 (vl-plainarglist-drop-blankports (cdr args) (cdr ports))))
          (t
           (vl-plainarglist-drop-blankports (cdr args) (cdr ports)))))

  (local (in-theory (enable vl-plainarglist-drop-blankports)))

  (defthm vl-plainarglist-p-of-vl-plainarglist-drop-blankports
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-portlist-p ports))
                  (force (same-lengthp args ports)))
             (vl-plainarglist-p
              (vl-plainarglist-drop-blankports args ports)))))



(defsection vl-modinst-drop-blankports
  :parents (drop-blankports)
  :short "Drop any blank ports from a module instance."

  (defund vl-modinst-drop-blankports (x mods modalist warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (vl-warninglist-p warnings))))
    (b* (((vl-modinst x) x)

         (target-mod (vl-fast-find-module x.modname mods modalist))
         ((unless target-mod)
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname)
                   :fatalp t
                   :fn 'vl-modinst-drop-blankports)))
            (mv (cons w warnings) x)))

         ((when (vl-arguments->namedp x.portargs))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: expected all modules to be using plain arguments, ~
                         but found named arguments.  Did you forget to run the ~
                         argresolve transform first?"
                   :args (list x)
                   :fatalp t
                   :fn 'vl-modinst-drop-blankports)))
            (mv (cons w warnings) x)))

         (ports         (vl-module->ports target-mod))
         (plainargs     (vl-arguments->args x.portargs))

         ((unless (same-lengthp plainargs ports))
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: bad arity.  Expected ~x1 arguments but found ~x2 ~
                         arguments."
                   :args (list x (len ports) (len plainargs))
                   :fatalp t
                   :fn 'vl-modinst-drop-blankports)))
            (mv (cons w warnings) x)))

         (new-plainargs (vl-plainarglist-drop-blankports plainargs ports))
         (new-arguments (vl-arguments nil new-plainargs))
         (x-prime       (change-vl-modinst x :portargs new-arguments)))

      (mv warnings x-prime)))

  (local (in-theory (enable vl-modinst-drop-blankports)))

  (defthm vl-warninglist-p-of-vl-modinst-drop-blankports
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinst-drop-blankports x mods modalist warnings)))))

  (defthm vl-modinst-p-of-vl-modinst-drop-blankports
    (implies (and (force (vl-modinst-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-modinst-p
              (mv-nth 1 (vl-modinst-drop-blankports x mods modalist warnings))))))



(defsection vl-modinstlist-drop-blankports
  :parents (drop-blankports)
  :short "Extends @(see vl-modinst-drop-blankports) to a list of module
instances."

  (defund vl-modinstlist-drop-blankports (x mods modalist warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv warnings nil)
      (b* (((mv warnings car-prime)
            (vl-modinst-drop-blankports (car x) mods modalist warnings))
           ((mv warnings cdr-prime)
            (vl-modinstlist-drop-blankports (cdr x) mods modalist warnings))
           (x-prime
            (cons car-prime cdr-prime)))
        (mv warnings x-prime))))

  (local (in-theory (enable vl-modinstlist-drop-blankports)))

  (defthm vl-warninglist-p-of-vl-modinstlist-drop-blankports
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinstlist-drop-blankports x mods modalist warnings)))))

  (defthm vl-modinstlist-p-of-vl-modinstlist-drop-blankports
    (implies (and (vl-modinstlist-p x)
                  (vl-modulelist-p mods)
                  (equal modalist (vl-modalist mods)))
             (vl-modinstlist-p
              (mv-nth 1 (vl-modinstlist-drop-blankports x mods modalist warnings))))))



(defsection vl-portlist-drop-blankports
  :parents (drop-blankports)
  :short "Drop any blank ports from a list of ports."

  (defund vl-portlist-drop-blankports (x)
    (declare (xargs :guard (vl-portlist-p x)))
    (cond ((atom x)
           nil)
          ((vl-port->expr (car x))
           (cons (car x) (vl-portlist-drop-blankports (cdr x))))
          (t
           (vl-portlist-drop-blankports (cdr x)))))

  (local (in-theory (enable vl-portlist-drop-blankports)))

  (defthm vl-portlist-p-of-vl-portlist-drop-blankports
    (implies (force (vl-portlist-p x))
             (vl-portlist-p (vl-portlist-drop-blankports x)))))


(defsection vl-module-drop-blankports
  :parents (drop-blankports)
  :short "Drop any blank ports from a module, and simultaneously remove any
blank ports from all module instances within the module."

  (defund vl-module-drop-blankports (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    ;; Note: we don't respect hands-off, but it doesn't seem like it would be
    ;; legitimate to do so: the correctness of this transformation requires
    ;; that the instances throughout every module be updated.
    (b* (((vl-module x) x)
         (ports (vl-portlist-drop-blankports x.ports))
         ((mv warnings modinsts)
          (vl-modinstlist-drop-blankports x.modinsts mods modalist x.warnings))
         (x-prime
          (change-vl-module x
                            :ports ports
                            :modinsts modinsts
                            :warnings warnings)))
      x-prime))

  (local (in-theory (enable vl-module-drop-blankports)))

  (defthm vl-module-p-of-vl-module-drop-blankports
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p
              (vl-module-drop-blankports x mods modalist))))

  (defthm vl-module->name-of-vl-module-drop-blankports
    (equal (vl-module->name (vl-module-drop-blankports x mods modalist))
           (vl-module->name x))))



(defsection vl-modulelist-drop-blankports-aux
  :parents (drop-blankports)
  :short "Projects @(see vl-module-blankargs) across a module list."

  (defprojection vl-modulelist-drop-blankports-aux (x mods modalist)
    (vl-module-drop-blankports x mods modalist)
    :guard (and (vl-modulelist-p x)
                (vl-modulelist-p mods)
                (equal modalist (vl-modalist mods)))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-drop-blankports-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-drop-blankports-aux
    (equal (vl-modulelist->names (vl-modulelist-drop-blankports-aux x mods modalist))
           (vl-modulelist->names x))))



(defsection vl-modulelist-drop-blankports
  :parents (drop-blankports)
  :short "Top-level @(see drop-blankports) transformation."

  (defund vl-modulelist-drop-blankports (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (x-prime  (vl-modulelist-drop-blankports-aux x x modalist))
         (-        (fast-alist-free modalist)))
      x-prime))

  (local (in-theory (enable vl-modulelist-drop-blankports)))

  (defthm vl-modulelist-p-of-vl-modulelist-drop-blankports
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-drop-blankports x))))

  (defthm vl-modulelist->names-of-vl-modulelist-drop-blankports
    (equal (vl-modulelist->names (vl-modulelist-drop-blankports x))
           (vl-modulelist->names x))))

