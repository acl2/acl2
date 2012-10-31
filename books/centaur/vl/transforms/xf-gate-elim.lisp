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
(include-book "../primitives")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))



(defxdoc gate-elim
  :parents (transforms)
  :short "Convert gate instances into <see topic='@(url
primitives)'>primitive</see> VL module instances."

  :long "<p>This transformation eliminates any instances of basic gates (buf,
not, and, or, xor, nand, nor, and xnor), and replaces them with instances of
the VL's primitive modules like @(see *vl-1-bit-and*).</p>

<p>Note that this transform does not preserve delays.</p>

<p>Ordering notes.  This transform should typically be run after @(see
gatesplit) and @(see gateredux), and also after other transforms like @(see
blankargs), @(see expr-sizing), and @(see replicate).</p>

<p>We only try to deal with non-array instances of gates, with the usual
arities (i.e., 2 arguments to a NOT or BUF, and 3 arguments to AND, OR, ...).
We generally expect that the @(see gateredux), @(see gatesplit), and @(see
replicate) transforms will get all the gates into this format.</p>

<p><b>BOZO</b> it might make sense to merge this transform with @(see
gateredux).</p>")


(defund vl-gateinst-primitive-module (type)
  (declare (xargs :guard (vl-gatetype-p type)))
  (case type
    (:vl-buf  *vl-1-bit-buf*)
    (:vl-not  *vl-1-bit-not*)
    (:vl-and  *vl-1-bit-and*)
    (:vl-or   *vl-1-bit-or*)
    (:vl-xor  *vl-1-bit-xor*)
    (:vl-nand *vl-1-bit-nand*)
    (:vl-nor  *vl-1-bit-nor*)
    (:vl-xnor *vl-1-bit-xnor*)
    (otherwise nil)))

(local (in-theory (enable vl-gateinst-primitive-module)))



(defund vl-add-portnames-to-plainargs (plainargs ports)
  ;; Goofy operation: the plainargs come from a gate instance, the ports come
  ;; from the corresponding primitive VL module.  We just want to put the names
  ;; into the ports.  Their directions should already be correct.
  (declare (xargs :guard (and (vl-plainarglist-p plainargs)
                              (vl-portlist-p ports)
                              (same-lengthp plainargs ports))))
  (if (atom plainargs)
      nil
    (cons (change-vl-plainarg (car plainargs) :portname (vl-port->name (car ports)))
          (vl-add-portnames-to-plainargs (cdr plainargs) (cdr ports)))))

(defthm vl-plainarglist-p-of-vl-add-portnames-to-plainargs
  (implies (and (vl-plainarglist-p plainargs)
                (vl-portlist-p ports)
                (same-lengthp plainargs ports))
           (vl-plainarglist-p (vl-add-portnames-to-plainargs plainargs ports)))
  :hints(("Goal" :in-theory (enable vl-add-portnames-to-plainargs))))



(defsection vl-gateinst-gate-elim
  :parents (gate-elim)
  :short "Try to convert a single gate into one of VL's primitive modules."

  :long "<p><b>Signature:</b> @(call vl-gateinst-gate-elim) returns @('(mv
warnings gateinsts modinsts addmods)').</p>

<p>We try to convert the gate instance @('x') into an instance of the
corresponding <see topic='@(url primitives)'>primitive</see> VL module.  We
return new lists of @('gateinsts') and @('modinsts') that should collectively
replace this gate instance.  The idea is that the replacement
gateinsts/modinsts should be equivalent to the gate being eliminated.</p>

<p>We may fail to eliminate @('x') for several reasons, for instance:</p>

<ul>

<li>it is not one of the basic gate types (more complex gates can be handled by
@(see gateredux)),</li>

<li>it has more than the usual number of arguments (higher arity gates can
simplified by @(see gatesplit),</li>

<li>it is an array of gates (these can be split up by @(see replicate)),</li>

<li>it has blank arguments (these can be handled by @(see blankargs)), or</li>

<li>its arguments are not one-bit expressions, since these sometimes have odd
semantics in Cadence (see for instance the comments in @(see
vl-make-gates-for-buf/not), which is part of the gatesplit transform.)</li>

</ul>

<p>In case of such a failure, we add non-fatal warnings to explain what
happened and leave the gate unchanged.</p>"

  (defund vl-gateinst-gate-elim (x warnings)
    "Returns (MV WARNINGS GATEINSTS MODINSTS ADDMODS)"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-warninglist-p warnings))))
    (b* (((vl-gateinst x) x)

         (target (vl-gateinst-primitive-module x.type))
         (exprs  (vl-plainarglist->exprs x.args))

         ((unless target)
          (b* ((w (make-vl-warning
                   :type :vl-gate-elim-fail
                   :msg "~a0: gates of type ~x1 are not supported by ~
                         gate-elim; leaving this gate unchanged."
                   :args (list x x.type)
                   :fatalp nil
                   :fn 'vl-gateinst-gate-elim)))
            (mv (cons w warnings) (list x) nil nil)))

         (ports (vl-module->ports target))

         ((unless (and (not x.range)
                       (same-lengthp x.args ports)
                       (not (member nil exprs))
                       (all-equalp 1 (vl-exprlist->finalwidths exprs))))
          (b* ((w (make-vl-warning
                   :type :vl-gate-elim-fail
                   :msg "~a0: gates with ~s1 are not supported by gate-elim; ~
                         leaving this gate unchanged."
                   :args (list x (cond (x.range "arrays")
                                       ((not (same-lengthp x.args ports)) "extra arguments")
                                       ((member nil exprs) "blank arguments")
                                       (t "wide arguments")))
                   :fatalp nil
                   :fn 'vl-gateinst-gate-elim)))
            (mv (cons w warnings) (list x) nil nil)))

         (args (vl-add-portnames-to-plainargs x.args ports))
         (modinst (make-vl-modinst :instname  x.name
                                   :modname   (vl-module->name target)
                                   :portargs  (vl-arguments nil args)
                                   :paramargs (vl-arguments nil nil)
                                   :loc       x.loc)))
      (mv warnings nil (list modinst) (list target))))

  (local (in-theory (enable vl-gateinst-gate-elim)))

  (defmvtypes vl-gateinst-gate-elim (nil true-listp true-listp true-listp))

  (defthm vl-warninglist-p-of-vl-gateinst-gate-elim
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinst-gate-elim x warnings)))))

  (defthm vl-gateinst-gate-elim-basics
    (implies (force (vl-gateinst-p x))
             (let ((ret (vl-gateinst-gate-elim x warnings)))
               (and (vl-gateinstlist-p (mv-nth 1 ret))
                    (vl-modinstlist-p  (mv-nth 2 ret))
                    (vl-modulelist-p   (mv-nth 3 ret)))))))



(defsection vl-gateinstlist-gate-elim
  :parents (gate-elim)
  :short "Extends @(see vl-gateinst-gate-elim) to a list of gate instances."

  (defund vl-gateinstlist-gate-elim (x warnings)
    "Returns (MV WARNINGS GATEINSTS MODINSTS ADDMODS)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nil))
         ((mv warnings car-gateinsts car-modinsts car-addmods)
          (vl-gateinst-gate-elim (car x) warnings))
         ((mv warnings cdr-gateinsts cdr-modinsts cdr-addmods)
          (vl-gateinstlist-gate-elim (cdr x) warnings)))
      (mv warnings
          (append car-gateinsts cdr-gateinsts)
          (append car-modinsts  cdr-modinsts)
          (append car-addmods   cdr-addmods))))

  (local (in-theory (enable vl-gateinstlist-gate-elim)))

  (defmvtypes vl-gateinstlist-gate-elim (nil true-listp true-listp true-listp))

  (defthm vl-warninglist-p-of-vl-gateinstlist-gate-elim
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinstlist-gate-elim x warnings)))))

  (defthm vl-gateinstlist-gate-elim-basics
    (implies (force (vl-gateinstlist-p x))
             (let ((ret (vl-gateinstlist-gate-elim x warnings)))
               (and (vl-gateinstlist-p (mv-nth 1 ret))
                    (vl-modinstlist-p  (mv-nth 2 ret))
                    (vl-modulelist-p   (mv-nth 3 ret)))))))



(defsection vl-module-gate-elim
  :parents (gate-elim)
  :short "Convert gates throughout a module."

  (defund vl-module-gate-elim (x)
    "Returns (MV NEW-X ADDMODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)

         ((when (vl-module->hands-offp x))
          ;; Respect hands-off to avoid converting gates within the primitives,
          ;; etc.
          (mv x nil))

         ((unless x.gateinsts)
          ;; Dumb optimization to avoid re-consing
          (mv x nil))

         ((mv warnings new-gateinsts new-modinsts addmods)
          (vl-gateinstlist-gate-elim x.gateinsts x.warnings))

         (new-x (change-vl-module x
                                  :warnings  warnings
                                  :gateinsts new-gateinsts
                                  :modinsts  (append new-modinsts x.modinsts))))

      (mv new-x addmods)))

  (local (in-theory (enable vl-module-gate-elim)))

  (defmvtypes vl-module-gate-elim (nil true-listp))

  (defthm vl-module-p-of-vl-module-gate-elim
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-gate-elim x)))))

  (defthm vl-module->name-of-vl-module-gate-elim
    (equal (vl-module->name (mv-nth 0 (vl-module-gate-elim x)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-gate-elim
    (implies (force (vl-module-p x))
             (vl-modulelist-p (mv-nth 1 (vl-module-gate-elim x))))))



(defsection vl-modulelist-gate-elim-aux
  :parents (gate-elim)
  :short "Extends @(see vl-module-gate-elim) across a module list."

  (defund vl-modulelist-gate-elim-aux (x)
    "Returns (MV NEW-X ADDMODS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((when (atom x))
          (mv nil nil))
         ((mv car-prime car-addmods) (vl-module-gate-elim (car x)))
         ((mv cdr-prime cdr-addmods) (vl-modulelist-gate-elim-aux (cdr x))))
      (mv (cons car-prime cdr-prime)
          (append car-addmods cdr-addmods))))

  (local (in-theory (enable vl-modulelist-gate-elim-aux)))

  (defmvtypes vl-modulelist-gate-elim-aux (true-listp true-listp))

  (defthm vl-modulelist-gate-elim-aux-basics
    (implies (force (vl-modulelist-p x))
             (let ((ret (vl-modulelist-gate-elim-aux x)))
               (and (vl-modulelist-p (mv-nth 0 ret))
                    (vl-modulelist-p (mv-nth 1 ret)))))))



(defsection vl-modulelist-gate-elim
  :parents (gate-elim)
  :short "Convert gates throughout a list of modules and add any new primitives
into the module list."

  (defund vl-modulelist-gate-elim (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((mv new-x addmods)
          (vl-modulelist-gate-elim-aux x))
         (addmods (mergesort addmods))
         (allmods (mergesort (append addmods new-x)))
         ((unless (uniquep (vl-modulelist->names allmods)))
          (er hard? 'vl-modulelist-gate-elim
              "Name collision for ~&0."
              (duplicated-members (vl-modulelist->names allmods)))))
      allmods))

  (local (in-theory (enable vl-modulelist-gate-elim)))

  (defthm vl-modulelist-p-of-vl-modulelist-gate-elim
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-gate-elim x))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-gate-elim
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-gate-elim x)))))
