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
(include-book "../primitives")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))

(defxdoc gate-elim
  :parents (transforms)
  :short "Convert gate instances into instances of VL @(see primitives)."

  :long "<p>This transformation eliminates any instances of basic gates (buf,
not, and, or, xor, nand, nor, and xnor), and replaces them with instances of
the VL's primitive modules like @(see *vl-1-bit-and*).</p>

<p>Note that this transform does not preserve delays.</p>

<p>Ordering notes.  This transform should typically be run after @(see
gatesplit), and also after other transforms like @(see blankargs), @(see
expression-sizing), and @(see replicate).</p>

<p>We only try to deal with non-array instances of gates, with the usual
arities (i.e., 2 arguments to a NOT or BUF, and 3 arguments to AND, OR,
...).</p>")

(local (xdoc::set-default-parents gate-elim))

(define vl-gateinst-primitive-module ((type vl-gatetype-p))
  (case type
    (:vl-buf  *vl-1-bit-buf*)
    (:vl-not  *vl-1-bit-not*)
    (:vl-and  *vl-1-bit-and*)
    (:vl-or   *vl-1-bit-or*)
    (:vl-xor  *vl-1-bit-xor*)
    (:vl-nand *vl-1-bit-nand*)
    (:vl-nor  *vl-1-bit-nor*)
    (:vl-xnor *vl-1-bit-xnor*)
    (:vl-bufif0 *vl-1-bit-bufif0*)
    (:vl-bufif1 *vl-1-bit-bufif1*)
    (:vl-notif0 *vl-1-bit-notif0*)
    (:vl-notif1 *vl-1-bit-notif1*)
    (:vl-nmos *vl-1-bit-nmos*)
    (:vl-rnmos *vl-1-bit-rnmos*)
    (:vl-pmos *vl-1-bit-pmos*)
    (:vl-rpmos *vl-1-bit-rpmos*)
    (:vl-cmos *vl-1-bit-cmos*)
    (:vl-rcmos *vl-1-bit-rcmos*)
    (:vl-tran *vl-1-bit-tran*)
    (:vl-rtran *vl-1-bit-rtran*)
    (:vl-tranif0 *vl-1-bit-tranif0*)
    (:vl-rtranif0 *vl-1-bit-rtranif0*)
    (:vl-tranif1 *vl-1-bit-tranif1*)
    (:vl-rtranif1 *vl-1-bit-rtranif1*)
    (:vl-pullup *vl-1-bit-pullup*)
    (:vl-pulldown *vl-1-bit-pulldown*)
    (otherwise nil)))

(local (in-theory (enable vl-gateinst-primitive-module)))


(define vl-add-portnames-to-plainargs
  :short "Goofy operation to name the arguments as we convert gate instances."
  ((plainargs vl-plainarglist-p
              "Plainargs from a gate instance, which already should have their
               directions computed.")
   (ports     vl-portlist-p
              "Ports from the corresponding VL primitive.  We want to give the
               plainargs the names from these ports."))
  :guard (same-lengthp plainargs ports)
  :returns (new-args vl-plainarglist-p :hyp :fguard)
  (if (atom plainargs)
      nil
    (cons (change-vl-plainarg (car plainargs) :portname (vl-port->name (car ports)))
          (vl-add-portnames-to-plainargs (cdr plainargs) (cdr ports)))))


(define vl-gateinst-gate-elim
  :short "Try to convert a single gate into one of VL's primitive modules."
  ((x        vl-gateinst-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings  vl-warninglist-p)
      (gateinsts vl-gateinstlist-p :hyp (force (vl-gateinst-p x)))
      (modinsts  vl-modinstlist-p  :hyp (force (vl-gateinst-p x)))
      (addmods   vl-modulelist-p   :hyp (force (vl-gateinst-p x))))

  :long "<p>We try to convert the gate instance @('x') into an instance of the
corresponding <see topic='@(url primitives)'>primitive</see> VL module.  We
return new lists of @('gateinsts') and @('modinsts') that should collectively
replace this gate instance.  The idea is that the replacement
gateinsts/modinsts should be equivalent to the gate being eliminated.</p>

<p>We may fail to eliminate @('x') for several reasons, for instance:</p>

<ul>

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

  (b* (((vl-gateinst x) x)

       (target (vl-gateinst-primitive-module x.type))
       (exprs  (vl-plainarglist->exprs x.args))

       ((unless target)
        (mv (warn :type :vl-gate-elim-fail
                  :msg "~a0: gates of type ~x1 are not supported by ~
                        gate-elim; leaving this gate unchanged."
                  :args (list x x.type))
            (list x) nil nil))

       (ports (vl-module->ports target))

       ((unless (and (not x.range)
                     (same-lengthp x.args ports)
                     (not (member nil exprs))
                     (all-equalp 1 (vl-exprlist->finalwidths exprs))))
        (mv (warn :type :vl-gate-elim-fail
                  :msg "~a0: gates with ~s1 are not supported by gate-elim; ~
                        leaving this gate unchanged."
                  :args (list x (cond (x.range "arrays")
                                      ((not (same-lengthp x.args ports))
                                       "extra arguments")
                                      ((member nil exprs) "blank arguments")
                                      (t "wide arguments"))))
            (list x) nil nil))

       (args (vl-add-portnames-to-plainargs x.args ports))
       (modinst (make-vl-modinst :instname  x.name
                                 :modname   (vl-module->name target)
                                 :portargs  (vl-arguments nil args)
                                 :paramargs (vl-arguments nil nil)
                                 :loc       x.loc)))
    (mv (ok) nil (list modinst) (list target)))
  ///
  (defmvtypes vl-gateinst-gate-elim (nil true-listp true-listp true-listp)))


(define vl-gateinstlist-gate-elim
  :short "Extends @(see vl-gateinst-gate-elim) to a list of gate instances."
  ((x        vl-gateinstlist-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings  vl-warninglist-p)
      (gateinsts vl-gateinstlist-p :hyp (force (vl-gateinstlist-p x)))
      (modinsts  vl-modinstlist-p  :hyp (force (vl-gateinstlist-p x)))
      (addmods   vl-modulelist-p   :hyp (force (vl-gateinstlist-p x))))
  (b* (((when (atom x))
        (mv (ok) nil nil nil))
       ((mv warnings car-gateinsts car-modinsts car-addmods)
        (vl-gateinst-gate-elim (car x) warnings))
       ((mv warnings cdr-gateinsts cdr-modinsts cdr-addmods)
        (vl-gateinstlist-gate-elim (cdr x) warnings)))
    (mv warnings
        (append car-gateinsts cdr-gateinsts)
        (append car-modinsts  cdr-modinsts)
        (append car-addmods   cdr-addmods)))
  ///
  (defmvtypes vl-gateinstlist-gate-elim (nil true-listp true-listp true-listp)))


(define vl-module-gate-elim
  :short "Convert gates throughout a module."
  ((x vl-module-p))
  :returns (mv (new-x vl-module-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
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
    (mv new-x addmods))
  ///
  (defmvtypes vl-module-gate-elim (nil true-listp)))

(define vl-modulelist-gate-elim-aux
  :short "Extends @(see vl-module-gate-elim) across a module list."
  ((x vl-modulelist-p))
  :returns (mv (new-x vl-modulelist-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime car-addmods) (vl-module-gate-elim (car x)))
       ((mv cdr-prime cdr-addmods) (vl-modulelist-gate-elim-aux (cdr x))))
    (mv (cons car-prime cdr-prime)
        (append car-addmods cdr-addmods)))
  ///
  (defmvtypes vl-modulelist-gate-elim-aux (true-listp true-listp)))

(define vl-modulelist-gate-elim
  :short "Convert gates throughout a list of modules and add any new primitives
into the module list."
  ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* (((mv new-x addmods)
        (vl-modulelist-gate-elim-aux x))
       (addmods (mergesort addmods))
       (allmods (mergesort (append addmods new-x)))
       ((unless (uniquep (vl-modulelist->names allmods)))
        (raise 'vl-modulelist-gate-elim
               "Name collision for ~&0."
               (duplicated-members (vl-modulelist->names allmods)))))
    allmods))

(define vl-design-gate-elim
  :short "Top-level @(see gate-elim) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-gate-elim x.mods))))

