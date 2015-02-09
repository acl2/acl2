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
expression-sizing), and @(see replicate-insts).</p>

<p>We only try to deal with non-array instances of gates, with the usual
arities (i.e., 2 arguments to a NOT or BUF, and 3 arguments to AND, OR,
...).</p>")

(local (xdoc::set-default-parents gate-elim))

(defconst *vl-gateinst-primitives-alist*
  `((:vl-buf  . ,*vl-1-bit-buf*)
    (:vl-not  . ,*vl-1-bit-not*)
    (:vl-and  . ,*vl-1-bit-and*)
    (:vl-or   . ,*vl-1-bit-or*)
    (:vl-xor  . ,*vl-1-bit-xor*)
    (:vl-nand . ,*vl-1-bit-nand*)
    (:vl-nor  . ,*vl-1-bit-nor*)
    (:vl-xnor . ,*vl-1-bit-xnor*)
    (:vl-bufif0 . ,*vl-1-bit-bufif0*)
    (:vl-bufif1 . ,*vl-1-bit-bufif1*)
    (:vl-notif0 . ,*vl-1-bit-notif0*)
    (:vl-notif1 . ,*vl-1-bit-notif1*)
    (:vl-nmos . ,*vl-1-bit-nmos*)
    (:vl-rnmos . ,*vl-1-bit-rnmos*)
    (:vl-pmos . ,*vl-1-bit-pmos*)
    (:vl-rpmos . ,*vl-1-bit-rpmos*)
    (:vl-cmos . ,*vl-1-bit-cmos*)
    (:vl-rcmos . ,*vl-1-bit-rcmos*)
    (:vl-tran . ,*vl-1-bit-tran*)
    (:vl-rtran . ,*vl-1-bit-rtran*)
    (:vl-tranif0 . ,*vl-1-bit-tranif0*)
    (:vl-rtranif0 . ,*vl-1-bit-rtranif0*)
    (:vl-tranif1 . ,*vl-1-bit-tranif1*)
    (:vl-rtranif1 . ,*vl-1-bit-rtranif1*)
    (:vl-pullup . ,*vl-1-bit-pullup*)
    (:vl-pulldown . ,*vl-1-bit-pulldown*)))

(fty::defalist vl-primalist
  :key-type symbolp
  :val-type vl-module-p
  :keyp-of-nil t
  :valp-of-nil nil
  :short "An alist mapping gate primitive names to primitive modules.")



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
   (primalist vl-primalist-p
              "Mapping from gate types to primitive modules")
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

<li>it is an array of gates (these can be split up by @(see
replicate-insts)),</li>

<li>it has blank arguments (these can be handled by @(see blankargs)), or</li>

<li>its arguments are not one-bit expressions, since these sometimes have odd
semantics in Cadence (see for instance the comments in @(see
vl-make-gates-for-buf/not), which is part of the gatesplit transform.)</li>

</ul>

<p>In case of such a failure, we add non-fatal warnings to explain what
happened and leave the gate unchanged.</p>"

  (b* (((vl-gateinst x) x)

       (target (cdr (hons-assoc-equal x.type primalist)))
       (exprs  (vl-plainarglist->exprs x.args))

       ((unless target)
        (mv (warn :type :vl-gate-elim-fail
                  :msg "~a0: gates of type ~x1 are not supported by ~
                        gate-elim; leaving this gate unchanged."
                  :args (list x x.type))
            (list x) nil nil))

       (target (vl-module-fix target))

       (ports (vl-module->ports target))

       ((unless (and (not x.range)
                     (not (vl-collect-interface-ports ports))
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
       (modinst (make-vl-modinst
                 :instname  x.name
                 :modname   (vl-module->name target)
                 :portargs  (make-vl-arguments-plain :args args)
                 :paramargs (make-vl-paramargs-plain :args nil)
                 :loc       x.loc)))
    (mv (ok) nil (list modinst) (list target)))
  ///
  (defmvtypes vl-gateinst-gate-elim (nil true-listp true-listp true-listp)))


(define vl-gateinstlist-gate-elim
  :short "Extends @(see vl-gateinst-gate-elim) to a list of gate instances."
  ((x        vl-gateinstlist-p)
   (primalist vl-primalist-p
              "Mapping from gate types to primitive modules")
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings  vl-warninglist-p)
      (gateinsts vl-gateinstlist-p :hyp (force (vl-gateinstlist-p x)))
      (modinsts  vl-modinstlist-p  :hyp (force (vl-gateinstlist-p x)))
      (addmods   vl-modulelist-p   :hyp (force (vl-gateinstlist-p x))))
  (b* (((when (atom x))
        (mv (ok) nil nil nil))
       ((mv warnings car-gateinsts car-modinsts car-addmods)
        (vl-gateinst-gate-elim (car x) primalist warnings))
       ((mv warnings cdr-gateinsts cdr-modinsts cdr-addmods)
        (vl-gateinstlist-gate-elim (cdr x) primalist warnings)))
    (mv warnings
        (append car-gateinsts cdr-gateinsts)
        (append car-modinsts  cdr-modinsts)
        (append car-addmods   cdr-addmods)))
  ///
  (defmvtypes vl-gateinstlist-gate-elim (nil true-listp true-listp true-listp)))


(define vl-module-gate-elim
  :short "Convert gates throughout a module."
  ((x vl-module-p)
   (primalist vl-primalist-p
              "Mapping from gate types to primitive modules"))
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
        (vl-gateinstlist-gate-elim x.gateinsts primalist x.warnings))
       (new-x (change-vl-module x
                                :warnings  warnings
                                :gateinsts new-gateinsts
                                :modinsts  (append new-modinsts x.modinsts))))
    (mv new-x addmods))
  ///
  (defmvtypes vl-module-gate-elim (nil true-listp)))

(define vl-modulelist-gate-elim-aux
  :short "Extends @(see vl-module-gate-elim) across a module list."
  ((x vl-modulelist-p)
   (primalist vl-primalist-p
              "Mapping from gate types to primitive modules"))
  :returns (mv (new-x vl-modulelist-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car-prime car-addmods) (vl-module-gate-elim (car x) primalist))
       ((mv cdr-prime cdr-addmods) (vl-modulelist-gate-elim-aux (cdr x) primalist)))
    (mv (cons car-prime cdr-prime)
        (append car-addmods cdr-addmods)))
  ///
  (defmvtypes vl-modulelist-gate-elim-aux (true-listp true-listp)))

(define vl-modulelist-gate-elim
  :short "Convert gates throughout a list of modules and add any new primitives
into the module list."
  ((x vl-modulelist-p)
   &key
   ((primalist vl-primalist-p
               "Mapping from gate types to primitive modules")
    '*vl-gateinst-primitives-alist*))
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* (((mv new-x addmods)
        (vl-modulelist-gate-elim-aux x primalist))
       (addmods (mergesort addmods))
       (allmods (mergesort (append addmods new-x)))
       ((unless (uniquep (vl-modulelist->names allmods)))
        (raise 'vl-modulelist-gate-elim
               "Name collision for ~&0."
               (duplicated-members (vl-modulelist->names allmods)))))
    allmods))

(define vl-design-gate-elim
  :short "Top-level @(see gate-elim) transform."
  ((x vl-design-p)
   &key
   ((primalist vl-primalist-p
               "Mapping from gate types to primitive modules")
    '*vl-gateinst-primitives-alist*))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-gate-elim x.mods :primalist primalist))))


