; VL Verilog Toolkit
; Copyright (C) 2008-2012 Centaur Technology
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
(include-book "../mlib/find-item")
(include-book "../mlib/expr-tools")
(include-book "../mlib/expr-building")
(include-book "../mlib/expr-slice")
(local (include-book "../util/arithmetic"))

(defxdoc propagate-help
  :parents (transforms)
  :short "Split up assignments to concatenations to assist with @(see propagate)."

  :long "<p>The @(see propagate) transform can get rid of assignments to
\"intermediate\" wires, but only deals with assignments whose left-hand sides
are simple identifiers.  This limitation means that, in practice, it can fail
to carry out the desired propagation when there are assignments like this:</p>

@({
assign {net0413_4, net0413_3, net0413_2, net0413_1, net0413_0} = spb ;
})

<p>This is a helper transform that is meant to be run before propagate, in order
to split up assignments like the above into a form that propagate can process.  The
idea is to replace assignments like the above with sequences of assignments, e.g.,</p>

@({
assign net0413_4 = spb[4];
assign net0413_3 = spb[3];
assign net0413_2 = spb[2];
assign net0413_1 = spb[1];
assign net0413_0 = spb[0];
})

<p>After this, propagate can presumably eliminate these intermediate nets.</p>

<p>Prerequisites: expressions need to be sized and ranges resolved.  To keep
things as safe as possible, we only simplify assignments wehre the widths work
out exactly.</p>")

(local (in-theory (disable all-equalp)))

(local (defthm nat-listp-when-pos-listp
         ;; BOZO this is probably fine as a tau system rule, find it a home
         ;; and make it non-local.
         (implies (pos-listp x)
                  (nat-listp x))
         :rule-classes :tau-system
         :hints(("Goal" :induct (len x)))))


(define vl-prophelp-split
  ((lhs-wires "individual wires from the left-hand side's concatenation"
              (and (vl-exprlist-p lhs-wires)
                   (vl-idexprlist-p lhs-wires)
                   (pos-listp (vl-exprlist->finalwidths lhs-wires))))
   (rhs-bits  "exploded bits from the right-hand side expression"
              (and (true-listp rhs-bits)
                   (vl-exprlist-p rhs-bits)
                   (all-equalp 1 (vl-exprlist->finalwidths rhs-bits))))
   (loc       vl-location-p))
  :guard (equal (sum-nats (vl-exprlist->finalwidths lhs-wires))
                (len rhs-bits))
  :returns (assigns vl-assignlist-p :hyp :fguard)
  :parents (propagate-help)
  :short "Create an assignment for each individual wire on the left-hand side
to its associated bits from the right-hand side."

  (b* (((when (atom lhs-wires))
        nil)
       (lhs1   (car lhs-wires))
       (width1 (vl-expr->finalwidth lhs1))
       (bits1  (take width1 rhs-bits))
       (rhs1   (make-vl-nonatom :op :vl-concat
                                :args bits1
                                :finaltype :vl-unsigned
                                :finalwidth width1)))
    (cons (make-vl-assign :lvalue lhs1
                          :expr rhs1
                          :loc loc)
          (vl-prophelp-split (cdr lhs-wires)
                             (nthcdr width1 rhs-bits)
                             loc)))
  :prepwork
  ((local (defthm l0
            (implies (all-equalp a (vl-exprlist->finalwidths x))
                     (all-equalp a (vl-exprlist->finalwidths (nthcdr n x))))
            :hints(("Goal" :in-theory (enable nthcdr)))))))



(define vl-prophelp-assign
  ((x        "assignment to be split up, if it has the right form."
             vl-assign-p)
   (mod      "module the assignment occurs in, so we can slice up the rhs."
             vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod)))
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x vl-assignlist-p :hyp :fguard))
  :parents (propagate-help)
  :short "Maybe split up an assignment."
  (b* (((vl-assign x) x)

       ((when (vl-fast-atom-p x.lvalue))
        ;; Not applicable (assigning to an atom, not a concat)
        (mv warnings (list x)))

       ((vl-nonatom x.lvalue) x.lvalue)
       ((unless (and (eq x.lvalue.op :vl-concat)
                     (vl-idexprlist-p x.lvalue.args)
                     (vl-expr-sliceable-p x.expr)))
        ;; Not applicable (not a concat, or too hard)
        (mv warnings (list x)))

       (widths (vl-exprlist->finalwidths x.lvalue.args))
       ((unless (pos-listp widths))
        ;; Some width isn't computed, so how would we split it up?  Give up.
        (mv (warn :type :vl-prophelp-fail
                  :msg  "~a0: not splitting up assignment because the lhs ~
                         width is not determined!"
                  :args (list x))
            (list x)))

       (lhs-width (sum-nats widths))
       (rhs-width (vl-expr->finalwidth x.expr))
       ((unless (eql lhs-width rhs-width))
        ;; Widths don't agree, so give up; I don't want to think about how to
        ;; properly do truncations/extensions here.
        (mv (warn :type :vl-prophelp-fail
                  :msg "~a0: not splitting up assignment because the lhs/rhs ~
                        do not have the same width.  Lhs width is ~x1, rhs ~
                        width is ~x2."
                  :args (list x lhs-width rhs-width))
            (list x)))

       ((unless (and (vl-expr-welltyped-p x.lvalue)
                     (vl-expr-welltyped-p x.expr)))
        (mv (warn :type :vl-prophelp-fail
                  :msg "~a0: not splitting up assignment because lhs or rhs ~
                        is not well-typed."
                  :args (list x))
            (list x)))

       ((mv okp warnings rhs-bits)
        (vl-msb-bitslice-expr x.expr mod ialist warnings))
       ((unless okp)
        ;; Somehow failed to split up RHS?  Don't do anything.
        (mv (warn :type :vl-prophelp-fail
                  :msg "~a0: not splitting up assignment because we somehow ~
                        failed to slice its rhs into bits."
                  :args (list x))
            (list x)))

       ;; Otherwise, this is looking good.
       (new-assigns (vl-prophelp-split x.lvalue.args rhs-bits x.loc)))
    (mv warnings new-assigns))
  ///
  (defmvtypes vl-prophelp-assign (nil true-listp)))


(define vl-prophelp-assignlist
  ((x        vl-assignlist-p)
   (mod      vl-module-p)
   (ialist   (equal ialist (vl-moditem-alist mod)))
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p :hyp :fguard)
               (new-x vl-assignlist-p :hyp :fguard))
  :parents (propagate-help)
  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car) (vl-prophelp-assign (car x) mod ialist warnings))
       ((mv warnings cdr) (vl-prophelp-assignlist (cdr x) mod ialist warnings)))
    (mv warnings (append car cdr)))
  ///
  (defmvtypes vl-prophelp-assign (nil true-listp)))


(define vl-prophelp-module ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (propagate-help)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.assigns)
        ;; Optimization: don't even build the moditem alist unless there are
        ;; assignments.  We could do better here, i.e., check for an assignment
        ;; with a concatenation on the lhs, but this is probably good enough.
        x)
       (ialist (vl-moditem-alist x))
       ((mv warnings assigns)
        (vl-prophelp-assignlist x.assigns x ialist x.warnings)))
    (fast-alist-free ialist)
    (change-vl-module x
                      :assigns assigns
                      :warnings warnings))
  ///
  (defthm vl-module->name-of-vl-prophelp-module
    (equal (vl-module->name (vl-prophelp-module x))
           (vl-module->name x))))

(defprojection vl-prophelp-modulelist (x)
  (vl-prophelp-module x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(defthm vl-modulelist->names-of-vl-prophelp-modulelist
  (equal (vl-modulelist->names (vl-prophelp-modulelist x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))

