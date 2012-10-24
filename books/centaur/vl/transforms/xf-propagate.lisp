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
(include-book "xf-subst")
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))

(defxdoc propagate
  :parents (transforms)
  :short "Eliminate assignments to simple \"intermediate\" wires. (UNSOUND)"

  :long "<p>This is a basic assignment-propagation simplification.  The idea is
to reduce modules that have lots of intermediate wires by just replacing the
wire with its expression.  For instance, a module that had assignments
like:</p>

<code>
    assign a1 = ~a2;
    assign a2 = ~a3;
    assign a3 = ~a4;
    assign a4 = ~a5;
</code>

<p>Could presumably be propagated into:</p>

<code>
    assign a1 = ~(~(~(~a5)));
</code>

<p>Which we could then reduce in other ways.</p>

<p>This transformation is <b>generally unsound</b>.  We aren't really doing any
checking to make sure that we are substituting into contexts with compatible
widths, etc.  We're also relying on the :DIR fields on module instance
arguments, which is probably not safe when ports are incorrectly marked as
inputs instead of outputs, etc.</p>

<p>Prerequisites: arguments need to be resolved so we can tell directions on
module/gate instance ports.</p>")



(defaggregate propagate-limits
  (max-ops)
  :tag :propagate-limits
  :require ((vl-maybe-natp-of-propagate-limits->max-ops
             (vl-maybe-natp max-ops)
             :rule-classes :type-prescription))
  :parents (propagate)
  :short "Limits on the assignments to consider."
  :long "<p>We put this in an aggregate just to make it easy to extend.</p>")


(defund propagate-expr-limits-okp (x limits)
  (declare (xargs :guard (and (vl-expr-p x)
                              (propagate-limits-p limits))))
  (b* (((propagate-limits limits) limits)
       ((unless limits.max-ops)
        t)
       (ops (vl-expr-ops x))
       (ops (set-difference-eq ops '(:vl-bitselect :vl-partselect-colon))))
    (< (len ops) limits.max-ops)))


(defsection candidates-for-propagation
  :parents (propagate)
  :short "Gather initial candidates for propagation."

  :long "<p>@(call candidates-for-propagation) walks over a @(see
vl-assignlist-p), looking for assignments that are simple enough to consider
eliminating.  We're basically just looking for assignments like:</p>

<code>
   assign identifier = expr;
</code>

<p>These are just initial candidates, and we'll eliminate some of them because
propagation would be too hard.  We return a @(see vl-sigma-p) that binds each
identifiers to its replacement (i.e., the rhs).</p>"

  (defund candidates-for-propagation (x limits)
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (propagate-limits-p limits))))
    (b* (((when (atom x))
          nil)
         ((vl-assign x1) (car x))
         ((when (and (vl-idexpr-p x1.lvalue)
                     (propagate-expr-limits-okp x1.expr limits)))
          (cons (cons (vl-idexpr->name x1.lvalue) x1.expr)
                (candidates-for-propagation (cdr x) limits))))
      (candidates-for-propagation (cdr x) limits)))

  (local (in-theory (enable candidates-for-propagation)))

  (defthm alistp-of-candidates-for-propagation
    (alistp (candidates-for-propagation x limits)))

  (defthm vl-sigma-p-of-candidates-for-propagation
    (implies (force (vl-assignlist-p x))
             (vl-sigma-p (candidates-for-propagation x limits)))))




(defsection vl-maybe-driven-by-args
  :parents (propagate)
  :short "Approximately collects the names of wires that are driven by the
arguments to a gate/module instance. (unsound)"

  :long "<p>This hopefully returns an overapproximation of the wires that might
possibly be driven by a gate/module instance with these arguments.  Note that
we only collect names here, so the entire wire is considered driven even if
only a single bit of it is driven, etc.</p>

<p>It is not sound if there are incorrectly labeled ports (e.g., if a submodule
drives its inputs, then we will not realize that the wires connected to that
input are driven.</p>"

  (defund vl-maybe-driven-by-args (x)
    (declare (xargs :guard (vl-plainarglist-p x)))
    (b* (((mv ?in out inout unknown)
          (vl-partition-plainargs x nil nil nil nil))
         (out     (remove nil (vl-plainarglist->exprs out)))
         (inout   (remove nil (vl-plainarglist->exprs inout)))
         (unknown (remove nil (vl-plainarglist->exprs unknown))))
      (append (vl-exprlist-names out)
              (vl-exprlist-names inout)
              (vl-exprlist-names unknown))))

  (local (in-theory (enable vl-maybe-driven-by-args)))

  (defthm string-listp-of-vl-maybe-driven-by-args
    (implies (force (vl-plainarglist-p x))
             (string-listp (vl-maybe-driven-by-args x)))))


(defsection vl-maybe-driven-by-gateinst
  :parents (propagate)
  :short "Approximately the wires driven by a gate instance."
  :long "<p>This should be sound if @(see argresolve) treats gate instances
correctly.</p>"

  (defund vl-maybe-driven-by-gateinst (x)
    (declare (xargs :guard (vl-gateinst-p x)))
    (vl-maybe-driven-by-args (vl-gateinst->args x)))

  (local (in-theory (enable vl-maybe-driven-by-gateinst)))

  (defthm string-listp-vl-maybe-driven-by-gateinst
    (implies (vl-gateinst-p x)
             (string-listp (vl-maybe-driven-by-gateinst x)))))


(defmapappend vl-maybe-driven-by-gateinsts (x)
  (vl-maybe-driven-by-gateinst x)
  :guard (vl-gateinstlist-p x)
  :parents (propagate))

(defthm string-listp-vl-maybe-driven-by-gateinsts
  (implies (vl-gateinstlist-p x)
           (string-listp (vl-maybe-driven-by-gateinsts x)))
  :hints(("Goal" :induct (len x))))


(defsection vl-maybe-driven-by-modinsts
  :parents (propagate)
  :short "Approxpimately the wires driven by a module instance (unsound)."

  (defund vl-maybe-driven-by-modinst (x)
    (declare (xargs :guard (vl-modinst-p x)))
    (b* ((args (vl-modinst->portargs x))
         ((when (vl-arguments->namedp args))
          ;; Could make this more general by just returning all exprs
          ;; in this case...
          (er hard? 'vl-maybe-driven-by-modinst "args still named???")))
      (vl-maybe-driven-by-args (vl-arguments->args args))))

  (local (in-theory (enable vl-maybe-driven-by-modinst)))

  (defthm string-listp-vl-maybe-driven-by-modinst
    (implies (vl-modinst-p x)
             (string-listp (vl-maybe-driven-by-modinst x)))))


(defmapappend vl-maybe-driven-by-modinsts (x)
  (vl-maybe-driven-by-modinst x)
  :guard (vl-modinstlist-p x)
  :parents (propagate))

(defthm string-listp-vl-maybe-driven-by-modinsts
  (implies (vl-modinstlist-p x)
           (string-listp (vl-maybe-driven-by-modinsts x)))
  :hints(("Goal" :induct (len x))))


(defsection vl-driven-by-assign
  :parents (propagate)
  :short "Approximate the wires driven by an assignment."

  (defund vl-driven-by-assign (x)
    (declare (xargs :guard (vl-assign-p x)))
    (vl-expr-names (vl-assign->lvalue x))))


(defmapappend vl-driven-by-assigns (x)
  (vl-driven-by-assign x)
  :guard (vl-assignlist-p x)
  :parents (propagate))


(defsection too-hard-to-propagate
  :parents (propagate)
  :short "Identify wires that are too hard to propagate."

  :long "<p>To keep propagation simple, we don't want to try to propagate an
assignment to a wire that is ever selected from.  The goal is to avoid having
to deal with things like this:</p>

<code>
    assign foo = a + b;
    assign bar = foo[2] + 3;
</code>

<p>Naive propagation of foo would result in:</p>

<code>
    assign bar = (a + b)[2] + 3;
</code>

<p>And we don't want to try to think about how to handle this.  Even if we just
had something like assign foo = bar, it'd be complicated because foo/bar could
have different ranges, e.g., if we have</p>

<code>
    wire [3:0] foo;
    wire [4:1] bar;
    assign foo = bar;
    assign baz = foo[2] + 3;
</code>

<p>Then we would need to be careful to fix up the indicides when substituting
into baz, i.e., the correct substitution would be:</p>

<code>
    assign baz = bar[3] + 3;
</code>

<p>And that's getting tricky.  So, the basic idea is: if the wire is ever
selected from anywhere, then just don't try to propagate it.</p>

<p>Also, for propagation to be safe, we need to make sure that we are not
propagating wires that have multiple drivers.  For instance, if we had:</p>

<code>
    assign A = B;
    assign A = C;
</code>

<p>Then it wouldn't be safe to just go around replacing uses of A with either B
or C, because neither B nor C captures the whole value being assigned to A.
Hence, we need some code for detecting what wires are driven.</p>"

  (defund used-in-some-select-p (x)
    (declare (Xargs :guard (vl-module-p x)))
    (b* ((exprs   (vl-module-allexprs x))
         (selects (vl-exprlist-selects exprs))
         (names   (vl-exprlist-names selects)))
      names))

  (defund too-hard-to-propagate (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x))
      (mergesort
       (append
        ;; Can't propagate any ports (we need to keep driving them!)
        (vl-portdecllist->names x.portdecls)
        ;; Don't propagate when there are multiple drivers, as discussed above.
        (vl-maybe-driven-by-modinsts x.modinsts)
        (vl-maybe-driven-by-gateinsts x.gateinsts)
        (duplicated-members (vl-driven-by-assigns x.assigns))
        ;; Don't propagate wires used in selects, as discussed above.
        (used-in-some-select-p x))))))



(defsection propagation-sigma
  :parents (propagate)
  :short "Determine what wires to use for one round of propagation."

  (defund remove-each-from-alist (keys alist)
    ;; BOZO, terribly inefficient
    (declare (xargs :guard (alistp alist)))
    (if (atom keys)
        alist
      (remove-each-from-alist (cdr keys)
                              (remove-from-alist (car keys) alist))))

  (local (defthm vl-sigma-p-of-remove-from-alist
           (implies (vl-sigma-p alist)
                    (vl-sigma-p (remove-from-alist key alist)))
           :hints(("Goal" :in-theory (enable remove-from-alist)))))

  (local (defthm vl-sigma-p-of-remove-each-from-alist
           (implies (vl-sigma-p alist)
                    (vl-sigma-p (remove-each-from-alist keys alist)))
           :hints(("Goal" :in-theory (enable remove-each-from-alist)))))

  (local (defthm alistp-of-remove-each-from-alist
           (implies (alistp alist)
                    (alistp (remove-each-from-alist keys alist)))
           :hints(("Goal" :in-theory (enable remove-each-from-alist)))))

  (defund propagation-sigma (x limits)
    (declare (xargs :guard (and (vl-module-p x)
                                (propagate-limits-p limits))))
    (b* (((vl-module x) x)
         (candidates (candidates-for-propagation x.assigns limits))
;         (- (cw "  - Initial candidates: ~&0~%" (mergesort (alist-keys candidates))))
         (too-hard   (too-hard-to-propagate x))
;         (- (cw "  - Too hard: ~&0~%" (mergesort too-hard)))
         (candidates (remove-each-from-alist too-hard candidates))

; Now, we restrict ourselves to only using candidates that aren't used by the
; expressions in other candidates.  The idea is if we have:
;
;      assign a = ~b;
;      assign b = ~c;
;      assign c = ~d;
;      myinst foo (..., a, b, c, ...);
;
; Then initially we only want to propagate A.  After A has been propagated and
; removed from the module, we can come back in another round and propagate B.
; Without this restriction, blindly substituting the three assignments would
; give us:
;
;      myinst foo(..., ~b, ~c, ~d, ...);
;
; And this is terrible because we are going to also eliminate B and C from the
; module, which means that FOO now has bad expressions that aren't even driven.

         (must-wait (mergesort (vl-exprlist-names (alist-vals candidates))))
;         (- (cw "  - Used by other candidates: ~&0~%" must-wait))
         (candidates (remove-each-from-alist must-wait candidates))
         (- (cw "  - Final candidates: ~&0~%" (mergesort (alist-keys candidates)))))
      candidates))

  (defthm vl-sigma-p-of-propagation-sigma
    (implies (force (vl-module-p x))
             (vl-sigma-p (propagation-sigma x limits)))
    :hints(("Goal" :in-theory (enable propagation-sigma)))))



(defsection vl-propagation-round
  :parents (propagate)
  :short "One single round of propagation."

  (defund remove-simple-assigns-to (names assigns)
    ;; After we've propagated the names, we need to remove the assignments to them.
    (declare (xargs :guard (and (string-listp names)
                                (vl-assignlist-p assigns))))
    (b* (((when (atom assigns))
          nil)
         (x1 (car assigns))
         ((vl-assign x1) x1)
         ((when (and (vl-idexpr-p x1.lvalue)
                     (member-equal (vl-idexpr->name x1.lvalue) names)))
          ;; Assignment to one of these names, so drop it.
          (remove-simple-assigns-to names (cdr assigns))))
      (cons (car assigns)
            (remove-simple-assigns-to names (cdr assigns)))))

  (defthm vl-assignlist-p-of-remove-simple-assigns-to
    (implies (and (force (string-listp names))
                  (force (vl-assignlist-p assigns)))
             (vl-assignlist-p (remove-simple-assigns-to names assigns)))
    :hints(("Goal" :in-theory (enable remove-simple-assigns-to))))

  (local (defthm l0
           (implies (vl-sigma-p x)
                    (string-listp (alist-keys x)))
           :hints(("Goal" :induct (len x)))))

  (defund vl-propagation-round (x limits)
    (declare (xargs :guard (and (vl-module-p x)
                                (propagate-limits-p limits))))
    (b* ((- (cw "Starting propagation round for ~s0~%" (vl-module->name x)))
         (sigma (propagation-sigma x limits))
         ((unless sigma)
          ;; Nothing to do.
          x)
         ((with-fast sigma))
         (propagate-names (alist-keys sigma))
         (temp-assigns    (remove-simple-assigns-to propagate-names (vl-module->assigns x)))
         (temp-mod        (change-vl-module x :assigns temp-assigns)))
      (vl-module-subst temp-mod sigma)))

  (local (in-theory (enable vl-propagation-round)))

  (defthm vl-module-p-of-vl-propagation-round
    (implies (force (vl-module-p x))
             (vl-module-p (vl-propagation-round x limits))))

  (defthm vl-module->name-of-vl-propagation-round
    (equal (vl-module->name (vl-propagation-round x limits))
           (vl-module->name x))))



(defsection vl-module-propagate
  :parents (propagate)
  :short "Repeatedly propagate assignments in a module."

  (defund vl-propagation-fixpoint (x n limits)
    (declare (xargs :guard (and (vl-module-p x)
                                (natp n)
                                (propagate-limits-p limits))
                    :measure (nfix n)))
    (b* (((when (zp n))
          (cw "Note: ran out of steps in vl-propagation-fixpoint for ~s0.~%"
              (vl-module->name x))
          x)
         (new-x (vl-propagation-round x limits))
         ((when (equal new-x x))
          x))
      (vl-propagation-fixpoint new-x (- n 1) limits)))

  (local (in-theory (enable vl-propagation-fixpoint)))

  (local (defthm l0
           (implies (force (vl-module-p x))
                    (vl-module-p (vl-propagation-fixpoint x n limits)))))

  (local (defthm l1
           (equal (vl-module->name (vl-propagation-fixpoint x n limits))
                  (vl-module->name x))))

  (defund vl-module-propagate (x limits)
    (declare (xargs :guard (and (vl-module-p x)
                                (propagate-limits-p limits))))
    (b* (((vl-module x) x)
         ((when (or x.alwayses
                    x.paramdecls
                    x.fundecls
                    x.taskdecls
                    x.eventdecls
                    x.regdecls
                    x.vardecls))
          (cw "Note: not propagating in ~s0; module looks too complicated.~%" x.name)
          x))
      (vl-propagation-fixpoint x 1000 limits)))

  (local (in-theory (enable vl-module-propagate)))

  (defthm vl-module-p-of-vl-module-propagate
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-propagate x limits))))

  (defthm vl-module->name-of-vl-module-propagate
    (equal (vl-module->name (vl-module-propagate x limits))
           (vl-module->name x))))


(defprojection vl-modulelist-propagate (x limits)
  (vl-module-propagate x limits)
  :guard (and (vl-modulelist-p x)
              (propagate-limits-p limits))
  :result-type vl-modulelist-p
  :parents (propagate))

(defthm vl-modulelist->names-of-vl-modulelist-propagate
  (equal (vl-modulelist->names (vl-modulelist-propagate x limits))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))
