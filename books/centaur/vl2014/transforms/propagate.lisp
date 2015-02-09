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
(include-book "../mlib/subst")
(include-book "../mlib/allexprs")
(include-book "../mlib/modnamespace")
(include-book "../mlib/port-tools")
(local (include-book "../util/arithmetic"))

(defxdoc propagate
  :parents (transforms)
  :short "Eliminate assignments to simple \"intermediate\" wires. (UNSOUND)"

  :long "<p>This is a basic assignment-propagation simplification.  The idea is
to reduce modules that have lots of intermediate wires by just replacing the
wire with its expression.  For instance, a module that had assignments
like:</p>

@({
    assign a1 = ~a2;
    assign a2 = ~a3;
    assign a3 = ~a4;
    assign a4 = ~a5;
})

<p>Could presumably be propagated into:</p>

@({
    assign a1 = ~(~(~(~a5)));
})

<p>Which we could then reduce in other ways.</p>

<p>This transformation is <b>generally unsound</b>.  We aren't really doing any
checking to make sure that we are substituting into contexts with compatible
widths, etc.  We're also relying on the :DIR fields on module instance
arguments, which is probably not safe when ports are incorrectly marked as
inputs instead of outputs, etc.</p>

<p>Prerequisites: arguments need to be resolved so we can tell directions on
module/gate instance ports.</p>")

(local (xdoc::set-default-parents propagate))

(defaggregate propagate-limits
  :tag :propagate-limits
  :short "Limits on the assignments to consider."
  ((max-ops maybe-natp :rule-classes :type-prescription))
  :long "<p>We put this in an aggregate just to make it easy to extend.</p>")

(define propagate-expr-limits-okp ((x      vl-expr-p)
                                   (limits propagate-limits-p))
  :short "Check whether an expression is simple enough to propagate."
  :returns (okp booleanp :rule-classes :type-prescription)
  (b* (((propagate-limits limits) limits)
       ((unless limits.max-ops)
        t)
       (ops (vl-expr-ops x))
       (ops (set-difference-eq ops '(:vl-bitselect :vl-partselect-colon))))
    (< (len ops) limits.max-ops)))

(define candidates-for-propagation
  :short "Gather initial candidates for propagation."
  ((x      vl-assignlist-p)
   (limits propagate-limits-p))
  :returns (sigma vl-sigma-p :hyp (force (vl-assignlist-p x))
                  "Binds each identifier (lhs) to its replacement (rhs).")
  :long "<p>We're basically just looking for assignments like:</p>

@({
   assign identifier = expr;
})

<p>These are just initial candidates, and later we'll eliminate some of them
because propagation would be too hard.</p>"
  (b* (((when (atom x))
        nil)
       ((vl-assign x1) (car x))
       ((when (and (vl-idexpr-p x1.lvalue)
                   (propagate-expr-limits-okp x1.expr limits)))
        (cons (cons (vl-idexpr->name x1.lvalue) x1.expr)
              (candidates-for-propagation (cdr x) limits))))
    (candidates-for-propagation (cdr x) limits))
  ///
  (defthm alistp-of-candidates-for-propagation ;; BOZO why do we care?
    (alistp (candidates-for-propagation x limits))))

(define vl-maybe-driven-by-args
  :short "Approximately collects the names of wires that are driven by the
arguments to a gate/module instance. (unsound)"

  ((x vl-plainarglist-p))
  :returns (driven-names string-listp :hyp :fguard)

  :long "<p>This hopefully returns an overapproximation of the wires that might
possibly be driven by a gate/module instance with these arguments.  Note that
we only collect names here, so the entire wire is considered driven even if
only a single bit of it is driven, etc.</p>

<p>It is not sound if there are incorrectly labeled ports (e.g., if a submodule
drives its inputs, then we will not realize that the wires connected to that
input are driven.</p>"

  (b* (((mv ?in out inout unknown)
        (vl-partition-plainargs x nil nil nil nil))
       (out     (remove nil (vl-plainarglist->exprs out)))
       (inout   (remove nil (vl-plainarglist->exprs inout)))
       (unknown (remove nil (vl-plainarglist->exprs unknown))))
    (append (vl-exprlist-names out)
            (vl-exprlist-names inout)
            (vl-exprlist-names unknown))))

(define vl-maybe-driven-by-gateinst
  :short "Approximately the wires driven by a gate instance."
  ((x vl-gateinst-p))
  :returns (driven-names string-listp :hyp :fguard)
  :long "<p>This should be sound if @(see argresolve) treats gate instances
correctly.</p>"
  (vl-maybe-driven-by-args (vl-gateinst->args x)))

(defmapappend vl-maybe-driven-by-gateinsts (x)
  (vl-maybe-driven-by-gateinst x)
  :guard (vl-gateinstlist-p x))

(defthm string-listp-vl-maybe-driven-by-gateinsts
  (implies (vl-gateinstlist-p x)
           (string-listp (vl-maybe-driven-by-gateinsts x)))
  :hints(("Goal" :induct (len x))))


(define vl-maybe-driven-by-modinst
  :short "Approxpimately the wires driven by a module instance (unsound)."
  ((x vl-modinst-p))
  :returns (driven-names string-listp :hyp :fguard)
  (b* ((args (vl-modinst->portargs x))
       ((unless (eq (vl-arguments-kind args) :vl-arguments-plain))
        ;; Could make this more general by just returning all exprs in this
        ;; case...
        (raise "args still named???")))
    (vl-maybe-driven-by-args (vl-arguments-plain->args args))))

(defmapappend vl-maybe-driven-by-modinsts (x)
  (vl-maybe-driven-by-modinst x)
  :guard (vl-modinstlist-p x))

(defthm string-listp-vl-maybe-driven-by-modinsts
  (implies (vl-modinstlist-p x)
           (string-listp (vl-maybe-driven-by-modinsts x)))
  :hints(("Goal" :induct (len x))))


(define vl-driven-by-assign
  :short "Approximate the wires driven by an assignment."
  ((x vl-assign-p))
  :returns (drive-names string-listp :hyp :fguard)
  (vl-expr-names (vl-assign->lvalue x)))

(defmapappend vl-driven-by-assigns (x)
  (vl-driven-by-assign x)
  :guard (vl-assignlist-p x))

(defthm string-listp-vl-driven-by-assigns
  (implies (force (vl-assignlist-p x))
           (string-listp (vl-driven-by-assigns x)))
  :hints(("Goal" :induct (len x))))




(define used-in-some-select-p
  :parents (too-hard-to-propagate)
  ((x vl-module-p))
  :returns (names string-listp :hyp :fguard)
  (b* ((exprs   (vl-module-allexprs x))
       (selects (vl-exprlist-selects exprs))
       (names   (vl-exprlist-names selects)))
    names))


(define too-hard-to-propagate
  :short "Identify wires that are too hard to propagate."
  ((x vl-module-p))
  :returns (names string-listp :hyp :fguard)

  :long "<p>To keep propagation simple, we don't want to try to propagate an
assignment to a wire that is ever selected from.  The goal is to avoid having
to deal with things like this:</p>

@({
    assign foo = a + b;
    assign bar = foo[2] + 3;
})

<p>Naive propagation of foo would result in:</p>

@({
    assign bar = (a + b)[2] + 3;
})

<p>And we don't want to try to think about how to handle this.  Even if we just
had something like assign foo = bar, it'd be complicated because foo/bar could
have different ranges, e.g., if we have</p>

@({
    wire [3:0] foo;
    wire [4:1] bar;
    assign foo = bar;
    assign baz = foo[2] + 3;
})

<p>Then we would need to be careful to fix up the indicides when substituting
into baz, i.e., the correct substitution would be:</p>

@({
    assign baz = bar[3] + 3;
})

<p>And that's getting tricky.  So, the basic idea is: if the wire is ever
selected from anywhere, then just don't try to propagate it.</p>

<p>Also, for propagation to be safe, we need to make sure that we are not
propagating wires that have multiple drivers.  For instance, if we had:</p>

@({
    assign A = B;
    assign A = C;
})

<p>Then it wouldn't be safe to just go around replacing uses of A with either B
or C, because neither B nor C captures the whole value being assigned to A.
Hence, we need some code for detecting what wires are driven.</p>

<p>Another new restriction: we now allow ourselves to propagate into modules
that have always blocks, initial blocks, and function declarations.  But to
hopefully make this safe, we consider any names that are actually used in these
places to be unsafe.</p>"

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
      (used-in-some-select-p x)

      ;; Don't propagate any names used in functions, always blocks, initial blocks
      (vl-exprlist-names (vl-fundecllist-allexprs x.fundecls))
      (vl-exprlist-names (vl-alwayslist-allexprs x.alwayses))
      (vl-exprlist-names (vl-initiallist-allexprs x.initials))
      (vl-exprlist-names (vl-taskdecllist-allexprs x.taskdecls))
      (vl-exprlist-names (vl-paramdecllist-allexprs x.paramdecls))
      ;; (vl-exprlist-names (vl-vardecllist-allexprs x.vardecls))
      ;; (vl-vardecllist->names x.vardecls)
      (vl-taskdecllist->names x.taskdecls)
      (vl-paramdecllist->names x.paramdecls)
      ))))


(define remove-each-from-alist (keys alist)
  :parents (propagation-sigma)
  :short "BOZO, terrible, inefficient."
  (declare (xargs :guard (alistp alist)))
  (if (atom keys)
      alist
    (remove-each-from-alist (cdr keys)
                            (remove-from-alist (car keys) alist)))
  ///
  (defthm vl-sigma-p-of-remove-from-alist
    (implies (vl-sigma-p alist)
             (vl-sigma-p (remove-from-alist key alist)))
    :hints(("Goal" :in-theory (enable remove-from-alist))))

  (defthm vl-sigma-p-of-remove-each-from-alist
    (implies (vl-sigma-p alist)
             (vl-sigma-p (remove-each-from-alist keys alist))))

  (defthm alistp-of-remove-each-from-alist
    (implies (alistp alist)
             (alistp (remove-each-from-alist keys alist)))))


(define propagation-sigma
  :short "Determine what wires to use for one round of propagation."
  ((x      vl-module-p)
   (limits propagate-limits-p))
  :returns (sigma vl-sigma-p :hyp (force (vl-module-p x)))
  (b* (((vl-module x) x)
       (candidates (candidates-for-propagation x.assigns limits))
       ;; (- (cw "  - Initial candidates: ~&0~%" (mergesort (alist-keys candidates))))
       (too-hard   (too-hard-to-propagate x))
       ;; (- (cw "  - Too hard: ~&0~%" (mergesort too-hard)))
       (candidates (remove-each-from-alist too-hard candidates))
       ;; Now, we restrict ourselves to only using candidates that aren't used
       ;; by the expressions in other candidates.  The idea is if we have:
       ;;
       ;;      assign a = ~b;
       ;;      assign b = ~c;
       ;;      assign c = ~d;
       ;;      myinst foo (..., a, b, c, ...);
       ;;
       ;; Then initially we only want to propagate A.  After A has been
       ;; propagated and removed from the module, we can come back in another
       ;; round and propagate B.  Without this restriction, blindly
       ;; substituting the three assignments would give us:
       ;;
       ;;      myinst foo(..., ~b, ~c, ~d, ...);
       ;;
       ;; And this is terrible because we are going to also eliminate B and C
       ;; from the module, which means that FOO now has bad expressions that
       ;; aren't even driven.
       (must-wait (mergesort (vl-exprlist-names (alist-vals candidates))))
       ;; (- (cw "  - Used by other candidates: ~&0~%" must-wait))
       (candidates (remove-each-from-alist must-wait candidates))
       (- (cw "  - Final candidates: ~&0~%" (mergesort (alist-keys candidates)))))
      candidates))


(define remove-simple-assigns-to
  :short "Remove all assignments to these wires (we do this after we've
          propagated the assignments."
  ((names   string-listp)
   (assigns vl-assignlist-p))
  :returns (new-assigns vl-assignlist-p :hyp :fguard)
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

(define vl-propagation-round
  :short "One single round of propagation."
  ((x      vl-module-p)
   (limits propagate-limits-p))
  :returns (new-x vl-module-p :hyp (force (vl-module-p x)))

  (b* ((- (cw "Starting propagation round for ~s0~%" (vl-module->name x)))
       (sigma (propagation-sigma x limits))
       ((unless sigma)
        ;; Nothing to do.
        x)
       ((with-fast sigma))
       (propagate-names (alist-keys sigma))
       (temp-assigns    (remove-simple-assigns-to propagate-names
                                                  (vl-module->assigns x)))
       (temp-mod        (change-vl-module x :assigns temp-assigns)))
    (vl-module-subst temp-mod sigma))

  :prepwork ((local (defthm l0
                      (implies (vl-sigma-p x)
                               (string-listp (alist-keys x)))
                      :hints(("Goal" :induct (len x)))))))

(define vl-propagation-fixpoint ((x      vl-module-p)
                                 (n      natp)
                                 (limits propagate-limits-p))
  :returns (new-x vl-module-p :hyp (force (vl-module-p x)))
  :measure (nfix n)
  (b* (((when (zp n))
        (cw "Note: ran out of steps in vl-propagation-fixpoint for ~s0.~%"
            (vl-module->name x))
        x)
       (new-x (vl-propagation-round x limits))
       ((when (equal new-x x))
        x))
    (vl-propagation-fixpoint new-x (- n 1) limits)))

(define vl-module-propagate
  :short "Repeatedly propagate assignments in a module."
  ((x      vl-module-p)
   (limits propagate-limits-p))
  :returns (new-x vl-module-p)
  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       ;; We no longer prohibit this.  Instead we try to prevent it from
       ;; causing problems by making sure we don't propagate anything that's
       ;; used in these areas.
       ;; ((when (or x.alwayses
       ;;            x.fundecls
       ;;            x.vardecls
       ;;            x.paramdecls
       ;;            x.taskdecls
       ;;            ))
       ;;  (cw "Note: not propagating in ~s0; module looks too complicated.~%" x.name)
       ;;  x))
       )
    (vl-propagation-fixpoint x 1000 limits)))

(defprojection vl-modulelist-propagate (x limits)
  :returns (new-x vl-modulelist-p)
  (vl-module-propagate x limits)
  :guard (and (vl-modulelist-p x)
              (propagate-limits-p limits)))

(define vl-design-propagate ((x vl-design-p)
                             (limits propagate-limits-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-propagate x.mods limits))))

