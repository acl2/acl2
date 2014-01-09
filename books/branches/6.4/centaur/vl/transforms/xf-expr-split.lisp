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
(include-book "../mlib/expr-slice")
(include-book "../mlib/range-tools")
(include-book "../mlib/context")
(include-book "../mlib/delta")
(local (include-book "../util/arithmetic"))


(defxdoc split
  :parents (transforms)
  :short "Split up expressions by generating new wires."

  :long "<p>The basic idea of this transformation is to introduce temporary
variables for sub-expressions, e.g., we might split up:</p>

@({
    assign w = a + b * c + d;
})

<p>into a series of simpler assignments, e.g.,</p>

@({
    assign t1 = b * c;
    assign t2 = a + t1;
    assign w = t2 + d;
})

<p>Almost true: we split up expressions until they involve either 0 or 1
operations.  The twist is that we don't split up expressions that consist of
\"mere wiring\", e.g., concatenation and bit- or part-selects.  More precisely,
we don't split up expressions that are already atomic or <i>sliceable</i>; see
@(see expr-slicing).</p>

<p>Splitting up expressions involves creating new wire declarations and
assignments to those wires.  Sometimes the new modules are much bigger than the
old modules.  We have seen cases where tens of thousands of new wires are
introduced.  In fact, this transform was one of our initial motivations for
<see topic='@(url vl-namefactory-p)'>name factories</see>.</p>

<p><b>Context.</b> I usually think of expression splitting as a kind of
preprocessing step that leads toward @(see occform); occform replaces simple
assignments (e.g., like those to the temporary wires above) with module
instances, but can't deal with complex expressions.</p>

<p><b>Prerequisites.</b> We expect that @(see argresolve) has been run and that
@(see expression-sizing) has already been done.  Unsized expressions or named
arguments will generally lead to fatal @(see warnings) being added to the
module.</p>

<p><b>Soundness Concerns.</b> If submodule ports are mislabeled, we might end
up splitting up an input to a module instance that has backflow.  That is, we
could do somethign like this:</p>

@({
  submod foo ( ..., .i(a + b), ...);
    --->
  wire[3:0] tmp = a + b;
  submod foo ( ..., .i(tmp), ...);
})

<p>And if @('foo') drives @('i'), then we might end up with @('tmp') being X
sometimes.  Worse would be if the expression was somethign like @('a ? b :
1'bz'), in which case the submodule could actually end up putting out a value
onto @('tmp').</p>

<p>I don't really think this is a problem.  I think we're saved because, since
a new, fresh temporary wire is going to be used, whether or not that temporary
is driven from both sides isn't really relevant.  It can't be used anywhere
else in the module or affect anything except for exactly this port.</p>")

(define vl-nosplit-p ((x vl-expr-p))
  :parents (split)
  :short "Recognize an expression that is may as well be atomic for the
purposes of @(see split)."
  :long "<p>This is almost just @(see vl-expr-sliceable-p), except that there
are some atomic expressions (e.g., real numbers, strings, etc.) that aren't
sliceable, but that we still don't want to split up.</p>"
  :inline t
  :enabled t
  (if (vl-fast-atom-p x)
      t
    (vl-expr-sliceable-p x)))

(deflist vl-nosplitlist-p (x)
  (vl-nosplit-p x)
  :guard (vl-exprlist-p x)
  :elementp-of-nil nil
  :parents (split))

(defsection vl-expr-split
  :parents (split)
  :short "Split up complex subexpressions throughout an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-split) returns @('(mv x'
delta')').</p>

<ul>

<li>@('x') is an expression to split, which we recur through.</li>

<li>@('elem') is a @(see vl-modelement-p) that says where this expression
occurs.  It is used for better error messages and for the locations of newly
generated wires/assignments, but is otherwise not meaningful.</li>

<li>@('delta') is a @(see vl-delta-p) that gathers up the additions we are
going to make.</li>

</ul>

<p>We return a new, expression @('x'') that is a replacement for @('x').  If
@('x') was already sliceable we just return it unchanged.  Otherwise @('x'')
will be the name of a newly generated, equivalent wire.</p>"

  (defconst *vl-tmp-wire-atts* (list (list (hons-copy "VL_TMP_WIRE"))))

  (mutual-recursion

   (defund vl-expr-split (x elem delta)
     "Returns (mv x' delta')"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-modelement-p elem)
                                 (vl-delta-p delta))
                     :verify-guards nil
                     :measure (vl-expr-count x)))

     (b* ((width (vl-expr->finalwidth x))
          (type  (vl-expr->finaltype x))

          ((unless (and (posp width) type))
           ;; Basic sanity check.  Widths should be computed and positive, or
           ;; what are we even doing??
           (mv x (dwarn :type :vl-programming-error
                        :msg "~a0: expected widths/types to be determined, ~
                              but expression ~a1 has width ~x2 and type ~x3."
                        :args (list elem x width type)
                        :fatalp t
                        :fn 'vl-expr-split)))

          ((when (vl-nosplit-p x))
           ;; X isn't anything we need to split, nothing to do.
           (mv x delta))

          ;; Otherwise, X contains at least some unsliceable components.
          ;; First, lets recursively split the arguments.  Note that each of
          ;; the new-args will be either atoms or sliceable expressions.
          ((mv new-args delta)
           (vl-exprlist-split (vl-nonatom->args x) elem delta))

          ((vl-delta delta) delta)

          ;; Now, our operation applied to the simplified args is a simple
          ;; expression.  We create a new, temporary wire of the appropriate
          ;; width, and assign the expression to this new wire.
          ((mv tmp-name nf) (vl-namefactory-indexed-name "temp" delta.nf))
          (rhs-expr   (change-vl-nonatom x :args new-args))
          (tmp-expr   (vl-idexpr tmp-name width type))
          (tmp-decl   (make-vl-netdecl :loc     (vl-modelement-loc elem)
                                       :name    tmp-name
                                       :type    :vl-wire
                                       :signedp (eq type :vl-signed)
                                       :range   (vl-make-n-bit-range width)
                                       :atts    *vl-tmp-wire-atts*))
          (tmp-assign (make-vl-assign :loc (vl-modelement-loc elem)
                                      :lvalue tmp-expr
                                      :expr rhs-expr))
          (delta      (change-vl-delta delta
                                       :nf nf
                                       :netdecls (cons tmp-decl delta.netdecls)
                                       :assigns  (cons tmp-assign delta.assigns))))
       (mv tmp-expr delta)))

   (defund vl-exprlist-split (x elem delta)
     "Returns (mv x' delta')"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-modelement-p elem)
                                 (vl-delta-p delta))
                     :measure (vl-exprlist-count x)))
     (b* (((when (atom x))
           (mv nil delta))
          ((mv car-prime delta)
           (vl-expr-split (car x) elem delta))
          ((mv cdr-prime delta)
           (vl-exprlist-split (cdr x) elem delta))
          (x-prime (cons car-prime cdr-prime)))
       (mv x-prime delta))))

  (flag::make-flag flag-vl-expr-split
                   vl-expr-split
                   :flag-mapping ((vl-expr-split . expr)
                                  (vl-exprlist-split . list)))

  (defthm-flag-vl-expr-split
    (expr t :skip t)
    (defthm len-of-vl-exprlist-split
      (equal (len (mv-nth 0 (vl-exprlist-split x elem delta)))
             (len x))
      :flag list)
    :hints(("Goal" :expand (vl-exprlist-split x elem delta))))

  (defthm-flag-vl-expr-split
    (expr t :skip t)
    (defthm true-listp-of-vl-exprlist-split
      (true-listp (mv-nth 0 (vl-exprlist-split x elem delta)))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal" :expand (vl-exprlist-split x elem delta))))

  (defthm-flag-vl-expr-split

    (defthm vl-expr-split-basics
      (implies (and (force (vl-expr-p x))
                    (force (vl-modelement-p elem))
                    (force (vl-delta-p delta)))
               (b* (((mv x-prime delta)
                     (vl-expr-split x elem delta)))
                 (and (vl-expr-p x-prime)
                      (vl-delta-p delta))))
      :flag expr)

    (defthm vl-exprlist-split-basics
      (implies (and (force (vl-exprlist-p x))
                    (force (vl-modelement-p elem))
                    (force (vl-delta-p delta)))
               (b* (((mv x-prime delta)
                     (vl-exprlist-split x elem delta)))
                 (and (vl-exprlist-p x-prime)
                      (vl-delta-p delta))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-expr-split x elem delta)
                     (vl-exprlist-split x elem delta)))))

  (verify-guards vl-expr-split))


(define vl-assign-split ((x vl-assign-p)
                         (delta vl-delta-p))
  :returns (mv (new-x vl-assign-p :hyp :fguard)
               (delta vl-delta-p :hyp :fguard))
  :parents (split)
  :short "Split up assignments with complex right-hand sides."

  :long "<p>This is a little more interesting than usual.  We want to split up
the right-hand side of an assignment only if it is a compound expression that
involves unsliceable arguments.  That is, we don't want to split up assignments
like:</p>

<ul>
<li> @('foo = bar') -- no operations </li>
<li> @('foo = bar[3]') -- no \"non-wiring\" operations </li>
<li> @('foo = bar + 1') -- just one operation </li>
<li> @('foo = bar[3] & foo[4]') -- just one \"non-wiring\" operation</li>
</ul>

<p>But we do want to split up anything more complicated, for instance, if we
have:</p>

@({
  foo = bar + (baz + 1)
})

<p>Then we want to split, because we have a top-level operator who has an
argument, @('(baz + 1)'), that isn't sliceable.</p>"

  (b* (((vl-assign x) x)

       ((when (vl-nosplit-p x.expr))
        ;; Don't split things if they are already atomic/wiring.
        (mv x delta))

       (args (vl-nonatom->args x.expr))

       ((when (vl-nosplitlist-p args))
        ;; Don't split up a single operator applied to atomic/wiring stuff.
        (mv x delta))

       ;; Even at this point, we don't want to apply splitting to the whole
       ;; expression.  Instead, just recursively simplify the args until they
       ;; are atomic, and build a new expr out of them.
       ((mv new-args delta) (vl-exprlist-split args x delta))
       (new-expr            (change-vl-nonatom x.expr :args new-args))
       (x-prime             (change-vl-assign x :expr new-expr)))
    (mv x-prime delta)))

(define vl-assignlist-split ((x vl-assignlist-p)
                             (delta vl-delta-p))
  :returns (mv (new-x vl-assignlist-p :hyp :fguard)
               (delta vl-delta-p :hyp :fguard))
  :parents (split)
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-assign-split (car x) delta))
       ((mv cdr delta) (vl-assignlist-split (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-plainarg-split ((x vl-plainarg-p)
                           (elem vl-modelement-p)
                           (delta vl-delta-p))
  :returns (mv (new-x vl-plainarg-p :hyp :fguard)
               (delta vl-delta-p    :hyp :fguard))
  :parents (split)
  :short "Maybe split up an argument to a gate/module instances."

  :long "<p>We only want to split up expressions that are being given as inputs
to submodules.  If we have an output, we really want to hook up the actual
wires being connected, not some new internal wire that we've just created.</p>

<p>This is much like how, when we split up assignments, we only split up the
right-hand sides.  That is, the left-hand side of an assignment is similar to a
module output.  We generally think it's an error for a module output to be
connected to some non-sliceable expression like @('a + b').</p>

<p>I'm less sure what to do about inouts.  For now I'm going to not split them
up.</p>"

  (b* (((vl-plainarg x) x)
       ((unless (eq x.dir :vl-input))
        ;; Don't want to split it
        (mv x delta))

       ((unless x.expr)
        ;; Found a blank port.  Nothing to do.
        (mv x delta))

       ((when (vl-nosplit-p x.expr))
        ;; Historically we just split these up, too.  But we no longer want
        ;; to introduce temporary wires just for wiring-related expressions
        ;; like bit-selects, etc.  So, don't split this up.
        (mv x delta))

       ((mv new-expr delta) (vl-expr-split x.expr elem delta))
       (x-prime             (change-vl-plainarg x :expr new-expr)))
    (mv x-prime delta)))

(define vl-plainarglist-split ((x vl-plainarglist-p)
                               (elem vl-modelement-p)
                               (delta vl-delta-p))
  :returns (mv (new-x vl-plainarglist-p :hyp :fguard)
               (delta vl-delta-p        :hyp :fguard))
  :parents (split)
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-plainarg-split (car x) elem delta))
       ((mv cdr delta) (vl-plainarglist-split (cdr x) elem delta)))
    (mv (cons car cdr) delta)))

(define vl-arguments-split ((x vl-arguments-p)
                            (elem vl-modelement-p)
                            (delta vl-delta-p))
  :returns (mv (new-x vl-arguments-p :hyp :fguard)
               (delta vl-delta-p     :hyp :fguard))
  :parents (split)
  (b* (((vl-arguments x) x)
       ((when x.namedp)
        (mv x (dwarn :type :vl-bad-arguments
                     :msg "~a0: expected to only encounter plain arguments, ~
                           but found a named argument list.  Not actually ~
                           splitting anything."
                     :args (list elem)
                     :fatalp t
                     :fn 'vl-arguments-split)))
       ((mv new-args delta)
        (vl-plainarglist-split x.args elem delta))
       (x-prime (vl-arguments nil new-args)))
    (mv x-prime delta)))

(define vl-modinst-split ((x vl-modinst-p)
                          (delta vl-delta-p))
  :returns (mv (new-x vl-modinst-p :hyp :fguard)
               (delta vl-delta-p   :hyp :fguard))
  :parents (split)
  (b* (((vl-modinst x) x)
       ((mv new-args delta) (vl-arguments-split x.portargs x delta))
       (x-prime             (change-vl-modinst x :portargs new-args)))
    (mv x-prime delta)))

(define vl-modinstlist-split ((x vl-modinstlist-p)
                              (delta vl-delta-p))
  :returns (mv (new-x vl-modinstlist-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  :parents (split)
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-modinst-split (car x) delta))
       ((mv cdr delta) (vl-modinstlist-split (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-gateinst-split ((x vl-gateinst-p)
                           (delta vl-delta-p))
  :returns (mv (new-x vl-gateinst-p :hyp :fguard)
               (delta vl-delta-p    :hyp :fguard))
  :parents (split)
  (b* (((vl-gateinst x) x)
       ((mv new-args delta) (vl-plainarglist-split x.args x delta))
       (x-prime             (change-vl-gateinst x :args new-args)))
    (mv x-prime delta)))

(define vl-gateinstlist-split ((x vl-gateinstlist-p)
                               (delta vl-delta-p))
  :returns (mv (new-x vl-gateinstlist-p :hyp :fguard)
               (delta vl-delta-p        :hyp :fguard))
  :parents (split)
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-gateinst-split (car x) delta))
       ((mv cdr delta) (vl-gateinstlist-split (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-module-split ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (split)
  :short "Split up complex expressions throughout a module's assignments,
module instances, and gate instances."

  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       (delta                (vl-starting-delta x))
       (delta                (change-vl-delta delta :netdecls x.netdecls))
       ((mv assigns delta)   (vl-assignlist-split x.assigns delta))
       ((mv modinsts delta)  (vl-modinstlist-split x.modinsts delta))
       ((mv gateinsts delta) (vl-gateinstlist-split x.gateinsts delta))
       ((vl-delta delta)     (vl-free-delta delta)))

    (change-vl-module
     x
     ;; We started out with the netdecls and extended them, so the delta has
     ;; the new netdecls we want.
     :netdecls delta.netdecls

     ;; We rewrote all of our own assigns, but there are also assigns in the
     ;; delta, so merge them.
     :assigns (revappend-without-guard delta.assigns assigns)

     ;; The rewritten modinsts/gateinsts above are fine, we haven't added any
     ;; modinsts, there are no addmods...
     :modinsts modinsts
     :gateinsts gateinsts

     ;; The starting delta includes all former warnings for X, so the delta's
     ;; warnings are fine.
     :warnings delta.warnings))

  ///

  (defthm vl-module->name-of-vl-module-split
    (equal (vl-module->name (vl-module-split x))
           (vl-module->name x))))


(defprojection vl-modulelist-split (x)
  (vl-module-split x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (split)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-split
     (equal (vl-modulelist->names (vl-modulelist-split x))
            (vl-modulelist->names x)))))
