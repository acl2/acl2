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
(include-book "conditions")
(include-book "../occform/util")
(include-book "../../mlib/expr-slice")
(include-book "../../mlib/stmt-tools")
(include-book "../../mlib/delta")
(include-book "../../mlib/context")
(local (include-book "../../util/arithmetic"))

(defxdoc stmttemps
  :parents (always-top)
  :short "Replace @('if') conditions and right-hand sides into temporary
wires."

  :long "<p>This is a preprocessing step in synthesizing always blocks.  We
expect it to be run only after expressions are sized.</p>

<p>We rewrite statements throughout each @('always') block, adding temporary
wires for:</p>

<ol>
<li>non-trivial conditions of if expressions</li>
<li>non-sliceable right-hand sides of assignment statements</li>
</ol>

<p>Regarding (1), this is really just an optimization.  The idea is that we want
to simplify the condition expressions, since we might end up duplicating them
across many flops.  That is, if we have a block like:</p>

@({
   always @@(posedge clk)
     if (foo1 + foo2 + foo3 + foo4 == 1) begin
        a <= b;
        c <= d;
     end
})

<p>Then this might lead to flops like:</p>

@({
     myflop flop1 (a, (foo1 + foo2 + foo3 + foo4 == 1) ? b : a, clk);
     myflop flop2 (c, (foo1 + foo2 + foo3 + foo4 == 1) ? d : c, clk);
})

<p>And then we'll be redundantly synthesizing this complex expression.  This
wouldn't necessarily be any kind of problem, but it seems like we can do better
by pulling the combinational logic out of the conditions, e.g.:</p>

@({
   wire temp = |( foo1 + foo2 + foo3 + foo4 == 1);

   always @(posedge clk)
     if (temp) begin
       a <= b;
       c <= d;
     end
})

<p>When we synthesize this simpler block, we'll avoid introducing the repeated
subexpression.  That is, our output will be something like:</p>

@({
    wire temp = |( foo1 + foo2 + foo3 + foo4 == 1);
    myflop flop1 (a, temp ? b : a, clk);
    myflop flop2 (c, temp ? d : c, clk);
})

<p>Regarding (2), the idea here is that to support blocks that write to
different bits of wires, we may need to split up the right-hand sides.  For
instance, if we are trying to synthesize something like:</p>

@({
   always @@(posedge clk)
     if (cond)
        {a[1:0], a[3:2]} <= b1 + b2;
     else
        a[3:0] <= b1 + b2 + 1;
})

<p>Then we're basically going to end up dealing with this at the bit level, and
we're going to have to talk about bit @('0') of these compound expressions like
@('b1 + b2').  So we will want to be able to split up the right-hand sides we
see.  We also split up any wires where the widths of the lhs/rhs don't agree,
so that later transforms just need to deal with compatible assignments.</p>")

(define vl-assignstmt-stmttemps ((x     vl-assignstmt-p)
                                 (delta vl-delta-p)
                                 (elem  vl-modelement-p))
  :returns (mv (new-x vl-assignstmt-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  :parents (stmttemps)
  :short "Introduce temp wires for right-hand sides."

  (b* (((vl-assignstmt x) x)

       (lw    (vl-expr->finalwidth x.lvalue))
       (ltype (vl-expr->finaltype x.lvalue))
       (rw    (vl-expr->finalwidth x.expr))
       (rtype (vl-expr->finaltype x.expr))

       ((unless (and (posp lw) ltype))
        (mv x (dwarn :type :vl-stmttemps-fail
                     :msg "~a0: failing to transform assignment ~a1. ~
                           Expected the lhs to have positive width and ~
                           decided type, but found width ~x2 and type ~x3."
                     :args (list elem x lw ltype))))

       ((unless (and (posp rw) rtype))
        (mv x (dwarn :type :vl-stmttemps-fail
                     :msg "~a0: failing to transform assignment ~a1. ~
                           Expected the rhs to have positive width and ~
                           decided type, but found width ~x2 and type ~x3."
                     :args (list elem x rw rtype))))

       ((when (and (eql lw rw)
                   (vl-expr-sliceable-p x.expr)))
        ;; Looks prefectly reasonable, no need to do anything
        (mv x delta))

       ;; Everything looks good.  Introduce a temp wire.  The statement has
       ;; some crazy rhs, so there's not a good way to name it, really.  The
       ;; width we use for the temp wire is the LHS's width.  The truncation,
       ;; if any, moves to the new assign statement we make.
       (loc                      (vl-modelement-loc elem))
       ((vl-delta delta)         delta)
       ((mv temp-name nf)        (vl-namefactory-indexed-name "vl_rhs" delta.nf))
       ((mv temp-expr temp-decl) (vl-occform-mkwire temp-name lw :loc loc))

       ;; 1. Assign temp = rhs
       ;; 2. Rewrite stmt "lhs = rhs" to "lhs = temp"
       (temp-ass (make-vl-assign :lvalue temp-expr
                                 :expr   x.expr
                                 :loc    loc))
       (new-x    (change-vl-assignstmt x :expr temp-expr)))

    (mv new-x (change-vl-delta delta
                               :nf       nf
                               :netdecls (cons temp-decl delta.netdecls)
                               :assigns  (cons temp-ass delta.assigns)))))

(define vl-ifstmt-stmttemps
  ((x     "any statement, but we only rewrite it when it's an if statement;
           this makes writing @(see vl-stmt-stmttemps) very simple."
          (and (vl-stmt-p x)
               (vl-compoundstmt-p x)))
   (delta vl-delta-p)
   (elem  vl-modelement-p))
  :returns (mv (new-x vl-stmt-p :hyp :fguard)
               (delta vl-delta-p :hyp :fguard))
  :parents (stmttemps)
  :short "Introduce temp wires for if-statement conditions."

  (b* (((unless (vl-ifstmt-p x))
        ;; This makes the guards/basic-checks stuff for the caller very easy.
        (mv x delta))

       ((vl-ifstmt x) x)
       (width (vl-expr->finalwidth x.condition))
       (type  (vl-expr->finaltype  x.condition))

       ((when (and (eql width 1)
                   (vl-fast-atom-p x.condition)
                   (vl-expr-sliceable-p x.condition)))
        ;; I guess it's simple enough already, don't introduce a new wire.
        (mv x delta))

       ((unless (and type (posp width)))
        (mv x (dwarn :type :vl-stmttemps-fail
                     :msg "~a0: failing to transform if-statement condition ~
                           for ~a1. Expected the condition to have positive ~
                           width and decided type, but found width ~x2 and ~
                           type ~x3."
                     :args (list elem x width type))))

       ((unless (vl-expr-welltyped-p x.condition))
        (mv x (dwarn :type :vl-stmttemps-fail
                     :msg "~a0: failing to transform if-statement condition ~
                           for ~a1.  The condition expression is not well ~
                           typed! Raw expression: ~x2."
                     :args (list elem x x.condition)
                     :fatalp t)))

       (loc                      (vl-modelement-loc elem))
       ((vl-delta delta)         delta)
       ((mv temp-name nf)        (vl-namefactory-indexed-name "vl_test" delta.nf))
       ((mv temp-expr temp-decl) (vl-occform-mkwire temp-name 1 :loc loc))
       (temp-rhs                 (vl-condition-fix x.condition))
       (temp-assign              (make-vl-assign :lvalue temp-expr
                                                 :expr   temp-rhs
                                                 :loc    loc)))
    (mv (change-vl-ifstmt x
                          :condition temp-expr)
        (change-vl-delta delta
                         :nf       nf
                         :assigns  (cons temp-assign delta.assigns)
                         :netdecls (cons temp-decl delta.netdecls)))))

(defsection vl-stmt-stmttemps
  :parents (stmttemps)

  (mutual-recursion

   (defund vl-stmt-stmttemps (x delta elem)
     "Returns (mv new-x delta)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-delta-p delta)
                                 (vl-modelement-p elem))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (if (vl-fast-assignstmt-p x)
               (vl-assignstmt-stmttemps x delta elem)
             (mv x delta)))

          (substmts            (vl-compoundstmt->stmts x))
          ((mv substmts delta) (vl-stmtlist-stmttemps substmts delta elem))
          (x                   (change-vl-compoundstmt x :stmts substmts))
          ((mv x delta)        (vl-ifstmt-stmttemps x delta elem)))
       (mv x delta)))

   (defund vl-stmtlist-stmttemps (x delta elem)
     "Returns (mv new-x delta)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-delta-p delta)
                                 (vl-modelement-p elem))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv nil delta))
          ((mv car delta) (vl-stmt-stmttemps (car x) delta elem))
          ((mv cdr delta) (vl-stmtlist-stmttemps (cdr x) delta elem)))
       (mv (cons car cdr) delta))))

  (flag::make-flag vl-flag-stmt-stmttemps
                   vl-stmt-stmttemps
                   :flag-mapping ((vl-stmt-stmttemps . stmt)
                                  (vl-stmtlist-stmttemps . list)))

  (local (defun my-induction (x delta elem)
           (b* (((when (atom x))
                 (mv nil delta))
                ((mv car delta) (vl-stmt-stmttemps (car x) delta elem))
                ((mv cdr delta) (my-induction (cdr x) delta elem)))
             (mv (cons car cdr) delta))))

  (defthm len-of-vl-stmtlist-stmttemps
    (equal (len (mv-nth 0 (vl-stmtlist-stmttemps x delta elem)))
           (len x))
    :hints(("Goal"
            :induct (my-induction x delta elem)
            :expand (vl-stmtlist-stmttemps x delta elem))))

  (defthm-vl-flag-stmt-stmttemps

    (defthm return-type-of-vl-stmt-stmttemps
      (implies (and (force (vl-stmt-p x))
                    (force (vl-delta-p delta))
                    (force (vl-modelement-p elem)))
               (b* (((mv new-x delta)
                     (vl-stmt-stmttemps x delta elem)))
                 (and (vl-stmt-p new-x)
                      (vl-delta-p delta))))
      :flag stmt)

    (defthm return-type-of-vl-stmtlist-stmttemps
      (implies (and (force (vl-stmtlist-p x))
                    (force (vl-delta-p delta))
                    (force (vl-modelement-p elem)))
               (b* (((mv new-x delta)
                     (vl-stmtlist-stmttemps x delta elem)))
                 (and (vl-stmtlist-p new-x)
                      (vl-delta-p delta))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-stmt-stmttemps x delta elem)
                     (vl-stmtlist-stmttemps x delta elem)))))

  (verify-guards vl-stmt-stmttemps))

(define vl-always-stmttemps ((x     vl-always-p)
                             (delta vl-delta-p))
  :returns (mv (new-x vl-always-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  :parents (stmttemps)
  (b* (((vl-always x) x)
       ((mv stmt delta) (vl-stmt-stmttemps x.stmt delta x)))
    (mv (change-vl-always x :stmt stmt) delta)))

(define vl-alwayslist-stmttemps  ((x     vl-alwayslist-p)
                                  (delta vl-delta-p))
  :returns (mv (new-x vl-alwayslist-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  :parents (stmttemps)
  (b* (((when (atom x))
        (mv x delta))
       ((mv car delta) (vl-always-stmttemps (car x) delta))
       ((mv cdr delta) (vl-alwayslist-stmttemps (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-module-stmttemps ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (stmttemps)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        ;; Optimization: not going to do anything, don't bother re-consing the
        ;; module.
        x)
       (delta (vl-starting-delta x))
       (delta (change-vl-delta delta
                               :netdecls x.netdecls
                               :assigns x.assigns))
       ((mv alwayses delta) (vl-alwayslist-stmttemps x.alwayses delta))
       ((vl-delta delta)    (vl-free-delta delta)))
    (change-vl-module x
                      :alwayses alwayses
                      :assigns  delta.assigns
                      :netdecls delta.netdecls
                      :warnings delta.warnings))
  ///
  (defthm vl-module->name-of-vl-module-stmttemps
    (equal (vl-module->name (vl-module-stmttemps x))
           (vl-module->name x))))

(defprojection vl-modulelist-stmttemps (x)
  (vl-module-stmttemps x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (stmttemps)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-stmttemps
     (equal (vl-modulelist->names (vl-modulelist-stmttemps x))
            (vl-modulelist->names x)))))

