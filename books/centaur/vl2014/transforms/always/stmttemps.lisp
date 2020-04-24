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
(include-book "util")
(include-book "conditions")
(include-book "../../mlib/modgen")
(include-book "../../mlib/expr-slice")
(include-book "../../mlib/delta")
(local (include-book "../../util/arithmetic"))

(defxdoc stmttemps
  :parents (always-top)
  :short "Replace @('if') conditions and right-hand sides into temporary
wires."

  :long "<p>This is a preprocessing step in synthesizing always blocks.  We
expect it to be run only after expressions are sized.</p>

<p>We rewrite statements throughout each flop-like @('always') block, adding
temporary wires for:</p>

<ol>
<li>non-trivial conditions of if expressions</li>
<li>non-sliceable right-hand sides of assignment statements</li>
</ol>

<p>We don't apply this transform to latch-like blocks, because it would
interfere with our sensitivity-list checking.  That is, if our sensitivity list
is something like @('@(en1 or en2 or d)') and we rewrite @('if (en1 & en2)
...')  to @('if (temp_123) ...'), we would think the resulting sensitivity list
was incorrect.</p>

<p>Regarding (1), this is mainly an optimization.  The idea is that we want to
simplify the condition expressions, since we might end up duplicating them
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

<p>And we'll be redundantly synthesizing this complex expression.  This
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

(local (xdoc::set-default-parents stmttemps))

(define vl-assignstmt-stmttemps ((x     vl-stmt-p)
                                 (delta vl-delta-p)
                                 (elem  vl-modelement-p))
  :guard (eq (vl-stmt-kind x) :vl-assignstmt)
  :returns (mv (new-x vl-stmt-p  :hyp :fguard)
               (delta vl-delta-p :hyp :fguard))
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
       (loc                      (vl-modelement->loc elem))
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
                               :vardecls (cons temp-decl delta.vardecls)
                               :assigns  (cons temp-ass delta.assigns)))))

(define vl-ifstmt-stmttemps
  ((x     "any statement, but we only rewrite it when it's an if statement;
           this makes writing @(see vl-stmt-stmttemps) very simple."
          vl-stmt-p)
   (delta vl-delta-p)
   (elem  vl-modelement-p))
  :returns (mv (new-x vl-stmt-p :hyp :fguard)
               (delta vl-delta-p :hyp :fguard))
  :short "Introduce temp wires for if-statement conditions."

  (b* (((unless (eq (vl-stmt-kind x) :vl-ifstmt))
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

       (loc                      (vl-modelement->loc elem))
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
                         :vardecls (cons temp-decl delta.vardecls)))))

(defines vl-stmt-stmttemps
  :short "Apply the @(see stmttemps) transform to a statement"
  (define vl-stmt-stmttemps ((x     vl-stmt-p)
                             (delta vl-delta-p)
                             (elem  vl-modelement-p))
    :returns (mv (new-x vl-stmt-p :hyp :fguard)
                 (delta vl-delta-p :hyp :fguard))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-atomicstmt-p x))
          (if (eq (vl-stmt-kind x) :vl-assignstmt)
              (vl-assignstmt-stmttemps x delta elem)
            (mv x delta)))
         (substmts            (vl-compoundstmt->stmts x))
         ((mv substmts delta) (vl-stmtlist-stmttemps substmts delta elem))
         (x                   (change-vl-compoundstmt x :stmts substmts))
         ((mv x delta)        (vl-ifstmt-stmttemps x delta elem)))
      (mv x delta)))

  (define vl-stmtlist-stmttemps ((x     vl-stmtlist-p)
                                 (delta vl-delta-p)
                                 (elem  vl-modelement-p))
    :returns (mv (new-x (and (vl-stmtlist-p new-x)
                             (equal (len new-x) (len x)))
                        :hyp :fguard)
                 (delta vl-delta-p :hyp :fguard))
    :verify-guards nil
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv nil delta))
         ((mv car delta) (vl-stmt-stmttemps (car x) delta elem))
         ((mv cdr delta) (vl-stmtlist-stmttemps (cdr x) delta elem)))
      (mv (cons car cdr) delta)))

  ///
  (verify-guards vl-stmt-stmttemps))

(define vl-always-stmttemps ((x     vl-always-p)
                             (delta vl-delta-p))
  :returns (mv (new-x vl-always-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  (b* (((vl-always x) x)
       ((mv clk ?body) (vl-match-posedge-clk x))
       ((unless clk)
        ;; Not a flop-like always block, so don't change it.  We can screw
        ;; up the sensitivity lists on latches, otherwise.
        (mv x delta))
       ((mv stmt delta) (vl-stmt-stmttemps x.stmt delta x)))
    (mv (change-vl-always x :stmt stmt) delta)))

(define vl-alwayslist-stmttemps  ((x     vl-alwayslist-p)
                                  (delta vl-delta-p))
  :returns (mv (new-x vl-alwayslist-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  (b* (((when (atom x))
        (mv x delta))
       ((mv car delta) (vl-always-stmttemps (car x) delta))
       ((mv cdr delta) (vl-alwayslist-stmttemps (cdr x) delta)))
    (mv (cons car cdr) delta)))

(define vl-module-stmttemps ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)
       ((unless x.alwayses)
        ;; Optimization: not going to do anything, don't bother re-consing the
        ;; module.
        x)
       (delta (vl-starting-delta x))
       (delta (change-vl-delta delta
                               :vardecls x.vardecls
                               :assigns x.assigns))
       ((mv alwayses delta) (vl-alwayslist-stmttemps x.alwayses delta))
       ((vl-delta delta)    (vl-free-delta delta)))
    (change-vl-module x
                      :alwayses alwayses
                      :assigns  delta.assigns
                      :vardecls delta.vardecls
                      :warnings delta.warnings)))

(defprojection vl-modulelist-stmttemps (x)
  (vl-module-stmttemps x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-stmttemps
  :short "Top-level @(see stmttemps) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-stmttemps x.mods))))
