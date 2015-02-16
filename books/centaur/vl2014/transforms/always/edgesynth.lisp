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
(include-book "nedgeflop")
(include-book "conditions")
(include-book "../../mlib/welltyped")
(include-book "../../mlib/delta")
(include-book "../../mlib/filter")
(include-book "../oprewrite") ;; BOZO for vl-qmark-p
(local (include-book "../../util/arithmetic"))


(local (defthm vl-atomicstmt-p-of-vl-ifstmt
         (equal (vl-atomicstmt-p (make-vl-ifstmt :condition condition
                                                 :truebranch truebranch
                                                 :falsebranch falsebranch
                                                 :atts atts))
                nil)
         :hints(("Goal" :in-theory (enable vl-atomicstmt-p)))))

(local (defthm vl-atomicstmt-p-of-vl-blockstmt
         (equal (vl-atomicstmt-p (make-vl-blockstmt :sequentialp sequentialp
                                                    :name name
                                                    :vardecls vardecls
                                                    :paramdecls paramdecls
                                                    :imports imports
                                                    :stmts stmts
                                                    :atts atts))
                nil)
         :hints(("Goal" :in-theory (enable vl-atomicstmt-p)))))

(xdoc::add-resource-directory "vl/always" "images")

(defxdoc edgesynth
  :parents (always-top)
  :short "Synthesize simple edge-triggered @('always') blocks into primitives."

  :long "<p>This is our \"final,\" transformation for synthesizing
edge-triggered always blocks into primitives.  This transform supports only a
limited subset of Verilog statements.  Generally speaking, VL can handle a much
richer subset of Verilog statements than we are going to deal with here.  Other
@(see transforms)&mdash;e.g., @(see stmtrewrite), @(see caseelim), and @(see
edgesplit)&mdash;are typically first used to reduce these much richer
statements into the simple form that we now target.</p>

<p>Despite the many limits we place on the Verilog statements that we do try to
support here, synthesizing edge-triggered always blocks is still difficult to
do in a way that is completely faithful to the Verilog semantics.  We describe
some of the challenges and our general approach below.</p>


<h3>Preliminaries: Edge-Triggered Blocks, Clocks</h3>

<p><u>Definition.</u> We say that an @('always') block is <b>edge-triggered</b>
when it contains a @(see vl-timingstmt) whose control is a list of @('posedge')
or @('negedge') events.  As examples:</p>

@({
 always @(posedge clk) ... ;                  // edge-triggered
 always @(negedge clk) ... ;                  // edge-triggered
 always @(posedge clk or negedge reset) ... ; // edge-triggered

 always @(*) ... ;                            // not edge-triggered
 always @(a or b or c) ... ;                  // not edge-triggered
 always @(posedge clk or a) ... ;             // not edge-triggered
 always #3 ... ;                              // not edge-triggered
 always begin ... end ;                       // not edge-triggered
})

<p>Throughout this discussion, we will assume that we are attempting to
synthesize an edge-triggered always block.  Some other kinds of @('always')
blocks are supported by other VL transforms, e.g., the @(see cblock) transform
can process certain kinds of combinational always blocks.  But we aren't going
to try to cover any of that, here.</p>

<p>For many years, VL only supported edge-triggered always blocks that had a
single @('posedge') or @('negedge') trigger.  We now support arbitrary lists of
@('posedge') and @('negedge') edges.  That is, we can now handle always blocks
such as:</p>

@({
 always @(posedge a or negedge b or posedge c or ...)
 begin
    // restricted statements as explained below
 end
})

<p><u>Definition</u>.  We say that the <b>clocks</b> of such an always block
are the expressions in the sensitivity list, regardless of whether they are
used with @('posedge') or @('negedge') specifiers.  For instance:</p>

@({
 // example:                                  // clocks (expressions)
 always @(posedge clk) ...;                   //   clk
 always @(posedge mclk or negedge reset) ...; //   mclk, reset
 always @(posedge a & b or posedge c[0]) ...; //   a & b, c[0]
})

<p>We only support always blocks whose clocks are each <b>one-bit wide, plain
identifiers</b>.  Why?</p>

<ul>

<li>The width restriction is meant to avoid mismatches between Verilog tools:
we have found that various Verilog simulators do not agree about what
constitutes an edge for a wide signal.  At any rate, it would be weird to ask
about the edge of a wide signal.</li>

<li>Requiring the clock be a plain identifier is a significant help in keeping
our processing code more simple.  We'll soon describe some of the timing
nuances that make it important to be able to distinguishing clocks from
non-clocks in @('if') statements and right-hand sides of expressions.  We think
this restriction is probably not too severe, as most reasonable designs will
not include, e.g., vectors of clocks.</li>

</ul>


<h3>Synthesis Challenge: X Optimism</h3>

<p>One basic problem in synthesizing edge-triggered @('always') blocks (or any
other kind of @('always') blocks, for that matter) is the unwarranted optimism
of @('if') statements.</p>

<p>Suppose for simplicity that @('en') is one bit wide.  In the Verilog
semantics, a statement like @('if (en) q <= d') causes an update to @('q') only
if @('en') evaluates to 1.  If @('en') instead evaluates to X or Z, the @('if')
statement <b>pretends it evaluated to 0</b> and does not update @('q').  This
is generally bad, as it fails to properly treat X as an unknown.</p>

<p>When we synthesize these always blocks for use with properly monotonic
back-ends like @(see esim), where X really does represent an unknown, we have
no way to model this kind of optimism.  Instead, roughly speaking, we are going
to treat these statements like @('?:') operators, which have safer but
different X behavior.  That is, in our semantics, when @('en') evaluates to X
or Z, we may write an X value into @('q') instead of failing to update it.</p>

<p>We cannot see any way to avoid this kind of mismatch.  We generally regard
the @('?:') behavior as more reasonable and safer.  But it's easy to imagine
that if @('q') is later fed into other, non-conservative Verilog
constructs (such as if statements, case/casex/casez statements, case equality
operators, etc.), then a Verilog simulator could go produce completely
different results than, say, an esim-based simulation.</p>


<h3>Synthesis Challenge: Clock/Data Races</h3>

<p>A much more subtle and tricky problem is the event-based Verilog timing
model allows for a number of races between the clock signals and the data
inputs.  To illustrate this, consider the following examples:</p>

@({
    // Version 1:

    always @(posedge clk or posedge reset)
      q <= reset ? 0 : data;

    // Version 2:

    wire q_next;
    assign q_next = reset ? 0 : data;
    always @(posedge clk or posedge reset)
      q <= q_next;
})

<p>You might hope these would behave the same.  After all, it looks like the
only difference is that we've named an intermediate expression.  Unfortunately,
Version 2 has a race condition in Verilog simulators.  In Version 2, when
@('reset') transitions from low to high, two separate events need to be
scheduled: the @('assign') and the @('always') block.  These events may occur
in any order, so we may find that either:</p>

<ul>

<li>The @('assign') statement happens first, so @('q_next') \"properly\" is
updated to 0 before the @('always') block updates @('q'), or</li>

<li>The @('always') statement happens first, so @('q_next') \"improperly\" has
the old value of @('data') when we assign it to @('q').</li>

</ul>

<p>(If you run these on a Verilog simulator and find that they simulate in the
same way, try reordering the assignment and the always block and you may get a
different result.)</p>

<p>In contrast, at least in Verilog's simulation semantics, Version 1 does not
suffer from this problem and will \"properly\" reset @('q').  The reason this
works is that there are no competing events are triggered by the transition of
@('reset'); only the single @('always') block must be run.</p>

<p>Here is an attempt to visualize what we might be modeling when we write
these two fragments of Verilog.</p>

<img src='res/vl/always/edgesynth_reset.png'/>

<p>Version 1 might be sensible.  If this handling of @('reset') is to be an
intrinsic part of the always block, a circuit designer might be able to design
something that implements it correctly.</p>

<p>But Version 2 is clearly not okay.  Here, with the muxing done independently
of the flop, we can see that a change in reset is going to trigger an update in
both the flop itself and in the mux that is feeding the flop.  This is a clear
race.</p>

<p>The fanciful \"horrible circuit\" is similar to Version 2, but made worse
just to drive the point home.  Imagine here that the adder is some large
circuit with some large delay.  When reset goes high, the flip-flop is
triggered and, meanwhile, the adder's inputs have changed, so it will be busily
transitioning to compute the new sum.  The value that gets latched in, then, is
anyone's guess.  Clearly you would never want to design something like
this.</p>

<p>At any rate, if we regard the right-hand sides of assignments in an
edge-triggered always block as the data inputs to flip-flops, then for our
design to make any sense, we really need these data inputs to be stable
whenever a clock changes.  For that to hold, these assignments should, at the
very least, <b>not depend on the clocks</b> of the always block.</p>

<p>This is difficult to reliably identify syntactically.  Even in a simple case
like Version 2, we would need to analyze the assignments that are occurring in
the module to discover that @('q_next') depends on @('reset').  If @('q_next')
were instead driven by some submodule, then noticing this would require an
analysis of that submodule.  Aliasing makes this much worse, e.g., what if we
have something like:</p>

@({
     wire my_clk = real_clk;
     always @(posedge my_clk) q <= real_clk;
})

<p>At any rate, detecting this situation seems very difficult, so we have not
seriously considered trying to identify these races.  We do, however, at least
forbid the clocks from occurring in the right hand sides of expressions.</p>

<p>This may seem quite unsatisfying&mdash;it rules out Version 1 and doesn't
rule out Version 2!  But this restriction is practically very useful.  It means
that for the blocks we <i>do</i> support, it's reasonable to move the
right-hand sides out of the always block.  That is, it makes it safe to do
something like:</p>

@({
    always @(posedge clk or posedge reset)
      if (reset)
         q <= 0;
      else
         q <= q+1;
    -->

    assign q_next = q+1;

    always @(posedge clk or posedge reset)
      if (reset)
         q <= 0;
      else
         q <= q_next;
})

<p>This sort of reassignment wouldn't be valid if the right-hand side
expression mentioned any of the clocks, as we have just beaten to death,
above.  (It's the whole difference between Version 1 and Version 2).</p>


<h3>Historic Approach to Edge-Triggered Blocks</h3>

<p>Before describing our new approach, it's useful to describe the old way that
VL handled edge-triggered blocks.  Previously, VL supported only basic,
single-edge registers, and reduced all supported always blocks into instances
of a single, 1-bit flip-flop primitive.</p>

@({
    module VL_1_BIT_FLOP (q, d, clk);
      output reg q;
      input d;
      input clk;
      always @(posedge clk)
        q <= d;
    endmodule
})

<p>Given this primitive, it was straightforward to implement a simple,
posedge-triggered, <i>N</i>-bit flip-flop: just instance <i>N</i> of these
primitive flops, one for each bit.  We named the resulting modules, e.g.,
@('VL_4_BIT_FLOP'), @('VL_128_BIT_FLOP'), and so forth, for any <i>N</i>.</p>

<p>We then had a transformation that could support basic @('always') blocks by
converting them into instances of an appropriately sized flop module.  For
instance:</p>

@({
    always @(posedge clk)
      q <= a + b + cin;
     --->
    VL_12_BIT_FLOP foo123 (q, a + b + cin, clk);
})

<p>Our transform could also support always blocks with limited if/else
expressions, by merging the if/else structure into the data input.  For
instance:</p>

@({
    always @(posedge clk)
    begin
      if (cycle)
         q <= 12'b0;
      else
         q <= a + b + cin;
    end
    --->
    VL_12_BIT_FLOP foo123 (q, cycle ? 12'b0 : a + b + cin, clk);
})

<p>Along with other transforms, e.g., for converting @('negedge') into posedge
signals by inverting them, this allowed VL to support a fairly rich set of
single-edge always blocks.  Meanwhile, back-end tools like @(see esim) only
needed to support a single VL_1_BIT_FLOP primitive.  Historically this was done
using a traditional master/slave latch style.</p>


<h3>New Primitives</h3>

<p>Unfortunately, we don't how we can construct a multi-edge flip flop out of a
single-edge flip-flop.  To allow VL to support @('always') blocks with multiple
edges, then, we need new primitives.</p>

<p>After studying the kinds of multi-edge flops that we wanted to support, we
decided that what we really want is a flip-flop with a built-in priority mux
that is governed by the clock edges.  Our new, simplest flip-flop primitive is
just like the previous VL_1_BIT_FLOP:</p>

@({
    module VL_1_BIT_1_EDGE_FLOP (q, d, clk);
      output reg q;
      input d;
      input clk;
      always @(posedge clk)
        q <= d;
    endmodule
})

<p>The next simplest primitive has two clocks and two data signals.  We assume
that one clock has priority over the other.  This module is just a slight
generalization of, e.g., Version 1 of the resettable mux that we saw above,
where instead of necessarily resetting to zero we can choose between two
arbitrary data inputs.</p>

@({
    module VL_1_BIT_2_EDGE_FLOP (q, d0, d1, clk0, clk1);
     output reg q;
     input d0, d1;
     input clk0, clk1;
     always @(posedge clk0 or posedge clk1)
       if (clk0)
          q <= d0
       else
          q <= d1;
    endmodule
})

<p><b>BOZO</b> consider using ?: instead of IF here for the Verilog definition.</p>

<p>For three clocks we simply add another clock and data input, extending the
priority mux.  This module could be used to model, e.g., a flip-flop with
asynchronous set and clears, e.g., by allowing @('d0 = 1') and @('d1 = 0') or
vice versa depending on the desired priority of set versus clear.</p>

@({
    module VL_1_BIT_3_EDGE_FLOP (q, d0, d1, d2, clk0, clk1, clk2);
     output reg q;
     input d0, d1;
     input clk0, clk1;
     always @(posedge clk0 or posedge clk1 or posedge clk2)
       if (clk0)
          q <= d0
       else if (clk1)
          q <= d1;
       else
          q <= d2;
    endmodule
})

<p>Although we don't know what use there would be for such a flip-flop with
more than three clocks and data inputs, we can continue this way, adding more
clocks and data inputs, up to any number desired.  See @(see nedgeflop) for
more details about how we generate these primitives.</p>

<p>Given these new primitives, we can still construct wide flip-flops by
chaining together one-bit primitive flops.</p>

<p>The remaining challenge is to line up edge-triggered @('always') with
instances of these primitives.</p>")

(local (xdoc::set-default-parents edgesynth))



; -----------------------------------------------------------------------------
;
;                                Edge Tables
;
; -----------------------------------------------------------------------------

(defsection edge-tables
  :short "Data structure that conveniently summarizes a sensitivity list."
  :long "<p>In @(see edgesynth) we only support always blocks with simple event
controls such as</p>

@({
    always @(posedge clk1 or negedge clk2 or posedge clk3 or ...)
})

<p>It's convenient not to work with these as lists of evatoms, but instead to
just build a table that lets us look up the kind of clock and tells us the
clock names.</p>")

(define vl-edgesynth-edge-p (x)
  (and (vl-evatom-p x)
       (b* (((vl-evatom x) x))
         (and (or (eq x.type :vl-posedge)
                  (eq x.type :vl-negedge))
              (vl-idexpr-p x.expr)
              (vl-expr->finaltype x.expr)
              (equal (vl-expr->finalwidth x.expr) 1)))))

(deflist vl-edgesynth-edgelist-p (x)
  (vl-edgesynth-edge-p x)
  :elementp-of-nil nil)

(define vl-edgesynth-edge->expr ((x vl-edgesynth-edge-p))
  :parents (vl-edgesynth-edge-p)
  :returns (expr (and (vl-expr-p expr)
                      (vl-idexpr-p expr)
                      (vl-expr->finaltype expr)
                      (equal (vl-expr->finalwidth expr) 1))
                 :hyp :guard)
  (vl-evatom->expr x)
  :prepwork ((local (in-theory (enable vl-edgesynth-edge-p)))))

(define vl-edgesynth-edge->name ((x vl-edgesynth-edge-p))
  :parents (vl-edgesynth-edge-p)
  :returns (name stringp :rule-classes :type-prescription)
  (vl-idexpr->name (vl-evatom->expr x))
  :prepwork ((local (in-theory (enable vl-edgesynth-edge-p)))))

(define vl-edgesynth-edge->posedgep ((x vl-edgesynth-edge-p))
  :parents (vl-edgesynth-edge-p)
  :returns (type booleanp :rule-classes :type-prescription)
  (eq (vl-evatom->type x) :vl-posedge)
  :prepwork ((local (in-theory (enable vl-edgesynth-edge-p)))))

(defalist vl-edgetable-p (x)
  :key (stringp x)
  :val (vl-edgesynth-edge-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :short "Associates each edge name to the edge itself.")

(local (defthm string-listp-of-alist-keys-when-vl-edgetable-p
         (implies (vl-edgetable-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :induct (len x)))))

(define vl-make-edgetable
  ((edges (and (vl-evatomlist-p edges)
               (vl-evatomlist-all-have-edges-p edges)
               (vl-idexprlist-p (vl-evatomlist->exprs edges))
               (not (member nil (vl-exprlist->finaltypes (vl-evatomlist->exprs edges))))
               (all-equalp 1 (vl-exprlist->finalwidths (vl-evatomlist->exprs edges))))))
  :returns (table vl-edgetable-p :hyp :fguard)
  :prepwork ((local (in-theory (e/d (vl-edgesynth-edge-p
                                     vl-evatomlist-all-have-edges-p)
                                    (all-equalp)))))
  (if (atom edges)
      nil
    (acons (vl-edgesynth-edge->name (car edges))
           (car edges)
           (vl-make-edgetable (cdr edges)))))


; -----------------------------------------------------------------------------
;
;                         Assignment Statement Lists
;
; -----------------------------------------------------------------------------

; BOZO find me a home

(deflist vl-assignstmtlist-p (x)
  (vl-assignstmt-p x)
  :guard (vl-stmtlist-p x)
  :elementp-of-nil nil
  ///
  (defthm vl-atomicstmtlist-p-when-vl-assignstmtlist-p
    (implies (vl-assignstmtlist-p x)
             (vl-atomicstmtlist-p x))
    :hints(("Goal"
            :induct (len x)
            :in-theory (enable vl-atomicstmt-p)))))

(defprojection vl-assignstmtlist->lhses (x)
  (vl-assignstmt->lvalue x)
  :guard (and (vl-stmtlist-p x)
              (vl-assignstmtlist-p x))
  :result-type vl-exprlist-p)

(defprojection vl-assignstmtlist->rhses (x)
  (vl-assignstmt->expr x)
  :guard (and (vl-stmtlist-p x)
              (vl-assignstmtlist-p x))
  :result-type vl-exprlist-p)

(deflist vl-assigncontrols-p (x)
  (vl-maybe-delayoreventcontrol-p x)
  :guard t
  :elementp-of-nil t)

(defprojection vl-assignstmtlist->controls (x)
  (vl-assignstmt->ctrl x)
  :guard (and (vl-stmtlist-p x)
              (vl-assignstmtlist-p x))
  :result-type vl-assigncontrols-p)


; -----------------------------------------------------------------------------
;
;                    Basic Syntax for Supported Statements
;
; -----------------------------------------------------------------------------

(defines vl-edgesynth-stmt-p
  :short "Supported statements: if statements, block statements, null
statements, non-blocking assignments to whole identifiers."

  (define vl-edgesynth-stmt-p ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((unless (mbt (vl-stmt-p x)))
          nil)

         ((when (vl-nullstmt-p x))
          t)

         ((when (vl-assignstmt-p x))
          (b* (((vl-assignstmt x) x))
            (and (eq x.type :vl-nonblocking)
                 (vl-idexpr-p x.lvalue)
                 (vl-expr->finaltype x.lvalue)
                 (posp (vl-expr->finalwidth x.lvalue)))))

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x))
            (and (vl-edgesynth-stmt-p x.truebranch)
                 (vl-edgesynth-stmt-p x.falsebranch))))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x))
            (and x.sequentialp  ;; BOZO could we also support fork/join?
                 (not x.name)
                 (not x.vardecls)
                 (not x.paramdecls)
                 (not x.imports)
                 (vl-edgesynth-stmtlist-p x.stmts)))))

      ;; We don't support anything else.
      nil))

  (define vl-edgesynth-stmtlist-p ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        (not x)
      (and (vl-edgesynth-stmt-p (car x))
           (vl-edgesynth-stmtlist-p (cdr x)))))

  ///
  (xdoc::without-xdoc
    (deflist vl-edgesynth-stmtlist-p (x)
      (vl-edgesynth-stmt-p x)
      :already-definedp t
      :true-listp t))

  (defthm vl-stmt-p-when-vl-edgesynth-stmt-p
    (implies (vl-edgesynth-stmt-p x)
             (vl-stmt-p x)))

  (defthm vl-stmtlist-p-when-vl-edgesynth-stmtlist-p
    (implies (vl-edgesynth-stmtlist-p x)
             (vl-stmtlist-p x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-edgesynth-stmt-p-of-make-vl-assignstmt
    (implies (and (force (equal type :vl-nonblocking))
                  (force (vl-idexpr-p lvalue))
                  (force (vl-expr->finaltype lvalue))
                  (force (posp (vl-expr->finalwidth lvalue)))
                  (force (vl-expr-p expr))
                  (force (vl-maybe-delayoreventcontrol-p ctrl))
                  (force (vl-atts-p atts))
                  (force (vl-location-p loc)))
             (vl-edgesynth-stmt-p (make-vl-assignstmt :type type
                                                      :lvalue lvalue
                                                      :expr expr
                                                      :ctrl ctrl
                                                      :atts atts
                                                      :loc loc))))

  (defthm vl-assignstmt->type-when-vl-edgesynth-stmt-p
    (implies (and (vl-assignstmt-p x)
                  (vl-edgesynth-stmt-p x))
             (equal (vl-assignstmt->type x)
                    :vl-nonblocking)))

  (defthm vl-idexpr-p-of-vl-assignstmt->lvalue-when-vl-edgesynth-stmt-p
    (implies (and (vl-assignstmt-p x)
                  (vl-edgesynth-stmt-p x))
             (and (vl-idexpr-p (vl-assignstmt->lvalue x))
                  (posp (vl-expr->finalwidth (vl-assignstmt->lvalue x)))
                  (vl-expr->finaltype (vl-assignstmt->lvalue x)))))

  (defthm vl-edgesynth-stmt-p-of-vl-ifstmt
    (implies (and (vl-edgesynth-stmt-p truebranch)
                  (vl-edgesynth-stmt-p falsebranch)
                  (force (vl-expr-p condition))
                  (force (vl-atts-p atts)))
             (vl-edgesynth-stmt-p (make-vl-ifstmt :condition condition
                                                  :truebranch truebranch
                                                  :falsebranch falsebranch
                                                  :atts atts))))

  (defthm vl-edgesynth-stmt-p-of-vl-ifstmt->truebranch
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-ifstmt-p x)))
             (vl-edgesynth-stmt-p (vl-ifstmt->truebranch x))))

  (defthm vl-edgesynth-stmt-p-of-vl-ifstmt->falsebranch
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-ifstmt-p x)))
             (vl-edgesynth-stmt-p (vl-ifstmt->falsebranch x)))
    ;; wtf, why do I have to disable force here?
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-edgesynth-stmt-p-of-vl-blockstmt
    (implies (and (vl-edgesynth-stmtlist-p stmts)
                  (force (equal sequentialp t))
                  (force (not name))
                  (force (not vardecls))
                  (force (not paramdecls))
                  (force (not imports))
                  (force (vl-atts-p atts)))
             (vl-edgesynth-stmt-p (make-vl-blockstmt :sequentialp sequentialp
                                                     :name name
                                                     :vardecls vardecls
                                                     :paramdecls paramdecls
                                                     :imports imports
                                                     :loaditems loaditems
                                                     :stmts stmts
                                                     :atts atts))))

  (defthm vl-blockstmt->sequentialp-when-vl-edgesynth-stmt-p
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-blockstmt-p x)))
             (equal (vl-blockstmt->sequentialp x)
                    t)))

  (defthm vl-blockstmt->name-when-vl-edgesynth-stmt-p
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-blockstmt-p x)))
             (equal (vl-blockstmt->name x)
                    nil)))

  (defthm vl-blockstmt->decls-when-vl-edgesynth-stmt-p
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-blockstmt-p x)))
             (and (equal (vl-blockstmt->vardecls x)
                         nil)
                  (equal (vl-blockstmt->paramdecls x)
                         nil)
                  (equal (vl-blockstmt->imports x)
                         nil))))

  (defthm vl-edgesynth-stmtlist-p-of-vl-blockstmt->stmts
    (implies (and (vl-edgesynth-stmt-p x)
                  (force (vl-blockstmt-p x)))
             (vl-edgesynth-stmtlist-p (vl-blockstmt->stmts x))))

  (defthm atomic-cases-for-vl-edgesynth-stmt-p
    (implies (and (vl-edgesynth-stmt-p x)
                  (vl-atomicstmt-p x))
             (or (eq (vl-stmt-kind x) :vl-assignstmt)
                 (eq (vl-stmt-kind x) :vl-nullstmt)))
    :rule-classes :forward-chaining
    :hints(("Goal" :in-theory (enable vl-atomicstmt-p)))))


(defines vl-edgesynth-stmt-assigns
  :short "Collect all assignsment statements from an edgesynth statement."
  :hints(("Goal" :in-theory (disable (force))))

  (define vl-edgesynth-stmt-assigns ((x (and (vl-stmt-p x)
                                             (vl-edgesynth-stmt-p x))))
    :returns (assigns (and (vl-stmtlist-p assigns)
                           (vl-assignstmtlist-p assigns)
                           (let ((lhses (vl-assignstmtlist->lhses assigns)))
                             (and (vl-idexprlist-p lhses)
                                  (pos-listp (vl-exprlist->finalwidths lhses))
                                  (not (member nil (vl-exprlist->finaltypes lhses))))))
                      :hyp :fguard)
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-nullstmt-p x))
          nil)

         ((when (vl-assignstmt-p x))
          (list x))

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x))
            (append (vl-edgesynth-stmt-assigns x.truebranch)
                    (vl-edgesynth-stmt-assigns x.falsebranch))))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x))
            (vl-edgesynth-stmtlist-assigns x.stmts))))

      nil))

  (define vl-edgesynth-stmtlist-assigns ((x (and (vl-stmtlist-p x)
                                               (vl-edgesynth-stmtlist-p x))))
    :returns (assigns (and (vl-stmtlist-p assigns)
                           (vl-assignstmtlist-p assigns)
                           (let ((lhses (vl-assignstmtlist->lhses assigns)))
                             (and (vl-idexprlist-p lhses)
                                  (pos-listp (vl-exprlist->finalwidths lhses))
                                  (not (member nil (vl-exprlist->finaltypes lhses))))))
                      :hyp :fguard)
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        nil
      (append (vl-edgesynth-stmt-assigns (car x))
              (vl-edgesynth-stmtlist-assigns (cdr x))))))

(defines vl-edgesynth-stmt-conditions
  :short "Collect all conditions from if statements in an edgesynth statement."
  :hints(("Goal" :in-theory (disable (force))))

  (define vl-edgesynth-stmt-conditions ((x (and (vl-stmt-p x)
                                                (vl-edgesynth-stmt-p x))))
    :returns (rhses vl-exprlist-p :hyp :fguard)
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-nullstmt-p x))
          nil)

         ((when (vl-assignstmt-p x))
          nil)

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x))
            (cons x.condition
                  (append (vl-edgesynth-stmt-conditions x.truebranch)
                          (vl-edgesynth-stmt-conditions x.falsebranch)))))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x))
            (vl-edgesynth-stmtlist-conditions x.stmts))))

      nil))

  (define vl-edgesynth-stmtlist-conditions ((x (and (vl-stmtlist-p x)
                                                    (vl-edgesynth-stmtlist-p x))))
    :returns (conditions vl-exprlist-p :hyp :fguard)
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        nil
      (append (vl-edgesynth-stmt-conditions (car x))
              (vl-edgesynth-stmtlist-conditions (cdr x))))))


; -----------------------------------------------------------------------------
;
;              Checking for Supported Assignment Delay Controls
;
; -----------------------------------------------------------------------------

(define vl-edgesynth-simple-delay-p ((x vl-maybe-delayoreventcontrol-p))
  :short "Recognizer for empty delays and simple integer delays like @('#5')."
  :parents (vl-edgesynth-delays-okp)
  (or (not x)
      (and (mbe :logic (vl-delaycontrol-p x)
                :exec (eq (tag x) :vl-delaycontrol))
           (vl-expr-resolved-p (vl-delaycontrol->value x)))))

(define vl-edgesynth-simple-delay->amount
  :parents (vl-edgesynth-delays-okp)
  :short "Extract the delay amount from a simple enough delay, if any."
  ((x (and (vl-maybe-delayoreventcontrol-p x)
           (vl-edgesynth-simple-delay-p x))))
  :returns (amount maybe-natp :rule-classes :type-prescription)
  (and x
       (vl-resolved->val (vl-delaycontrol->value x)))
  :guard-hints(("Goal" :in-theory (enable vl-edgesynth-simple-delay-p))))

(deflist vl-edgesynth-simple-delays-p (x)
  (vl-edgesynth-simple-delay-p x)
  :guard (vl-assigncontrols-p x)
  :parents (vl-edgesynth-delays-okp))

(defprojection vl-edgesynth-simple-delays->amounts (x)
  (vl-edgesynth-simple-delay->amount x)
  :guard (and (vl-assigncontrols-p x)
              (vl-edgesynth-simple-delays-p x))
  :parents (vl-edgesynth-delays-okp))

(define vl-edgesynth-delays-okp
  :short "Check that internal delays on assignments are simple enough to
          process and compatible with one another."
  ((x vl-assigncontrols-p))
  :returns (okp booleanp :rule-classes :type-prescription)
  (and (consp x)
       (vl-edgesynth-simple-delays-p x)
       (all-equalp (vl-edgesynth-simple-delay->amount (first x))
                   (vl-edgesynth-simple-delays->amounts (rest x))))
  ///
  (defthm vl-edgesynth-simple-delays-p-when-vl-edgesynth-delays-okp
    (implies (vl-edgesynth-delays-okp x)
             (vl-edgesynth-simple-delays-p x)))
  (defthm consp-when-vl-edgesynth-delays-okp
    (implies (vl-edgesynth-delays-okp x)
             (consp x))
    :rule-classes :compound-recognizer))

(define vl-edgesynth-get-delay
  :short "Extract the shared, simple delay from the controls for the
          assignment statements."
  ((x (and (vl-assigncontrols-p x)
           (vl-edgesynth-delays-okp x))))
  :returns (maybe-natp :rule-classes :type-prescription)
  (vl-edgesynth-simple-delay->amount (car x)))


; -----------------------------------------------------------------------------
;
;                         Eliminating Begin/End Blocks
;
; -----------------------------------------------------------------------------

(defines vl-edgesynth-blockelim
  :short "Eliminate begin/end blocks and leave us with just an IF structure."

  :long "<p>Assumptions:</p>

<ul>
<li>All assignments are to the same register (call it Q).</li>
<li>At least one assignment writes to Q.</li>
<li>All assignments have compatible delays.</li>
</ul>

<p>Our goal is to eliminate any begin/end blocks and end up with just
assignments, if statements, and null statements.  For instance, we might
rewrite:</p>

@({
  begin                      if (clk1)
    q <= d3;       ----->       q <= d1;
    if (clk2)                else if (clk2)
       q <= d2;                 q <= d2;
    if (clk1)                else
       q <= d1;                 q <= d3;
  end
})"

  :hints(("Goal" :in-theory (disable (force))))
  :verify-guards nil

  (define vl-edgesynth-stmt-blockelim
    ((x    (and (vl-stmt-p x)
                (vl-edgesynth-stmt-p x))
           "Statement we're rewriting, from the top down.")
     (curr (and (vl-stmt-p curr)
                (vl-edgesynth-stmt-p curr))
           "Statement we've constructed so far, from any previous statements in
            the current begin/end block.  Could be a NULL statement if we haven't
            seen any other statements yet."))
    :returns (new-stmt vl-edgesynth-stmt-p :hyp :fguard)
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-nullstmt-p x))
          curr)

         ((when (vl-assignstmt-p x))
          ;; Since we assume every assignment is writing to the same LHS, this
          ;; new assignment overwrites anything that was previously written and
          ;; just becomes the new statement.
          x)

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x)
               (true  (vl-edgesynth-stmt-blockelim x.truebranch curr))
               (false (vl-edgesynth-stmt-blockelim x.falsebranch curr)))
            (change-vl-ifstmt x
                              :truebranch true
                              :falsebranch false)))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x))
            (vl-edgesynth-stmtlist-blockelim x.stmts curr))))

      ;; We don't support anything else
      curr))

  (define vl-edgesynth-stmtlist-blockelim
    ((x    (and (vl-stmtlist-p x)
                (vl-edgesynth-stmtlist-p x)))
     (curr (and (vl-stmt-p curr)
                (vl-edgesynth-stmt-p curr))))
    :returns (stmts vl-edgesynth-stmt-p :hyp :fguard)
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          curr)
         (curr (vl-edgesynth-stmt-blockelim (car x) curr)))
      (vl-edgesynth-stmtlist-blockelim (cdr x) curr)))

  ///
  (verify-guards vl-edgesynth-stmt-blockelim))



; -----------------------------------------------------------------------------
;
;                     Clock Decisions vs. Data Decisions
;
; -----------------------------------------------------------------------------

; Next, we are going to distinguish between clock-based and data-based IF
; tests.  The idea is to push the data-based IFs down into the statement and
; then turn them into ordinary ?: operations.  Looking at it the other way, we
; want to pull the clock-based IFs up and expose them as the top-level
; decisions that are being made.

; A first step toward this is to classify the decisions in the if/else
; hierarchy as either clock decisions or data decisions.  If a decision
; mentions both clocks and non-clock signals, then it's just too hard and we
; aren't going to try to support it.

(defenum vl-edgesynth-iftype-p
  (:clock    ;; Normal clocks, i.e.,  if (clk)
   :nclock   ;; Negated clocks, i.e., if (~clk)
   :data     ;; Non-clock signals, i.e., if (data1 & data2 | data3 ^ ...)
   :error    ;; Unsupported things, i.e., if (clk & data1), if (clk1 & clk2), ...
   )
  :short "Classifications of if tests into clock/data signals.")

(define vl-edgesynth-classify-iftest-aux
  :parents (vl-edgesynth-classify-iftest)
  :short "Walk through a clock expression, eliminating double negations."
  ((condition vl-expr-p "An expression that mentions just one clock."))
  :returns
  (mv (type vl-edgesynth-iftype-p
            "Either :clock, :nclock, or :error.")
      (guts vl-expr-p
            "Canonical version of this clock to use, with negations stripped
             from negated clocks."
            :hyp :fguard))
  :measure (vl-expr-count condition)
  (b* (((when (vl-fast-atom-p condition))
        (if (and (vl-idexpr-p condition)
                 (eql (vl-expr->finalwidth condition) 1)
                 (vl-expr->finaltype condition))
            (mv :clock condition)
          ;; Not a simple clock, not anything we support.
          (mv :error condition)))

       ;; We could eventually extend this to include things like CLK == 0 or
       ;; similar, but for now we'll keep it pretty simple:
       (op   (vl-nonatom->op condition))
       (args (vl-nonatom->args condition))

       ((when (or (eq op :vl-unary-bitor)
                  (and (eq op :vl-concat)
                       (eql (len args) 1))))
        ;; The oprewrite transform likes to stick in these silly ors.  So, if
        ;; we happen to have |clk or |~clk, treat it transparently.
        ;; It also likes to stick in unary concatenations.  They can be treated
        ;; transparently, too.
        (b* (((mv type guts) (vl-edgesynth-classify-iftest-aux (first args))))
          (if (or (eq type :clock)
                  (eq type :nclock))
              (mv type guts)
            (mv type condition))))

       ((when (member op '(:vl-unary-lognot :vl-unary-bitnot)))
        (b* (((mv type exp) (vl-edgesynth-classify-iftest-aux (first args)))
             ;; Handle the negation:
             ((when (eq type :clock))  (mv :nclock exp))
             ((when (eq type :nclock)) (mv :clock exp)))
          ;; Anything else is just not supported.
          (mv :error condition))))

    ;; Not something we understnad.
    (mv :error condition))
  ///
  (defthm vl-idexpr-p-of-vl-edgesynth-classify-iftest-aux
    (b* (((mv type guts) (vl-edgesynth-classify-iftest-aux condition)))
      (implies (or (equal type :clock)
                   (equal type :nclock))
               (and (vl-idexpr-p guts)
                    (equal (vl-expr->finalwidth guts) 1)
                    (vl-expr->finaltype guts)))))

  (local (defthmd l0
           (b* (((mv ?type guts) (vl-edgesynth-classify-iftest-aux condition)))
             (implies (vl-expr-p condition)
                      (subsetp-equal (vl-expr-names guts)
                                     (vl-expr-names condition))))
           :hints(("Goal"
                   :induct (vl-edgesynth-classify-iftest-aux condition)
                   :expand ((vl-expr-names condition))))))

  (local (defthm l1
           (implies (vl-idexpr-p x)
                    (equal (vl-expr-names x)
                           (list (vl-idexpr->name x))))
           :hints(("Goal" :in-theory (enable vl-expr-names
                                             vl-idexpr-p
                                             vl-idexpr->name)))))

  (local (in-theory (disable vl-edgesynth-classify-iftest-aux)))

  (defthm name-bound-for-vl-edgesynth-classify-iftest-aux
    (b* (((mv type guts) (vl-edgesynth-classify-iftest-aux condition)))
      (implies (and (vl-expr-p condition)
                    (or (equal type :clock)
                        (equal type :nclock)))
               (member (vl-idexpr->name guts)
                       (vl-expr-names condition))))
    :hints(("Goal" :use ((:instance l0))))))

(define vl-edgesynth-classify-iftest
  ((condition vl-expr-p    "The expression being tested by the IF.")
   (edgetable vl-edgetable-p))
  :returns
  (mv (type vl-edgesynth-iftype-p
            "The type of this condition.")
      (guts vl-expr-p
            "Canonical version of this condition, e.g., if @('condition')
             is a negated clock, we strip the negation."
            :hyp :fguard))
  (b* ((used-names (vl-expr-names condition))
       ((unless (intersectp-equal used-names (alist-keys edgetable)))
        ;; It doesn't use any clocks.  That's fine, it's just testing data
        ;; inputs.
        (mv :data condition))

       ((unless (equal (len used-names) 1))
        ;; It mentions a clock and also some other (clock or non-clock)
        ;; signals.  Too hard, not supported.
        (mv :error condition)))

    ;; We know it mentions one and only one clock, so now do some basic pattern
    ;; matching to see if it's simple enough, e.g., CLK, ~CLK, ~~CLK, etc.
    (vl-edgesynth-classify-iftest-aux condition))
  ///
  (defthm vl-idexpr-p-of-vl-edgesynth-classify-iftest
    (b* (((mv type guts) (vl-edgesynth-classify-iftest condition edgetable)))
      (implies (or (equal type :clock)
                   (equal type :nclock))
               (and (vl-idexpr-p guts)
                    (equal (vl-expr->finalwidth guts) 1)
                    (vl-expr->finaltype guts)))))

  (local (in-theory (enable vl-edgesynth-classify-iftest)))

  (local (defthm l0
           (implies (equal (len y) 1)
                    (equal (intersectp-equal x y)
                           (if (member (car y) x) t nil)))))

  (local (defthm l1
           (implies (and (equal (len x) 1)
                         (member (vl-idexpr->name a) x))
                    (equal (vl-idexpr->name a) (car x)))))

  (defrule clock-found-when-vl-edgesynth-classify-iftest
    (b* (((mv type guts) (vl-edgesynth-classify-iftest condition edgetable)))
      (implies (and (vl-expr-p condition)
                    (or (equal type :clock)
                        (equal type :nclock)))
               (hons-assoc-equal (vl-idexpr->name guts) edgetable)))
    :use ((:instance name-bound-for-vl-edgesynth-classify-iftest-aux))))



; -----------------------------------------------------------------------------
;
;                              RHS Clock Lifting
;
; -----------------------------------------------------------------------------

(define vl-edgesynth-assignstmt-clklift ((x (and (vl-stmt-p x)
                                                 (vl-assignstmt-p x)
                                                 (vl-edgesynth-stmt-p x)))
                                         (edgetable vl-edgetable-p))
  :returns (stmt vl-edgesynth-stmt-p :hyp :fguard)
  :parents (vl-edgesynth-stmt-clklift)
  (b* (((vl-assignstmt x) x)

       ((mv c a b) (vl-qmark-p x.expr))
       ((unless (and c
                     (eql (vl-expr->finalwidth c) 1)))
        ;; RHS is not of a supported form, nothing to do
        x)

       ((mv type guts) (vl-edgesynth-classify-iftest c edgetable))

       ((when (eq type :clock))
        ;; The condition is equivalent to GUTS.  And GUTS is the name of some
        ;; clock.
        ;;
        ;; LHS <= CLOCK ? A : B -->  IF (CLOCK)
        ;;                              LHS <= A
        ;;                           ELSE
        ;;                              LHS <= B
        (make-vl-ifstmt :condition guts
                        :truebranch (change-vl-assignstmt x :expr a)
                        :falsebranch (change-vl-assignstmt x :expr b)))

       ((when (eq type :nclock))
        ;; The condition is equivalent to ~GUTS, and GUTS is the name of some
        ;; clock.
        ;;
        ;; LHS <= !CLOCK ? A : B --> IF (CLOCK)
        ;;                              LHS <= B
        ;;                           ELSE
        ;;                              LHS <= A
        (make-vl-ifstmt :condition guts
                        :truebranch (change-vl-assignstmt x :expr b)
                        :falsebranch (change-vl-assignstmt x :expr a))))

    ;; Else, there's a ?: here but it's not anything we support.  Don't
    ;; bother changing it.
    x))

(defines vl-edgesynth-stmt-clklift
  :short "Lightweight rewriting to support allow us to support right-hand,
 sides such as @('reset ? 0 : data')."

  :long "<p>We generally want to prohibit clocks from occurring in right-hand
sides, e.g., we don't want to try to support things like:</p>

@({
    always @(posedge clk)
       q <= a + b + clk;
})

<p>However, it's essentially reasonable for us to test the clocks in a
@('?:') expression, such as:</p>

@({
    always @(posedge clk or posedge reset)
       q <= reset ? 0 : data;
})

<p>So as a special hack, we implement a very lightweight transform to try to
recognize simple right-hand sides of the form:</p>

@({
      clk ? a : b
     ~clk ? a : b
     !clk ? a : b
})

<p>And replace them with equivalent if-then-else statements where the clocks is
used in the condition.  I think this works even when there are delays, since
the delays affect when the update is made, not when the right hand side values
are evaluated.</p>"

  :hints(("Goal" :in-theory (disable (force))))
  :verify-guards nil

  (define vl-edgesynth-stmt-clklift ((x (and (vl-stmt-p x)
                                             (vl-edgesynth-stmt-p x)))
                                     (edgetable vl-edgetable-p))
    :returns (new-x vl-edgesynth-stmt-p :hyp :fguard)
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* (((when (vl-atomicstmt-p x))
          (cond ((vl-assignstmt-p x)
                 (vl-edgesynth-assignstmt-clklift x edgetable))
                (t
                 x)))

         ((when (vl-ifstmt-p x))
          (b* (((vl-ifstmt x) x)
               (true  (vl-edgesynth-stmt-clklift x.truebranch edgetable))
               (false (vl-edgesynth-stmt-clklift x.falsebranch edgetable)))
            (change-vl-ifstmt x
                              :truebranch true
                              :falsebranch false)))

         ((when (vl-blockstmt-p x))
          (b* (((vl-blockstmt x) x)
               (new-stmts (vl-edgesynth-stmtlist-clklift x.stmts edgetable)))
            (change-vl-blockstmt x :stmts new-stmts))))

      ;; We don't support anything else.
      x))

  (define vl-edgesynth-stmtlist-clklift ((x (and (vl-stmtlist-p x)
                                                 (vl-edgesynth-stmtlist-p x)))
                                         (edgetable vl-edgetable-p))
    :returns (new-x vl-edgesynth-stmtlist-p :hyp :fguard)
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        nil
      (cons (vl-edgesynth-stmt-clklift (car x) edgetable)
            (vl-edgesynth-stmtlist-clklift (cdr x) edgetable))))
  ///
  (verify-guards vl-edgesynth-stmt-clklift))



; -----------------------------------------------------------------------------
;
;                       Flattening Data Decisions
;
; -----------------------------------------------------------------------------

(define vl-edgesynth-merge-data-ifs
  :short "Safely merge @('if (condition) q <= d1 else q <= d2')
          into  @('q <= condition ? d1 : d2')."
  ((condition    vl-expr-p
                 "Should be a data condition.")
   (true-branch  (and (vl-stmt-p true-branch)
                      (vl-atomicstmt-p true-branch)
                      (vl-edgesynth-stmt-p true-branch))
                 "Should be @('q <= d1') or a null statement.")
   (false-branch (and (vl-stmt-p false-branch)
                      (vl-atomicstmt-p false-branch)
                      (vl-edgesynth-stmt-p false-branch))
                 "Should be @('q <= d2') or a null statement.")
   (nf           vl-namefactory-p)
   (vardecls     vl-vardecllist-p)
   (assigns      vl-assignlist-p))
  :returns
  (mv (new-stmt vl-edgesynth-stmt-p
                :hyp (and (force (vl-expr-p condition))
                          (force (vl-edgesynth-stmt-p true-branch))
                          (force (vl-edgesynth-stmt-p false-branch))
                          (force (vl-atomicstmt-p true-branch))
                          (force (vl-atomicstmt-p false-branch))))
      (nf       vl-namefactory-p
                :hyp (force (vl-namefactory-p nf)))
      (vardecls vl-vardecllist-p :hyp :fguard)
      (assigns  vl-assignlist-p :hyp :fguard))
  :long "<p>Assumption: any assignments are to the same register.</p>"
  (b* (((when (and (vl-nullstmt-p true-branch)
                   (vl-nullstmt-p false-branch)))
        ;; Probably silly: if (condition) null null --> null
        (mv true-branch nf vardecls assigns))

       ;; At least one of true-branch or false-branch is an assignment.  If
       ;; they aren't both assignments, the null statement can become Q <= Q.
       (base-assign (if (vl-assignstmt-p true-branch)
                        true-branch
                      false-branch))
       (target-reg  (vl-assignstmt->lvalue base-assign))
       (loc         (vl-assignstmt->loc base-assign))
       (width       (vl-expr->finalwidth target-reg))
       (true-rhs    (if (vl-assignstmt-p true-branch)
                        (vl-assignstmt->expr true-branch)
                      target-reg))
       (false-rhs   (if (vl-assignstmt-p false-branch)
                        (vl-assignstmt->expr false-branch)
                      target-reg))

       ;; It isn't safe to merge true-rhs and false-rhs into a single ?:
       ;; expression if they don't share size/signedness.  So make temporary
       ;; wires to deal with any truncations, etc.
       (basename                   (cat (vl-idexpr->name target-reg) "_next"))
       ((mv true-name nf)          (vl-namefactory-indexed-name basename nf))
       ((mv false-name nf)         (vl-namefactory-indexed-name basename nf))
       ((mv true-expr true-decl)   (vl-occform-mkwire true-name  width :loc loc))
       ((mv false-expr false-decl) (vl-occform-mkwire false-name width :loc loc))
       (true-assign                (make-vl-assign :lvalue true-expr
                                                   :expr   true-rhs
                                                   :loc    loc))
       (false-assign               (make-vl-assign :lvalue false-expr
                                                   :expr   false-rhs
                                                   :loc    loc))
       (vardecls (list* true-decl false-decl vardecls))
       (assigns  (list* true-assign false-assign assigns))
       (new-rhs  (vl-safe-qmark-expr condition true-expr false-expr))
       (new-stmt (change-vl-assignstmt base-assign :expr new-rhs)))
    (mv new-stmt nf vardecls assigns)))

(define vl-edgesynth-flatten-data-ifs
  :short "Flatten out bottom-level if tests about data signals, such as
            @('if (data-expr) q <= d1 else q <= d2')
          into assignments like
            @('q <= data-expr ? d1 : d2')."
  ((x         (and (vl-stmt-p x)
                   (vl-edgesynth-stmt-p x)))
   (edgetable vl-edgetable-p)
   (nf        vl-namefactory-p)
   (vardecls  vl-vardecllist-p)
   (assigns   vl-assignlist-p))
  :returns
  (mv (new-stmt vl-edgesynth-stmt-p
                :hyp (force (vl-edgesynth-stmt-p x)))
      (nf       vl-namefactory-p
                :hyp (and (force (vl-edgesynth-stmt-p x))
                          (force (vl-namefactory-p nf))))
      (vardecls)
      (assigns))
  :measure (vl-stmt-count x)
  :hints(("Goal" :in-theory (disable (force))))
  :verify-guards nil
  :long "<p>This is a best-effort transform that leaves the statement alone
when it's not supported.</p>

<p>Originally I tried to just fail when the sizes of the true/false branch
didn't line up, but that caused problems because sometimes we would see
things like:</p>

@({
    if (data-expr)
       q <= d1;
    else
       q <= 0;
})

<p>And the plain integers are badly sized.  To deal with this, we now go ahead
and do the work of introducing temporary wires as necessary.  The only lousy
part of this is that we can't really extend the @(see vl-delta-p), since we're
not sure everything's going to work out yet.</p>"

  (b* (((when (vl-atomicstmt-p x))
        (mv x nf vardecls assigns))
       ((when (vl-ifstmt-p x))
        (b* (((vl-ifstmt x) x)
             ((mv type ?guts) (vl-edgesynth-classify-iftest x.condition edgetable))
             ((mv true nf vardecls assigns)
              (vl-edgesynth-flatten-data-ifs x.truebranch edgetable
                                             nf vardecls assigns))
             ((mv false nf vardecls assigns)
              (vl-edgesynth-flatten-data-ifs x.falsebranch edgetable
                                             nf vardecls assigns))

             ((unless (and (equal type :data)
                           (vl-atomicstmt-p true)
                           (vl-atomicstmt-p false)))
              ;; Either (1) this IF is testing a clock or something too complex
              ;; that isn't supported, or (2) the rewritten branches are too
              ;; complex to merge anyway, so just install the rewritten
              ;; branches and don't do anything further.
              (mv (change-vl-ifstmt x
                                    :truebranch true
                                    :falsebranch false)
                  nf vardecls assigns)))
          (vl-edgesynth-merge-data-ifs x.condition true false
                                       nf vardecls assigns)))
       ((when (vl-blockstmt-p x))
        (raise "Thought we already got rid of block statements!")
        (mv x nf vardecls assigns)))
    ;; No other expressions are supported.
    (raise "Should be impossible.")
    (mv x nf vardecls assigns))

  ///
  ;; Nasty because we have to prove them together
  (defthm vl-edgesynth-flatten-data-ifs-basics
    (implies (and (force (vl-edgesynth-stmt-p x))
                  (force (vl-namefactory-p nf))
                  (force (vl-vardecllist-p vardecls))
                  (force (vl-assignlist-p assigns)))
             (b* (((mv ?new-x ?nf ?vardecls ?assigns)
                   (vl-edgesynth-flatten-data-ifs x edgetable nf vardecls assigns)))
               (and (vl-vardecllist-p vardecls)
                    (vl-assignlist-p assigns)))))

  (verify-guards vl-edgesynth-flatten-data-ifs))


; -----------------------------------------------------------------------------
;
;                         Normalizing IF Trees
;
; -----------------------------------------------------------------------------

(define vl-edgesynth-normalize-ifs
  :short "Try to push data IFs down, pull clock IFs up, and align the polarity
          of clock-based IFs with the edge declarations."
  ((x (and (vl-stmt-p x)
           (vl-edgesynth-stmt-p x)))
   (edgetable vl-edgetable-p))
  :returns (new-stmt vl-edgesynth-stmt-p :hyp :fguard)
  :hints(("Goal" :in-theory (disable (force))))
  :verify-guards nil
  :measure (vl-stmt-count x)
  (b* (((when (vl-atomicstmt-p x))
        x)
       ((when (vl-ifstmt-p x))
        (b* (((vl-ifstmt x) x)
             ((mv type guts) (vl-edgesynth-classify-iftest x.condition edgetable))
             (true  (vl-edgesynth-normalize-ifs x.truebranch edgetable))
             (false (vl-edgesynth-normalize-ifs x.falsebranch edgetable))

             ((when (eq type :clock))
              (b* ((clockname (vl-idexpr->name guts))
                   (edge      (cdr (hons-assoc-equal clockname edgetable)))
                   (posedgep  (vl-edgesynth-edge->posedgep edge))
                   ((when posedgep)
                    ;; always @(posedge clk) if (clk) <true> else <false>
                    ;; this is already what we want.
                    (make-vl-ifstmt :condition guts
                                    :truebranch true
                                    :falsebranch false)))
                ;; to make the if test agree with the edge, rewrite:
                ;; always @(negedge clk) if (clk) <true> else <false>
                ;;   -->
                ;; always @(negedge clk) if (!clk) <false> else <true>
                (make-vl-ifstmt :condition (vl-condition-neg guts)
                                :truebranch false
                                :falsebranch true)))

             ((when (eq type :nclock))
              (b* ((clockname (vl-idexpr->name guts))
                   (edge      (cdr (hons-assoc-equal clockname edgetable)))
                   (posedgep  (vl-edgesynth-edge->posedgep edge))
                   ((when posedgep)
                    ;; swap as above:
                    ;; always @(posedge clk) if (!clk) <true> else <false>
                    ;;  -->
                    ;; always @(posedge clk) if (clk) <false> else <true>
                    (make-vl-ifstmt :condition guts
                                    :truebranch false
                                    :falsebranch true)))
                ;; always @(negedge clk) if (!clk) <true> else <false>
                ;; this is already what we want
                (make-vl-ifstmt :condition (vl-condition-neg guts)
                                :truebranch true
                                :falsebranch false)))

             ((unless (eq type :data))
              ;; The type is :error.  No need to do anything.
              x))

          ;; Tricky case.  We have just hit a data IF.  BOZO eventually it
          ;; might be worth trying to pull up any clock-related IFS that happen
          ;; to be below us.  For now we don't try anything like that.
          x))
       ((when (vl-blockstmt-p x))
        (raise "Thought we already got rid of block statements!")
        x))
    ;; No other expressions are supported.
    (raise "Should be impossible.")
    x)
  ///
  (verify-guards vl-edgesynth-normalize-ifs))


; -----------------------------------------------------------------------------
;
;                        Final Pattern Matching
;
; -----------------------------------------------------------------------------

(local (defthm crock
         (implies (and (vl-edgesynth-stmt-p x)
                       (vl-atomicstmt-p x)
                       (not (vl-nullstmt-p x)))
                  (equal (vl-stmt-kind x) :vl-assignstmt))))

(define vl-edgesynth-pattern-match
  :short "Recognize basic if statements for the core of a multi-edge block:
          we're basically looking for a proper priority ordering on the edges."
  ((target    vl-expr-p)
   (x         (and (vl-stmt-p x)
                   (vl-edgesynth-stmt-p x)))
   (edgetable vl-edgetable-p))
  :returns
  (mv (okp     booleanp
               :rule-classes :type-prescription
               :hints(("Goal" :in-theory (disable (force)))))
      (clks    string-listp
               "Names of clocks in priority order."
               :hints(("Goal" :in-theory (disable (force)))))
      (rhses vl-exprlist-p :hyp :guard
             "Corresponding right hand sides.")
      (final-rhs vl-expr-p :hyp :guard
                 "Right-hand side for the final else statement."))

  :long "<p>We're not trying to do much sanity checking here.  We just want to
match @('x') against a basic template like:</p>

@({
    if (clk1) assign1;
    else if (clk2) null;
    else if (clk3) assign3;
    finally;
})

<p>All if-tests that we match for clocks have the proper polarity for their
corresponding edges.</p>"

  :measure (vl-stmt-count x)
  :hints(("Goal" :in-theory (disable (force))))

  (b* (((when (vl-nullstmt-p x))
        ;; Final null statement, fine, no final rhs.  Use target register as
        ;; the rhs in this case, e.g., NULL is akin to Q <= Q.
        (mv t nil nil target))

       ((when (vl-assignstmt-p x))
        ;; Final assignment, fine, grab final rhs.
        (mv t nil nil (vl-assignstmt->expr x)))

       ((unless (vl-ifstmt-p x))
        ;; Not supported
        (mv nil nil nil target))

       ((vl-ifstmt x) x)
       ((mv type guts) (vl-edgesynth-classify-iftest x.condition edgetable))

       ((when (eq type :clock))
        (b* ((clockname (vl-idexpr->name guts))
             (edge      (cdr (hons-assoc-equal clockname edgetable)))
             (posedgep  (vl-edgesynth-edge->posedgep edge))
             ((unless posedgep)
              ;; Not ok -- can't handle "@(negedge clk) if (clk) ..."
              (mv nil nil nil target))
             ((unless (vl-atomicstmt-p x.truebranch))
              ;; Not ok -- can't handle "if (clk) if ..."
              (mv nil nil nil target))
             ((mv okp clks rhses finally)
              (vl-edgesynth-pattern-match target x.falsebranch edgetable))
             ((unless okp)
              (mv nil nil nil target))
             (rhs (if (vl-nullstmt-p x.truebranch)
                      target
                    (vl-assignstmt->expr x.truebranch))))
          (mv t (cons clockname clks) (cons rhs rhses) finally)))

       ((when (eq type :nclock))
        (b* ((clockname (vl-idexpr->name guts))
             (edge      (cdr (hons-assoc-equal clockname edgetable)))
             (posedgep  (vl-edgesynth-edge->posedgep edge))
             ((when posedgep)
              ;; Not ok -- can't handle "@(posedge clk) if (!clk) ..."
              (mv nil nil nil target))
             ((unless (vl-atomicstmt-p x.truebranch))
              ;; Not ok -- can't handle "if (clk) if ..."
              (mv nil nil nil target))
             ((mv okp clks rhses finally)
              (vl-edgesynth-pattern-match target x.falsebranch edgetable))
             ((unless okp)
              (mv nil nil nil target))
             (rhs (if (vl-nullstmt-p x.truebranch)
                      target
                    (vl-assignstmt->expr x.truebranch))))
          (mv t (cons clockname clks) (cons rhs rhses) finally))))

    ;; Otherwise, some unsupported type, e.g., a data if or mixed data/clock
    ;; if, not supported.
    (mv nil nil nil target))
  ///
  (defmvtypes vl-edgesynth-pattern-match
    (nil true-listp true-listp nil)))



; -----------------------------------------------------------------------------
;
;                             Main Transform
;
; -----------------------------------------------------------------------------

(define vl-edgesynth-sort-edges ((priority-clks string-listp)
                                 (edgetable     vl-edgetable-p))
  :guard (subsetp-equal priority-clks (alist-keys edgetable))
  :returns (edgelist vl-edgesynth-edgelist-p :hyp :fguard)
  (if (atom priority-clks)
      nil
    (cons (cdr (hons-assoc-equal (car priority-clks) edgetable))
          (vl-edgesynth-sort-edges (cdr priority-clks) edgetable)))
  ///
  (defthm len-of-vl-edgesynth-sort-edges
    (equal (len (vl-edgesynth-sort-edges priority-clks edgetable))
           (len priority-clks)))
  (defthm consp-of-vl-edgesynth-sort-edges
    (equal (consp (vl-edgesynth-sort-edges priority-clks edgetable))
           (consp priority-clks)))
  (defthm vl-edgesynth-sort-edges-under-iff
    (iff (vl-edgesynth-sort-edges priority-clks edgetable)
         (consp priority-clks))))

(define vl-edgesynth-make-data-inputs
  :short "Create (if necessary) temporary wires for the data inputs."
  ((width       posp         "Width of the register.")
   (target-name stringp      "Name of the target register, for more useful
                              name generation.")
   (data-exprs vl-exprlist-p "Right-hand side expressions for data inputs.")
   (loc        vl-location-p "Location for new module elements.")
   (delta      vl-delta-p    "A delta we're extending, for assignments, new
                              nets, etc."))
  :returns
  (mv (din-exprs vl-exprlist-p :hyp :guard
                 "The new expressions to use as the data inputs.")
      (delta     vl-delta-p :hyp :guard
                 "Updated delta with any additional stuff."))
  (b* (((when (atom data-exprs))
        (mv nil delta))
       ((mv rest delta)
        (vl-edgesynth-make-data-inputs width target-name (cdr data-exprs)
                                       loc delta))
       ((when (equal (vl-expr->finalwidth (car data-exprs)) width))
        ;; No need to create a temporary wire.
        (mv (cons (car data-exprs) rest) delta))

       ;; wire [width-1:0] temp = data-expr
       ((vl-delta delta) delta)
       (nf delta.nf)
       ((mv temp-name nf)         (vl-namefactory-indexed-name (cat target-name "_din") nf))
       ((mv temp-expr temp-decl)  (vl-occform-mkwire temp-name width :loc loc))
       (temp-assign               (make-vl-assign :lvalue temp-expr
                                                  :expr (car data-exprs)
                                                  :loc loc))
       (delta (change-vl-delta delta
                               :nf nf
                               :vardecls (cons temp-decl delta.vardecls)
                               :assigns  (cons temp-assign delta.assigns))))
    (mv (cons temp-expr rest) delta))
  ///
  (defmvtypes vl-edgesynth-make-data-inputs (true-listp nil)))

(define vl-edgesynth-make-clock-inputs
  :short "Create (if necessary) temporary wires for the clock inputs."
  ((edges vl-edgesynth-edgelist-p "Priority-ordered edges, may be posedge/negedges.")
   (loc   vl-location-p           "Location for new module elements.")
   (delta vl-delta-p              "Delta we're extending."))
  :returns
  (mv (clk-exprs vl-exprlist-p :hyp :guard
                 "New clock expressions in priority order.")
      (delta     vl-delta-p :hyp :guard
                 "Extended delta."))
  :long "<p>Our primitive n-edge-flop modules are all posedge driven.  This is
where we convert any negedge signals into posedge signals.</p>"
  (b* (((when (atom edges))
        (mv nil delta))
       ((mv rest delta)
        (vl-edgesynth-make-clock-inputs (cdr edges) loc delta))
       (expr     (vl-edgesynth-edge->expr (car edges)))
       (posedgep (vl-edgesynth-edge->posedgep (car edges)))
       ((when posedgep)
        ;; That's fine, nothing to do.
        (mv (cons expr rest) delta))
       ((vl-delta delta) delta)
       (name (vl-idexpr->name expr))
       ((mv temp-name nf)        (vl-namefactory-plain-name (cat name "_bar") delta.nf))
       ((mv temp-expr temp-decl) (vl-occform-mkwire temp-name 1 :loc loc))
       (~expr                    (make-vl-nonatom
                                  :op :vl-unary-bitnot
                                  :args (list expr)
                                  :finalwidth 1
                                  :finaltype (vl-expr->finaltype expr)))
       (temp-assign              (make-vl-assign
                                  :lvalue temp-expr
                                  :expr ~expr
                                  :loc loc))
       (delta (change-vl-delta delta
                               :nf nf
                               :vardecls (cons temp-decl delta.vardecls)
                               :assigns (cons temp-assign delta.assigns))))
    (mv (cons temp-expr rest) delta))
  ///
  (defmvtypes vl-edgesynth-make-clock-inputs (true-listp nil)))

(define vl-edgesynth-create ((target         vl-expr-p)
                             (priority-edges vl-edgesynth-edgelist-p)
                             (data-exprs     vl-exprlist-p)
                             (delay          maybe-natp)
                             (loc            vl-location-p)
                             (delta          vl-delta-p)
                             &key vecp)
  :guard (and (vl-idexpr-p target)
              (posp (vl-expr->finalwidth target))
              (same-lengthp priority-edges data-exprs)
              (consp priority-edges))
  :returns (new-delta vl-delta-p :hyp :fguard)

  (b* ((width   (vl-expr->finalwidth target))
       (name    (vl-idexpr->name target))
       (nedges  (len priority-edges))

       ;; Possibly create new wires for the data inputs, to deal with any
       ;; truncations and ensure that the port sizes agree.
       ((mv data-inputs delta)
        (vl-edgesynth-make-data-inputs width name data-exprs loc delta))

       ;; Possibly add clk_bar signals for (negedge clk)s.
       ((mv clock-inputs delta)
        (vl-edgesynth-make-clock-inputs priority-edges loc delta))

       ((vl-delta delta) delta)
       (nf delta.nf)
       ((mv instname nf)               (vl-namefactory-plain-name (cat name "_inst") nf))

       ((when vecp)
        ;; vector-oriented version: everything is wrapped in the module, no extra delay assign.

        (b* ((addmods (vl-make-nedgeflop-vec width nedges (or delay 0)))
             (submod (car addmods))
             (inst (vl-simple-instantiate
                    submod instname (cons target (append data-inputs clock-inputs)))))
          (change-vl-delta delta
                           :nf nf
                           :modinsts (cons inst delta.modinsts)
                           :addmods (append addmods delta.addmods))))

       ;; Raw output of the module goes to name_delfree, the "delay-free" output.

       ;; wire [n-1:0] name_delfree;
       ((mv delfree-name nf)           (vl-namefactory-plain-name (cat name "_delfree") nf))
       ((mv delfree-expr delfree-decl) (vl-occform-mkwire delfree-name width :loc loc))

       ;; Create the appropriate implementation module and its supporting modules
       (addmods (vl-make-nedgeflop width nedges))
       (submod  (car addmods))

       ;; Make the actual instance, which drives name_delfree.
       (inst (vl-simple-instantiate submod
                                    instname
                                    (cons delfree-expr (append data-inputs clock-inputs))
                                    :loc loc))

       ;; assign #delay name = name_delfree;
       (main-ass (make-vl-assign :lvalue target
                                 :expr   delfree-expr
                                 :loc    loc
                                 :delay  (and delay
                                              (let ((amt-expr (vl-make-index delay)))
                                                (make-vl-gatedelay :rise amt-expr
                                                                   :fall amt-expr
                                                                   :high amt-expr))))))
    (change-vl-delta delta
                     :nf nf
                     :assigns  (cons main-ass delta.assigns)
                     :vardecls (cons delfree-decl delta.vardecls)
                     :modinsts (cons inst delta.modinsts)
                     :addmods  (append addmods delta.addmods)))

  :prepwork ((local (defthm car-under-iff-when-vl-modulelist-p
                      (implies (vl-modulelist-p x)
                               (iff (car x)
                                    (consp x)))))))



(defconst *edgesynth-debug* nil)

(define vl-always-edgesynth
  :short "Try to synthesize a single @('always') block."
  ((x       vl-always-p
            "Always block to synthesize.")
   (scary   string-listp
            "The @(see vl-always-scary-regs) for this module.")
   (vars    vl-vardecllist-p
            "All of the registers in the module.")
   (cvtregs string-listp
            "Accumulator for the names of registers to convert into nets.")
   (delta   vl-delta-p
            "Delta for new nets, instances, etc.")
   &key vecp)
  :returns
  (mv (new-x? (equal (vl-always-p new-x?) (if new-x? t nil))
              "nil on success, x unchanged on failure."
              :hyp :fguard)
      (cvtregs string-listp :hyp :fguard)
      (delta   vl-delta-p   :hyp :fguard))
  ;; :ignore-ok t
  ;; :irrelevant-formals-ok t
  ;; :guard-debug t
  (b* (((vl-always x) x)
       ((unless (or (eq x.type :vl-always)
                    (eq x.type :vl-always-ff)))
        ;; Don't touch this block because it's combinational or latch logic.
        (mv x cvtregs delta))

       ((mv body ?ctrl edges) (vl-match-always-at-some-edges x.stmt))
       ((unless (and body
                     (vl-edgesynth-stmt-p body)))
        ;; Don't touch this block.  It's not an edge-triggered block, or
        ;; doesn't have a body that seems simple enough.
        (mv x cvtregs delta))

       (- (and *edgesynth-debug*
               (vl-cw-ps-seq
                (vl-cw "~%~%--- Synthesizing Edge-Triggered ~a0.~%" x)
                (vl-pp-always x))))

       ;; We already know there are some clocks.  See if they're simple enough.
       (clocks (vl-evatomlist->exprs edges))
       ((unless (and (vl-idexprlist-p clocks)
                     (all-equalp 1 (vl-exprlist->finalwidths clocks))
                     (not (member nil (vl-exprlist->finaltypes clocks)))))
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because some edges are too complex.  We ~
                                   only support simple edges like @@(posedge ~
                                   clk) or @@(negedge clk), where clk is a ~
                                   one-bit expression."
                             :args (list x))))
       (edgetable (vl-make-edgetable edges))
       (clknames  (alist-keys edgetable))
       (dupeclks  (duplicated-members clknames))
       ((when dupeclks)
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because its sensitivity list has multiple ~
                                   occurrences of clock signals ~&1."
                             :args (list x clknames))))

       (assigns   (vl-edgesynth-stmt-assigns body))
       (lhses     (vl-assignstmtlist->lhses assigns))
       (controls  (vl-assignstmtlist->controls assigns))

       ;; Make sure all the assignments are writing to the same LHS register.
       ;; This should have been taken care of by edgesplit.
       (lhs-names (mergesort (vl-idexprlist->names lhses)))
       ((when (atom lhs-names))
        ;; Well, weirdly enough this is okay.  This is an edge-triggered always
        ;; block that has some if statements, begin/end blocks, and null
        ;; statements, but it has no assignments so basically it just does
        ;; nothing.  It should be fine to just throw it away.
        (mv nil cvtregs delta))

       ((unless (eql (len lhs-names) 1))
        ;; Not just a single target register, not okay.
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because more than one register gets ~
                                   written to.  Normally the edgesplit ~
                                   transform should handle this.  Did it get ~
                                   run?  Registers written: ~&1."
                             :args (list x lhs-names))))

       (target-lvalue (car lhses))
       ((unless (vl-idexpr-p target-lvalue))
        (raise "impossible")
        (mv nil cvtregs delta))

       (target-name   (vl-idexpr->name target-lvalue))
       ;; Make sure the target register is simple enough to handle.
       (w (vl-always-check-reg target-name vars x))
       ((when w)
        ;; The warning explains why we are failing.
        (mv x cvtregs (vl-warn-delta w)))
       ((when (member-equal target-name scary))
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because the target register ~w1, is ~
                                   written to by other always blocks, which ~
                                   is too scary."
                             :args (list x target-name))))
       (width (vl-expr->finalwidth target-lvalue))
       ((unless (and (posp width)
                     (all-equalp width (vl-exprlist->finalwidths lhses))))
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because the target register width is not ~
                                   consistent: ~x1."
                             :args (list x width))))

       ((unless (vl-edgesynth-delays-okp controls))
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because it uses unsupported or mixed delays."
                             :args (list x))))
       (delay (vl-edgesynth-get-delay controls))

       (- (and *edgesynth-debug*
               (vl-cw-ps-seq (vl-cw ";; Initial sanity checks pass~%"))))


       ;; Slightly rewrite the body.  It doesn't matter what order we do block
       ;; elimination and clock lifting in.  Once we've lifted the obvious
       ;; clocks out of right-hand sides, there should not be any more clocks
       ;; in any right-hand side expression.
       (body (vl-edgesynth-stmt-blockelim body (make-vl-nullstmt)))
       (- (and *edgesynth-debug*
               (vl-cw-ps-seq (vl-cw ";; After block elimination: ~%")
                             (vl-pp-stmt body))))

       (body (vl-edgesynth-stmt-clklift body edgetable))
       (- (and *edgesynth-debug*
               (vl-cw-ps-seq (vl-cw ";; After clock-lifting: ~%")
                             (vl-pp-stmt body))))

       (clocks-in-rhs
        (intersect (mergesort clknames)
                   (mergesort (vl-exprlist-names
                               (vl-assignstmtlist->rhses
                                (vl-edgesynth-stmt-assigns body))))))
       ((when clocks-in-rhs)
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because clock signals are used in the ~
                                   right-hand sides of assignments.  This ~
                                   might be a race condition: ~&1."
                             :args (list x clocks-in-rhs)
                             :fatalp nil)))

       ;; Now make basic distinctions between clock/data signals and try to do
       ;; some last minute rewriting to try to support additional blocks.


       ((mv body new-nf new-vardecls new-assigns)
        (vl-edgesynth-flatten-data-ifs body edgetable
                                       (vl-delta->nf delta)
                                       (vl-delta->vardecls delta)
                                       (vl-delta->assigns delta)))

       ;; Subtle: if we fail we don't want to change the delta.  But we have
       ;; to because we've just used its name factory.  Well, that's fine.
       ;; Blah, this is pretty messy.
       (delta     (change-vl-delta delta :nf new-nf))
       (new-delta (change-vl-delta delta
                                   :nf       new-nf
                                   :vardecls new-vardecls
                                   :assigns  new-assigns))

       (- (and *edgesynth-debug*
               (vl-cw-ps-seq (vl-cw ";; After flattening data ifs: ~%")
                             (vl-pp-stmt body))))

       (body (vl-edgesynth-normalize-ifs body edgetable))

       (- (and *edgesynth-debug*
               (vl-cw-ps-seq (vl-cw ";; After normalizing clock ifs: ~%")
                             (vl-pp-stmt body))))

       ;; BOZO maybe add other kinds of rewriting here to try to further
       ;; simplify things.

       ;; At this point we've done as much as we can to simplify the block.
       ;; Let's see if we can make sense of it.
       ((mv okp priority-clknames rhslist final-rhs)
        (vl-edgesynth-pattern-match target-lvalue body edgetable))
       ((unless okp)
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because it did not match a supported pattern."
                             :args (list x)
                             :fatalp nil)))

       ((unless (uniquep priority-clknames))
        (mv x cvtregs (dwarn :type :vl-edgesynth-fail
                             :msg "~a0: failing to synthesize always block ~
                                   because the IF structure ends up with ~
                                   multiple occurrences through ~&1."
                             :args (list x (duplicated-members priority-clknames))
                             :fatalp nil)))

       ;; We have the clocks (in priority order) and their corresponding RHSes
       ;; and a final RHS.  Something very subtle, but which I believe works
       ;; out, is that any missing clocks can just be assigned the default RHS.
       ;; Afterwards, there is no reason to worry about the default, final-rhs.
       (missing-clocks    (set-difference-equal clknames priority-clknames))
       (priority-clknames (append priority-clknames missing-clocks))
       (rhslist           (append rhslist (replicate (len missing-clocks) final-rhs)))

       ((unless (subsetp-equal priority-clknames clknames))
        (raise "Clock name problem -- this should not be possible.")
        (mv x cvtregs delta))

       (priority-edges    (vl-edgesynth-sort-edges priority-clknames edgetable))
       ((unless (and (consp priority-edges)
                     (same-lengthp priority-edges rhslist)))
        (raise "Edge/data length problem.  Should not be possible.")
        (mv x cvtregs delta))

       ;; Things look like they'll work, so extend the delta.  Use the real,
       ;; new-delta, not the unmodified original delta.
       (cvtregs           (cons target-name cvtregs))
       (delta             (vl-edgesynth-create target-lvalue priority-edges rhslist
                                               delay x.loc new-delta :vecp vecp)))
    (mv nil cvtregs delta)))


; -----------------------------------------------------------------------------
;
;             Extending Edge Synthesis across the Whole Design
;
; -----------------------------------------------------------------------------

(define vl-alwayslist-edgesynth
  :short "Extends @(see vl-always-edgesynth) to a list of always blocks."
  ((x          vl-alwayslist-p)
   (scary-regs string-listp)
   (vars       vl-vardecllist-p)
   (cvtregs    string-listp)
   (delta      vl-delta-p)
   &key vecp)
  :returns (mv (new-x   vl-alwayslist-p :hyp :fguard)
               (cvtregs string-listp    :hyp :fguard)
               (delta   vl-delta-p      :hyp :fguard))
  (b* (((when (atom x))
        (mv nil cvtregs delta))
       ((mv new-car? cvtregs delta)
        (vl-always-edgesynth (car x) scary-regs vars cvtregs delta :vecp vecp))
       ((mv new-cdr cvtregs delta)
        (vl-alwayslist-edgesynth (cdr x) scary-regs vars cvtregs delta :vecp vecp))
       (new-x (if new-car?
                  (cons new-car? new-cdr)
                new-cdr)))
    (mv new-x cvtregs delta)))

(define vl-module-edgesynth
  :short "Synthesize edge-triggered @('always') blocks in a module."
  ((x vl-module-p) &key vecp)
  :returns (mv (new-x   vl-module-p     :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((vl-module x) x)

       ((when (vl-module->hands-offp x))
        ;; Don't mess with it.
        (mv x nil))

       ((unless (consp x.alwayses))
        ;; Optimization: nothing to do, so do nothing.
        (mv x nil))

       ((when (consp x.taskdecls))
        ;; For now, just don't try to support modules with tasks.  If we want
        ;; to support this, we need to at least be able to figure out if the
        ;; tasks are writing to the registers that we're synthesizing, etc.
        (b* ((warnings (warn :type :vl-edgesynth-fail
                             :msg "~m0 has tasks, so we are not going to try to ~
                                    synthesize its always blocks."
                             :args (list x.name)
                             :acc x.warnings)))
          (mv (change-vl-module x :warnings warnings)
              nil)))

       ((when (consp x.initials))
        ;; For now, just don't try to support modules with initial statements.
        ;; They should ideally be deleted (see eliminitial) before we ever run
        ;; this transform.  The problem is that if an initial statement tries
        ;; to write to the registers that we're converting, we don't have any
        ;; good way to rewrite it to deal with the new registers, because e.g.,
        ;; in the case of:
        ;;
        ;;   reg [3:0] q;
        ;;   always @(posedge clk) q <= d;
        ;;   initial q = 0;
        ;;
        ;; Our new module will instead look like:
        ;;
        ;;   wire [3:0] q;
        ;;   wire [3:0] q_next = d;
        ;;   VL_4_BIT_FLOP q_reg (q, clk, q_next);
        ;;   initial q = 0;
        ;;
        ;; The initial statement is now wrong, because it's trying to assign a
        ;; value to q, which has become a wire instead of a reg.  So really
        ;; we'd need to change it to something like:
        ;;
        ;;  initial q_reg.q = 0;
        ;;
        ;; But that's not good enough.  The actual reg is distributed among the
        ;; VL_1_BIT_FLOPs inside of q_reg, so we'd really need something like:
        ;;
        ;;  initial { q_reg.bit_3.q, ..., q_reg.bit_0.q } = 0;
        ;;
        ;; That's getting ridiculous.  It seems reasonable to expect that they
        ;; should be removed when we're trying to do synthesis.
        (b* ((warnings
              (warn :type :vl-edgesynth-fail
                    :msg "~m0 has initial statements so we aren't going to ~
                          try to synthesize its always blocks.  Note: usually ~
                          eliminitial should be run before edgesynth, in ~
                          which case you should not see this warning."
                    :args (list x.name)
                    :acc x.warnings)))
          (mv (change-vl-module x :warnings warnings)
              nil)))

       (delta      (vl-starting-delta x))
       (delta      (change-vl-delta delta
                                    ;; We'll strictly add modinsts and assigns,
                                    ;; so pre-populate them.
                                    :modinsts x.modinsts
                                    :assigns  x.assigns))
       (scary-regs (vl-always-scary-regs x.alwayses))
       (cvtregs    nil)

       ((mv new-alwayses cvtregs delta)
        (vl-alwayslist-edgesynth x.alwayses scary-regs x.vardecls
                                 cvtregs delta :vecp vecp))

       ((vl-delta delta) (vl-free-delta delta))

       ((mv fixed-vardecls fixed-portdecls)
        (vl-convert-regs cvtregs x.vardecls x.portdecls))

       (final-vardecls (append-without-guard delta.vardecls fixed-vardecls))

       (new-x (change-vl-module x
                                :vardecls final-vardecls
                                :portdecls fixed-portdecls
                                :assigns  delta.assigns
                                :modinsts delta.modinsts
                                :alwayses new-alwayses
                                :warnings delta.warnings)))
    (mv new-x delta.addmods)))

(define vl-modulelist-edgesynth-aux ((x vl-modulelist-p) &key vecp)
  :returns (mv (new-x   vl-modulelist-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car addmods1) (vl-module-edgesynth (car x) :vecp vecp))
       ((mv cdr addmods2) (vl-modulelist-edgesynth-aux (cdr x) :vecp vecp)))
    (mv (cons car cdr)
        (append-without-guard addmods1 addmods2))))

(define vl-modulelist-edgesynth
  :short "Synthesize edge-triggered @('always') blocks in a module list,
          perhaps adding some new, supporting modules."
  ((x vl-modulelist-p) &key vecp)
  :returns (new-x :hyp :fguard
                  (and (vl-modulelist-p new-x)
                       (no-duplicatesp-equal (vl-modulelist->names new-x))))
  (b* ((dupes (duplicated-members (vl-modulelist->names x)))
       ((when dupes)
        (raise "Module names must be unique, but found multiple definitions ~
                of ~&0." dupes))
       ((mv new-x addmods)
        (vl-modulelist-edgesynth-aux x :vecp vecp))
       (all-mods (union (mergesort new-x) (mergesort addmods)))
       (dupes    (duplicated-members (vl-modulelist->names all-mods)))
       ((when dupes)
        (raise "Edgesynth caused a name collision: ~&0." dupes)))
    all-mods))

(define vl-design-edgesynth
  :short "Top-level @(see edgesynth) transform."
  ((x vl-design-p) &key vecp)
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (mods          (vl-modulelist-edgesynth x.mods :vecp vecp)))
    (change-vl-design x :mods mods)))

