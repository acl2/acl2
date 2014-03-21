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

#||

;; BOZO temporary junk, not working yet


(include-book "../../mlib/expr-tools")
(include-book "../../mlib/welltyped")
(include-book "../../mlib/stmt-tools")
(local (include-book "../../util/arithmetic"))

; Recognizers for valid edgecode programs

(defxdoc edgecode
  :parents (synthalways)
  :short "Core subset of Verilog statements that we support for synthesizing
edge-triggered @('always') blocks."

  :long "<p>This is a \"final,\" back-end transformation for synthesizing
edge-triggered always blocks into primitives.  In this transform, we support
only a limited subset of Verilog statements which we call <b>edgecode
programs</b>.  Below, we describe this subset and roughly explain how we
synthesize supported @('always') blocks.</p>

<p>Note that, altogether, VL can handle a richer subset of Verilog statements
than we are about to describe.  Other transforms like @(see stmtrewrite) can
reduce these richer statements into simple edgecode equivalents.  You can think
of edgecode as a sort of back-end mini language that is meant to be rich enough
to target and yet simple enough to synthesize in a sensible way.</p>

<p>Unlike many VL transforms, the output from this transformation is generally
unsuitable for use with ordinary Verilog simulators.  Instead, the reduced
Verilog we produce is meant for use with back-end tools that support certain
finite-state-machine style semantics.</p>


<h3>Preliminaries: Edge-Triggered Blocks, Clocks</h3>

<p><u>Definition.</u> We say that an @('always') block is <b>edge-triggered</b>
when it contains a <see topic='@(url timing-statement)'>timing-statement</see>
whose control is a list of @('posedge') or @('negedge') events.  As
examples:</p>

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

<p>We will assume throughout this discussion that we are attempting to
synthesize an edge-triggered always block; other kinds of @('always') blocks
may be supported by other VL transforms, but are beyond the scope of the
edgecode transform.</p>

<p>Earlier versions of VL only supported a single @('posedge') edge.  But we
now support arbitrary lists of @('posedge') and @('negedge') edges, in any
mixture.  That is, we now support always blocks such as:</p>

@({
 always @(posedge a or negedge b or posedge c or ...)
 begin
   <edgecode-program>                         // explained below
 end
})


<p><u>Definition</u>.  We say that the <b>clocks</b> of such an always block
are the expressions in the sensitivity list, regardless of whether they are
used with @('posedge') or @('negedge') specifiers.  For instance:</p>

@({
 // example:                                  // clocks (expressions)
 always @(posedge clk) ...;                   //   clk
 always @(posedge mclk or negedge reset) ...; //   mclk, reset
 always @(posedge a & b or posedge c[0]) ...; //   a & b, c0
})

<p>We only support always blocks whose clocks are each <b>one-bit wide</b>.
This restriction is meant to avoid mismatches between VL and other Verilog
tools&mdash;we found disagreement between Verilog tools regarding what
constitutes an edge for a wide signal, and at any rate it would be quite
strange to ask about the edge of a wide signal.</p>


<p><u>Definition</u>.  We say that a clock (expression) is <b>simple</b> if it
is a plain identifier, i.e., it meets the @(see vl-idexpr-p) criteria.  For
instance, in the above examples, @('clk'), @('mclk'), and @('reset') are simple
clocks; but @('a & b') and @('c[0]') are non-simple.</p>

<p>We support both simple and non-simple clocks to some degree.  However,
non-simple clocks are subject to additional restrictions, as described
below.</p>


<h3>Edgecode Programs</h3>

<p>An edgecode program is a @(see vl-stmtlist-p) that meets several
restrictions.  Here is an example edgecode program:</p>

@({
 a <= x0;
 a <= (x1 & x2) | x3;
 if (c2) a <= x2;
 if (c2) a <= x3;
 if (c3 & c4) a <= x4;
 a <= x5 & 1;
})

<p>Here are some \"local\" requirements on every statement within an edgecode
program:</p>

<ul>

<li>All expressions have their widths and types computed.</li>

<li>Every assignment must be a non-blocking, i.e., it uses @('<=') instead of
@('=').</li>

<li>Every assignment must be to a simple identifier, i.e., the left-hand side
is not something like @('a[3]').</li>

<li>Every assignment must be either control-free or have a simple delay
control, i.e., @('#5').</li>

<li>Top-level @(see if-statements) are allowed, but the @('true') branch must
be an assignment and the @('else') branch must be a @(see vl-nullstmt-p).  In
other words, there really aren't any @('else') statements.</li>

<li>No other statements are allowed.  That is, every statement is either an
assignment, or one of these simple if statements.</li>

</ul>

<p>There are some \"global\" requirements on the program:</p>

<ul>

<li>There must be at least one statement.</li>

<li>Every assignment is to the same identifier.  For instance, notice above
that every assignment writes to @('a').  We'll call this the <b>target
register</b> of the program.</li>

<li>Every assignment must have the same delay.</li>

<li>All lhses/rhses must have the same width.</li>

<li>No right-hand side of any assignment may mention any identifier used in any
non-simple clock.</li>

</ul>

<p>We also require that:</p>

<ul>

<li>The target register of @('prog') must be defined as a <tt>reg</tt> in the
module; it must be a simple register, i.e., not an array, etc.</li>

<li>No other always blocks may write to the target register.</li>

</ul>


<h3>Edgecode Synthesis</h3>

<p>Despite the many restrictions above, edgecode programs are still difficult
to synthesize in a way that is completely faithful to the Verilog semantics.
Our treatment of these always blocks differs from the Verilog semantics in some
important ways.</p>

<h5>If Optimism</h5>

<p>One basic problem is the unwarranted optimism of @('if') statements.  That
is, in the Verilog semantics, a statement like @('if (en) q <= d') causes an
update to @('q') only if @('en') evaluates to 1.  If @('en') instead evaluates
to X or Z, the @('if') statement treats it as having evaluated to false and
does not update @('q').  This is generally bad because it fails to properly
treat X as an unknown.</p>

<p>When we synthesize these always blocks for use with properly monotonic
back-ends like @(see esim), where X really does represent an unknown, we have
no way to model this kind of optimism.  Instead, roughly speaking, we are going
to treat these statements like @('?:') operators, which have safer (though
different) X behavior.  That is, in our semantics, when @('en') evaluates to X
or Z, we may write an X value into @('q') instead of failing to update it.</p>

<p>We cannot see any way to avoid this kind of mismatch.  We generally regard
the VL behavior as more reasonable and safer.  But one can imagine that if,
say, @('q') is fed into other @('if') statements, then the Verilog simulator
could go produce completely different results than, say, an esim-based
simulation.</p>

<h5>Timing Nuances</h5>

<p>A much more subtle and tricky problem is the event-based Verilog timing
model.  To illustrate this, compare the following examples:</p>

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

<p>You might expect these to behave the same, but unfortunately Version 2 has a
race condition: suppose @('clk') is held high while @('reset') transitions from
low to high.  This change requires that two separate events be scheduled: the
@('assign') and the @('always') block.  Since these events may occur in any
order, we may find that either:</p>

<ul>

<li>The @('assign') statement happens first, so @('q_next') \"properly\" is
updated to 0 before the @('always') block updates it to @('q'), or</li>

<li>The @('always') statement happens first, so @('q_next') \"improperly\" has
the old value of @('data') when we assign it to @('q').</li>

</ul>

<p>In contrast, version 1 does not suffer from this problem and will always
\"properly\" reset @('q') in this scenario.  The main reason for this is that
there are no competing events are triggered by the transition of @('reset');
only the single @('always') block must be run.</p>

<p>In general, <i>any</i> signal used in the right-hand side of an assignment
within the @('always') block can have a race with @('reset'). 





  (If you run these on a Verilog simulator and find
that they simulate in the same way, try reordering the assignment and the
always block and you may get a different result.)</p>









  Challenges arise due to both the subtle and tricky
timing semantics of Verilog, and to the poor unknown handling in Verilog's if
statements.</p>


The Verilog timing model is very complex.synthesis of
edgecode programs difficult.

Many of the considerations of how to synthesize an edgecode block are derived
from the Verilog timing model.






(define vl-flopcodeassign-p ((x vl-assignstmt-p))
  :parents (vl-flopcodestmt-p)
  (b* (((vl-assignstmt x) x))
    (and (eq x.type :vl-nonblocking)
         (vl-idexpr-p x.lvalue)
         (or (not x.ctrl)
             (and (mbe :logic (vl-delaycontrol-p x.ctrl)
                       :exec (eq (tag x.ctrl) :vl-delaycontrol))
                  (vl-simpledelaycontrol-p x.ctrl)))
         (vl-expr-welltyped-p x.lvalue)
         (vl-expr-welltyped-p x.expr)
         (posp (vl-expr->finalwidth x.lvalue))
         (posp (vl-expr->finalwidth x.expr))
         (int= (vl-expr->finalwidth x.lvalue)
               (vl-expr->finalwidth x.expr)))))

(define vl-flopcodestmt-p ((x vl-stmt-p))
  :parents (flopcode)
  :short "Recognizer for flopcode statements."

  :long "<p>Every @(see flopcode) statement matches one of the following
forms:</p>

<ul>
<li>@('lhs <= [#(delay)] rhs')</li>
<li>@('if (test) lhs <= [#(delay)] rhs')</li>
</ul>

<p>It is convenient to define accessors to deal with flopcode statements in a
uniform way:</p>

<ul>

<li>@(call vl-flopcodestmt->test) returns the @('test') for conditional
flopcode assignments, or @('nil') for unconditional statements.</li>

<li>@(call vl-flopcodestmt->lhs) returns the @('lhs') in either case.</li>

<li>@(call vl-flopcodestmt->rhs) returns the @('rhs') in either case.</li>

<li>@(call vl-flopcodestmt->delay) returns the delay amount, a natural number
or @('nil') for no delay.</li>

</ul>"

  (b* (((when (vl-fast-atomicstmt-p x))
        (and (vl-fast-assignstmt-p x)
             (vl-flopcodeassign-p x)))
       ((unless (vl-ifstmt-p x))
        nil)
       ((vl-ifstmt x) x))
    (and (vl-assignstmt-p x.truebranch)
         (vl-flopcodeassign-p x.truebranch)
         (vl-nullstmt-p x.falsebranch)
         (vl-expr->finaltype x.condition)
         (vl-expr-welltyped-p x.condition)
         (eql (vl-expr->finalwidth x.condition) 1))))

(define vl-flopcodestmt->test ((x (and (vl-stmt-p x)
                                       (vl-flopcodestmt-p x))))
  :returns (test :hyp :fguard
                 (and (equal (vl-expr-p test) (if test t nil))
                      (implies test
                               (and (equal (vl-expr->finalwidth test) 1)
                                    (vl-expr->finaltype test)
                                    (vl-expr-welltyped-p test)))))
  :parents (vl-flopcodestmt-p)
  :inline t
  (and (vl-fast-compoundstmt-p x)
       (vl-ifstmt->condition x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p)))))

(define vl-flopcodestmt->lhs ((x (and (vl-stmt-p x)
                                      (vl-flopcodestmt-p x))))
  :returns (lhs :hyp :fguard (and (vl-expr-p lhs)
                                  (vl-idexpr-p lhs)
                                  (vl-expr-welltyped-p lhs)))
  :parents (vl-flopcodestmt-p)
  :inline t
  (if (vl-fast-compoundstmt-p x)
      (vl-assignstmt->lvalue (vl-ifstmt->truebranch x))
    (vl-assignstmt->lvalue x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p))))
  ///
  (defthm vl-flopcodestmt->lhs-width
    (implies (and (force (vl-stmt-p x))
                  (force (vl-flopcodestmt-p x)))
             (posp (vl-expr->finalwidth (vl-flopcodestmt->lhs x))))
    :rule-classes :type-prescription))

(define vl-flopcodestmt->rhs ((x (and (vl-stmt-p x)
                                      (vl-flopcodestmt-p x))))
  :returns (rhs :hyp :fguard
                (and (vl-expr-p rhs)
                     (vl-expr-welltyped-p rhs)
                     (equal (vl-expr->finalwidth rhs)
                            (vl-expr->finalwidth (vl-flopcodestmt->lhs x)))))
  :parents (vl-flopcodestmt-p)
  :inline t
  (if (vl-fast-compoundstmt-p x)
      (vl-assignstmt->expr (vl-ifstmt->truebranch x))
    (vl-assignstmt->expr x))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p
                                       vl-flopcodestmt->lhs)))))

(define vl-flopcodestmt->delay ((x (and (vl-stmt-p x)
                                        (vl-flopcodestmt-p x))))
  :returns ticks
  :parents (vl-flopcodestmt-p)
  :inline t
  (b* (((vl-assignstmt ass) (if (vl-fast-compoundstmt-p x)
                                (vl-ifstmt->truebranch x)
                              x)))
    (and ass.ctrl
         (vl-simpledelaycontrol->ticks ass.ctrl)))
  :prepwork ((local (in-theory (enable vl-flopcodestmt-p
                                       vl-flopcodeassign-p))))
  ///
  (defthm vl-maybe-natp-of-vl-flopcodestmt->delay
    (vl-maybe-natp (vl-flopcodestmt->delay x))
    :rule-classes :type-prescription))


(deflist vl-flopcodestmtlist-p (x)
  (vl-flopcodestmt-p x)
  :guard (vl-stmtlist-p x)
  :elementp-of-nil nil
  :parents (flopcode))

(defprojection vl-flopcodestmtlist->tests (x)
  (vl-flopcodestmt->test x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :parents (vl-flopcodestmtlist-p))

(defprojection vl-flopcodestmtlist->lhses (x)
  (vl-flopcodestmt->lhs x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-exprlist-p
  :parents (vl-flopcodestmtlist-p)
  :rest
  ((defthm vl-idexprlist-p-of-vl-flopcodestmtlist->lhses
     (implies (and (force (vl-stmtlist-p x))
                   (force (vl-flopcodestmtlist-p x)))
              (vl-idexprlist-p (vl-flopcodestmtlist->lhses x))))))

(defprojection vl-flopcodestmtlist->rhses (x)
  (vl-flopcodestmt->rhs x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-exprlist-p
  :parents (vl-flopcodestmtlist-p)
  :rest
  ((defthm vl-exprlist->finalwidths-of-vl-flopcodestmtlist->rhses
     ;; This holds because we require the widths to agree on the lhs/rhs in
     ;; vl-flopcodestmt-p.  This is important in vl-flopcode-next-expr.
     (implies (and (force (vl-stmtlist-p x))
                   (force (vl-flopcodestmtlist-p x)))
              (equal (vl-exprlist->finalwidths (vl-flopcodestmtlist->rhses x))
                     (vl-exprlist->finalwidths (vl-flopcodestmtlist->lhses x)))))))

(defprojection vl-flopcodestmtlist->delays (x)
  (vl-flopcodestmt->delay x)
  :guard (and (vl-stmtlist-p x)
              (vl-flopcodestmtlist-p x))
  :result-type vl-maybe-nat-listp
  :parents (vl-flopcodestmtlist-p))



(define vl-flopcodeprog-p ((x vl-stmtlist-p))
  :parents (flopcode)
  :short "Extends the local @(see vl-flopcodestmtlist-p)s checks with the
global requirements for flopcode programs."
  (b* (((unless (vl-flopcodestmtlist-p x))
        nil)
       (lhses (vl-flopcodestmtlist->lhses x))
       ((unless lhses)
        ;; Not a valid flop program since there isn't even one statement.
        nil)
       (lhs1   (car lhses))
       (name1  (vl-idexpr->name lhs1))
       (width1 (vl-expr->finalwidth lhs1))
       (delays (vl-flopcodestmtlist->delays x))
       (delay1 (car delays)))
    (and (all-equalp name1  (vl-idexprlist->names lhses))
         (all-equalp width1 (vl-exprlist->finalwidths lhses))
         (all-equalp delay1 delays)))
  ///
  (defthm consp-when-vl-flopcodeprog-p
    (implies (vl-flopcodeprog-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (defthm vl-flopcodestmtlist-p-when-vl-flopcodeprog-p
    (implies (vl-flopcodeprog-p x)
             (vl-flopcodestmtlist-p x))))

(define vl-flopcodeprog->target ((x (and (vl-stmtlist-p x)
                                         (vl-flopcodeprog-p x))))
  :returns (target :hyp :fguard (and (vl-expr-p target)
                                     (vl-idexpr-p target)
                                     (vl-expr-welltyped-p target)))
  :parents (vl-flopcodeprog-p)
  :short "Get the target register from a valid flopcode program."
  :inline t
  (vl-flopcodestmt->lhs (car x))
  ///
  (defthm vl-expr->finalwidth-of-vl-flopcodeprog->target
    (implies (and (force (vl-stmtlist-p x))
                  (force (vl-flopcodeprog-p x)))
             (posp (vl-expr->finalwidth (vl-flopcodeprog->target x))))
    :rule-classes :type-prescription))

(define vl-flopcodeprog->delay ((x (and (vl-stmtlist-p x)
                                        (vl-flopcodeprog-p x))))
  :returns ticks
  :parents (vl-flopcodeprog-p)
  :short "Get the delay for each assignment in a valid flopcode program."
  :inline t
  (vl-flopcodestmt->delay (car x))
  ///
  (defthm vl-maybe-natp-of-vl-flopcodeprog->delay
    (vl-maybe-natp (vl-flopcodeprog->delay x))
    :rule-classes :type-prescription))

||#