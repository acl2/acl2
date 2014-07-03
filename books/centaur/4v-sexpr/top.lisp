; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; top.lisp
;   - includes all the other books
;   - gives some general overview documentation

(in-package "ACL2")
(include-book "4v-logic")
(include-book "bitspecs")
(include-book "compose-sexpr")
(include-book "g-sexpr-eval")
(include-book "nsexprs")
(include-book "onehot-rewrite")
(include-book "sexpr-advanced")
(include-book "sexpr-building")
(include-book "sexpr-equivs")
(include-book "sexpr-eval")
(include-book "sexpr-fixpoint-correct")
(include-book "sexpr-fixpoint")
(include-book "sexpr-fixpoint-rewriting")
(include-book "sexpr-fixpoint-spec")
(include-book "sexpr-fixpoint-top")
(include-book "sexpr-loop-debug")
(include-book "sexpr-rewrites")
(include-book "sexpr-to-faig")
(include-book "sexpr-purebool-p")
(include-book "sexpr-vars")
(include-book "svarmap")


(defxdoc 4v
  :parents (boolean-reasoning)
  :short "An @(see hons)-based, s-expression representation of <see
topic='@(url 4v-monotonicity)'>monotonic</see>, four-valued functions."

  :long "<p>This library defines the logic of the @(see esim) symbolic
simulator.  By \"four-valued\", we mean that each wire can take one of the four
values recognized by @(see 4vp):</p>

<ul>
 <li><b>X</b> represents \"unknown\" values</li>
 <li><b>Z</b> represents an \"undriven\" or \"floating\" value</li>
 <li><b>T</b> represents logical truth</li>
 <li><b>F</b> represents logical falsity</li>
</ul>

<p>The non-Boolean values X and Z are <see topic='@(url why-4v-logic)'>often
useful</see> when modeling hardware, and are intended to correspond to
Verilog's notions of X and Z.</p>

<p>Our logic has a fixed set of primitive @(see 4v-operations) that model, for
instance, how an AND gate behaves when given a pair of four-valued inputs.  On
top of these primitives, we use a simplified <see topic='@(url
4v-sexprs)'>s-expression syntax</see> to represent expressions in the logic.
The semantics of these s-expressions are defined by @(see 4v-sexpr-eval), a
simple evaluator that can look up variables and apply the primitive
operations.</p>

<p>A feature of our logic is that all the primitives are intrinsically <see
topic='@(url 4v-monotonicity)'>monotonic</see>, which loosely means that they
properly treat X inputs as unknowns.  The monotonicity of the primitives
carries over to the s-expressions.</p>")

(defxdoc why-4v-logic
  :parents (4v)
  :short "Motivation for using a four-valued logic."

  :long "<p>Why use a four-valued logic instead of a simple, two-valued,
Boolean logic with just T and F?</p>

<p>Having an X value is fundamental to the semantics of @(see esim), our
circuit evaluator.  Loosely speaking, when we begin simulating a circuit, all
of the internal wires are given X as their value.  We then evaluate all of the
submodule occurrences.  Because of <see topic='@(url
4v-monotonicity)'>monotonicity</see>, these evaluations can only change wires
from X to a different value.  This puts a bound on the maximum number of
evaluation steps required for the circuit's wires to reach a fixed point.</p>

<p>In the context of symbolic simulation, X values are sometimes also useful as
a way to ignore certain signals.  For instance, if we think some inputs to a
particular circuit are not even involved in the property we wish to prove, we
may leave them as X.</p>

<p>X values also allow us to model some circuits which cannot be expressed with
just Boolean logic.  For instance, imagine a scenario like:</p>

@({
         Diagram                      Verilog
          ____
         |    \\                    assign C = ~A;
   A  ---|     o------+            assign C = ~B;
         |____/       |
          ____        |-- C
         |    \\       |
   B  ---|     o------+
         |____/
})

<p>Here the wire C is being driven by two separate sources.  When these sources
have different values, e.g., suppose A is T and B is F, then C is
simultaneously driven to both F and T.  We do not know which value will
\"win,\" or, really, whether there will even be a winner.  So in this case we
just say the value of C is X.  Without an X value, we would not be able to
model this circuit.</p>

<p>The Z value allows us to model additional circuits, even beyond those
circuits that are possible to model using Xes.  In the circuit above, we did
not need a Z value because not-gates always drive at least some value onto C.
But other kinds of circuits do not necessarily drive their output.  For
instance, in Verilog one might describe a mux whose selects must be one-hot as
follows:</p>

@({
 assign C = S1 ? A : 1'bz;
 assign C = S2 ? B : 1'bz;
 ...
})

<p>By adopting Z into our logic, we can model these kinds of assignments
directly, e.g., see @(see 4v-tristate) and @(see 4v-res).</p>")


(defsection 4v-sexprs
  :parents (4v)
  :short "S-Expression representation of four-valued expressions."

  :long "<p>We represent expressions in our four-valued logic using a simple
S-Expression (sexpr) format.</p>

<p>The semantics of these expressions is given by @(see 4v-sexpr-eval).
Loosely speaking,</p>

<ul>

<li>@('NIL') is special and always evaluates to X.</li>

<li>All atoms other than @('NIL') represent variables and get their values from
an environment.</li>

<li>@('(f a1 a2 ... an)') is a function application of @('f') to arguments
@('a1') ... @('an'), where each @('ai') is itself a sexpr.</li>

</ul>

<p>Since we only have four constants, we don't permit quoted constants; instead
we just have constant functions.  That is, in any environment,</p>

<ul>
<li>@('(T)') produces T,</li>
<li>@('(F)') produces F,</li>
<li>@('(Z)') produces Z, and</li>
<li>@('(X)') produces X.</li>
</ul>

<p>We also have around a dozen functions like @('AND'), @('OR'), @('NOT'),
@('ITE'), etc., that correspond to the @(see 4v-operations).  The particular
set of understood functions are determined by @(see 4v-sexpr-eval).</p>

<p>A wonderful feature of our 4v sexpr language is that, since all of these
operations are <see topic='@(url 4v-monotonicity)'>monotonic</see>,
monotonicity is an intrinsic property of every sexpr.</p>

<p>As with our @(see aig) and <see topic='@(url ubdds)'>ubdd</see>
representations, we generally expect to create all sexprs with @(see hons), and
we often @(see memoize) operations that deal with sexprs.  We provide some
@(see 4vs-constructors) for building s-expressions.</p>")

