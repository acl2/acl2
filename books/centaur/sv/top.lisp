; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "svex/top")
(include-book "mods/top")
(include-book "vl/top")
(include-book "svtv/top")

(defxdoc sv
  :parents (acl2::hardware-verification)
  :short "A hardware verification package based on a bit-vector expression language."
  :long "<p>SVEX stands for Symbolic Vector EXpression.</p>

<p>@(see Svex) is, narrowly, an expression language of bitvectors.  More
broadly, it is a framework for representing and reasoning about hardware
modules.  Its goal is to allow a Verilog design to be translated into a
finite-state machine representation with well-defined semantics and full
observability of all parts of the original design.  It is somewhat like @(see
esim) in its goals; for a comparison, see @(see svex-esim-comparison).</p>

<h3>Basic Tutorial</h3>

<p>For basic usage of svex for datapath verification (in the style of esim
@(see symbolic-test-vectors), see @(see svex-tutorial).</p>

<h5>SVEX Expressions and @(see 4vec) Values</h5>

<p>The SVEX expression language simply consists of s-expressions with functions
applied to variables or constants.  The functions are predefined;
there are no lambdas or user-defined primitives.</p>

<p>The values on which these functions operate are @(see 4vec) objects, which
can be thought of as signed integers whose bits may take any of the four values
1, 0, X, or Z.</p>

<p>The expressions of the language are @(see svex) objects.  This is a sum of
products type with the following kinds/fields:</p>

<ul>
<li>kind @(':quote') has field @('val'), a @(see 4vec)</li>
<li>kind @(':var') has field @('name'), an @(see svar)</li>
<li>kind @(':call') has fields @('fn'), a @(see fnsym), and @('args'), an svexlist.</li>
</ul>


<h5>LHS Expressions</h5>

<p>An @(see LHS) expression is a special format representing a concatenation of
finite segments of wires (variables).  An LHS expression may be
straightforwardly converted to an svex, and a particular subset of svex
expressions may be converted to LHS expressions.</p>

<h5>SVEX Modules</h5>

<p>Svex has an associated module format; see @(see svmods) and @(see design).
Verilog designs can be converted into this format using @(see
vl::vl-design->svex-design).  Each module contains:</p>

<ul>
<li>a list of wire names and dimensions (width, lower bit index, and range direction)</li>
<li>a list of submodule instances (instance name and submodule name)</li>
<li>a list of assignments (pairings of LHS expressions and svex right-hand-sides)</li>

<li>a list of aliases (pairings of LHS expressions), representing port
connections and any other constructs that cause a single wire to have more than
one name</li>
</ul>

<h5>FSM Conversion</h5>

<p>A hardware design may be expressed hierarchically as an svex @(see design),
but for reasoning usually it is best to have a finite-state machine
representation; that is, a set of states with update functions and a set of
outputs with value functions, each in terms of inputs and previous states.  See
@(see svex-compilation) for a description of the process of obtaining an FSM
representation from a hierarchical one.</p>

<h5>Rewriting and Masks</h5>

<p>The svex library contains a rewriting routine, @(see svex-rewrite), that
applies a series of rules in order to simplify expressions.  The rewriter is
unconditional and memoized so that it runs in time linear in the size of the
expression set.  The rewrite rules are somewhat conservative in that they are
careful to avoid transformations that might increase the total number of nodes.
The rewriter uses a table of bitmasks that signify which bits of each
subexpression are used; for example, if we have a concatenation
@({
  (concat 4 a b)
 })
but the mask for this subexpression is, say, 5 -- which has no bits set past
the lowest 4 -- then this expression may be rewritten to just @('a').</p>

<h5>Composition and Apparent Loops</h5>

<p>Most of the time, expressions may be composed together into full update
functions by recursively traversing them down to the variables and replacing
the variables the update functions produced by recurring on their assigned
expressions.  However, because our variables represent multi-bit vectors,
sometimes a variable appears to depend on itself.  We then must stop this
process early and leave an unresolved non-input variable in the update
functions; otherwise the process would not terminate.  However, we can get rid
of these self-looping variables in the cases where there is no dependency of
any bit of the variable on itself, only dependencies among different bits.  In
this case, we can use the care-masks introduced in the previous section to
determine how many times we need to unroll the expression in order to eliminate
the apparent self-dependency.</p>

<h5>Symbolic Execution and Translation to AIGs</h5>

<p>See @(see svex-symbolic-evaluation).  The book \"symbolic.lisp\" provides a
connection to GL that allows symbolic evaluations of SVEXes to be done by
translating the svexes into AIGs and composing those AIGs with the symbolic
representations of the variable bindings.</p>

<h5>Decomposition Proofs</h5>

<p>See @(see svex-decomp).  The book \"decomp.lisp\" provides automation for
proving that a composition of several slices of a circuit are equivalent to a
whole circuit.</p>

")



(defxdoc symbolic-test-vector
  :parents (sv)
  :short "An object describing a finite run of a hardware model."
  :long "
<p>Originally, symbolic test vectors (STVs) were conceived as an aid to
concretely and symbolically simulating E/@(see esim) modules.  Now, a similar
library exists for <see topic='@(url sv)'>@(csym svex)</see> which is
nearly a drop-in replacement for @(see esim) STVs.  See @(see
acl2::symbolic-test-vectors) for description of the original esim-based
library, and @(see svex-stvs) for a description of the differences in the new
svex version.</p>")

(defxdoc svex-esim-comparison
  :parents (sv)
  :short "Similarities and differences between the <see topic='@(url
sv)'>@(csym svex)</see> and @(csee esim) packages"
  :long " <p>Svex and esim largely share the same goal: to provide a
representation for (RTL) hardware designs that can be automatically derived
from Verilog/SystemVerilog and can be concretely or symbolically simulated.
Historically, esim is a successor to the E language of Hunt &amp; Boyer, which is
in turn descended from DE2 (Hunt &amp; Reeber) and DUAL-EVAL (Hunt &amp; Brock).</p>

<p>Below we discuss some of the differences between Svex and Esim, and their
motivations.</p>

<h3>Vector-level expression language</h3>

<p>The expression language used by esim is @(see 4v), in which each expression
just represents a single bit (though like in Verilog, it may take 4 values, 1,
0, X, or Z).  In the svex language, each expression represents a (4-valued) bit
vector, somewhat similar to a bignum representation.  (In fact, the values
taken by svex expressions are represented by @(see 4vec) structures, each of
which is essentially a pair of integers.)</p>

<p>The motivation for this change was to make it easier to translate large
Verilog/SystemVerilog models with reasonable performance.  In esim,
bit-blasting every expression has been a major performance bottleneck.  A
vector-level expression language also may lends itself to more specialized
reasoning strategies than just bit-blasting, although bit-blasting is also
supported by svex (see @(see svex-symbolic-evaluation)).</p>

<h3>Expression-level module representations</h3>

<p>In the esim module representation, each module is either a primitive (which
has an explicit representation of outputs/next-states in terms of
inputs/previous-states) or simply a bundle of submodules.  This means that to
translate a typical Verilog module containing assignments as well as
submodules, the assignments first needed to be broken down and represented as a
series of submodules themselves, in the @(see split) and @(see occform)
transformations.  In svex, we eliminate this process by directly representing
assignments of expressions to wires in the modules; this removes the need for
these two steps.</p>

<h3>Flattening</h3>

<p>One advantage of esim is that the semantics of a module hierarchy are
relatively straightforward and well-defined: each module has its output and
next-state functions in terms of its inputs and previous states, and the
functions for a parent module are computed by taking a fixpoint of the
compositions of the functions of all submodules.</p>

<p>In svex, rather than expressing the semantics in terms of a module
hierarchy, only the expression language has a real concrete interpretation.  To
obtain the meaning of a module hierarchy, we first flatten it and resolve
aliasing between wires, obtaining a flattened set of assignments and state
updates.  We then compose these together to obtain update functions for each
wire and state element in terms of primary inputs and previous states.</p>

<p>While arguably some meaning is lost here -- the flattening and
alias-normalization transforms are sufficiently complicated that we can't argue
that the module hierarchy has a well-defined semantics -- an important
advantage is that this process offers a much simpler way to deal with Verilog
constructs that violate the module hierarchy, such writes to hierarchical
identifiers.  This sort of construct can't be accommodated in esim without
drastically modifying its simple, elegant hierarchical semantics.
Additionally, esim support for bidirectionally-driven wires relies on a
complicated, unverified transformation to the module hierarchy, necessary to
ensure a fundamental assumption that every wire has only one driving module.
With flattening, a wire that is bidirectionally driven reduces to one that is
just multiply driven, and it is relatively easy to resolve any multiply-driven
wires after flattening and before composition.</p>

<h3>SystemVerilog support</h3>

<p>The flattening/alias-normalization/composition flow for deriving an FSM
representation from a module hierarchy has proven to be very convenient for
expressing new SystemVerilog features such as compound data structures.  For
this reason, some SystemVerilog support is now present in svex and more is
planned, whereas no further features are planned for esim development.</p>")
