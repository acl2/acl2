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
(include-book "svtv/new-svtv-top")

(defxdoc sv
  :parents (hardware-verification)
  :short "SV is a hardware verification library that features a vector-based
expression representation (@(see svex)), efficient symbolic simulation that is
integrated with @(see gl), and support for many SystemVerilog features.  It
generally replaces @(see esim) as a backend for @(see vl)."

  :long "

<box><p><b><color rgb='#ff0000'>ALPHA VERSION</color></b>.  SV is not yet ready
for public use and may change in drastic ways without any warning.  Users who
want to be on the bleeding edge should follow the github project to try to keep
up to date.</p></box>


<p><b>SV</b> is an ACL2 library for hardware verification, developed
at <a href='http://www.centtech.com/'>Centaur Technology</a>, primarily by Sol
Swords.  It is the latest in a long line of hardware description languages that
are deeply embedded within ACL2: it replaces Centaur's @(see esim), which
itself succeeded the E language of Hunt &amp; Boyer, which was a descendant of
DE2 (Hunt &amp; Reeber), which followed from DUAL-EVAL (Hunt &amp; Brock).  For
a brief comparison, see @(see sv-versus-esim).</p>

<p>SV combines and integrates several major components:</p>

<ol>

<li><b>Expression language</b>.  At its core, SV is based on a language of
symbolic @(see expressions) that represent functions over infinite-width
vectors of four-valued ``bits.''  We define a sensible semantics for these
expressions (@(see svex-eval)) and implement tools like @(see rewriting) for
simplifying these expressions in provably sound ways.  We also provide special
support for bit-blasting SV expressions with @(see gl), which allows you to
process them with efficient @(see acl2::boolean-reasoning) tools like @(see
acl2::aignet), @(see acl2::satlink), @(see acl2::ubdds), etc.</li>

<li><b>Modules and compilation</b>.  SV has a simple, @(see svex)-based
representation for hardware modules.  It also has a compiler that can assemble
these modules into a convenient finite state machine (FSM) representation, with
well-defined semantics, and with full observability of all parts of the
original design.  This compilation process involves, e.g., flattening the
module hierarchy, resolving multiply driven wires, etc.; see @(see
svex-compilation).</li>

<li><b>SystemVerilog/Verilog loading</b>.  SV is integrated with @(see vl) so
that you can translate SystemVerilog and Verilog designs into its internal SV
representation.  In practice, this is the main way to get the SV modules to
analyze.</li>

<li><b>Proof development and debugging</b>.  SV provides tools like @(see
svex-stvs)s for running modules, which allow you to supply inputs and extract
outputs at particular times.  These user-interfacing tools can be used in ACL2
theorems and provide debugging conveniences such as generating VCD files for
use with waveform viewers.</li>

</ol>

<p>This documentation is mainly a reference.  New users should probably start
with the @(see sv-tutorial), which gives a tour of using SV to verify some
simple Verilog designs.  (This tutorial will be quite familiar if you have used
@(see esim) in the past.)</p>")

(defxdoc sv-versus-esim
  :parents (sv)
  :short "A quick comparison of @(see sv) and its predecessor, @(see esim)."

  :long "<p>SV and ESIM have many similarities.  For instance:</p>

<ul>

<li>They largely share the same goal: to provide a representation for (RTL)
hardware designs that can be automatically derived from Verilog/SystemVerilog,
can be concretely or symbolically simulated, and can be formally analyzed by
ACL2.</li>

<li>They are both, like Verilog or SystemVerilog, based on four-valued logics
where each ``bit'' of a wire can be either 1, 0, X, or Z; see @(see
acl2::why-4v-logic) for additional background on why four-valued logics are
useful in hardware modeling.</li>

<li>They both provide similar user-interfacing tools.  For instance, the @(see
sv::symbolic-test-vector)s of SV are intentionally very similar to the symbolic
test vectors of ESIM.</li>

</ul>

<p>However, SV and ESIM have significantly different implementations.  Below,
we discuss some of these differences, their motivations, and their
consequences.</p>


<h3>Expression Language</h3>

<p>ESIM is a <b>bit-level</b> backend.  That is, the expression language used
by ESIM is @(see 4v).  Each expression in this language represents a
single (four-valued) bit.</p>

<p>In contrast, SV is a <v>vector-level</v> backend.  In its expression
language, @(see svex), each expression represents a (4-valued) bit vector,
somewhat similar to a bignum representation.  In particular, the values taken
by its expressions are represented by @(see 4vec) structures, each of which is
essentially a pair of integers.</p>

<p>The main motivation for this change was to make it easier to translate large
Verilog/SystemVerilog designs with reasonable performance.  In ESIM,
bit-blasting every expression has proven to be a major performance
bottleneck...</p>

<ul>

<li>In some cases it requires the creation of millions of symbols.  This could
be slow just to @(see intern).  We typically built ACL2 with a much larger
@('ACL2') @(see package) to improve performance.</li>

<li>These symbols were (of course) then consed together into various
structures, which could become large and require lots of memory to
represent (and to @(see hons)).</li>

<li>We needed separate expressions for each bit of the circuit.  For instance,
an assignment like @('assign foo[7:0] = bar[7:0] & baz[7:0]') would require
eight separate, distinct @('and') expressions, i.e., @('(and bar[7] baz[7])'),
@('(and bar[6] baz[6])'), ...; each of these were @(see acl2::4v-sexprs), which
were typically @(see hons)es, so there is a significant memory cost.</li>

<li>Traversing so many individual bit expressions adds significant time
overhead for algorithms such as evaluating, reducing, topologically sorting and
composing update functions, etc., as well as much larger memo tables.</li>

<li>It takes some memory to record the association of Verilog-level vectors to
their corresponding bits, and some computation to reassemble vectors out of
their bits, which you need to do in tools like waveform dumping and symbolic
test vector processing.</li>

<li>There are other undesirable consequences for the front-end (i.e., Verilog
translation), which we will come back to later.</li>

</ul>

<p>A vector-level language largely avoids these problems.  Since each variable
represents an entire vector, we need far fewer symbols and expressions, and
correspondingly far less memory is needed to represent structures such as the
state of the circuit at a particular instant in time and its update functions.
The symbolic expressions for our update functions are also more compact,
requiring less memory for memo tables and less time for traversals.  We don't
need to track associations between vectors and their individual bits for
waveforms/etc., which further reduces memory overhead and computation time.</p>

<p>A vector-level expression language also may lend itself to more specialized
reasoning strategies than just bit-blasting.  @(see Bit-blasting) is still an
important tool and is still well-supported by SV, but delaying bit-blasting
opens up opportunities for certain kinds of vector-level analysis such as @(see
rewriting).</p>




<h3>Module Representations</h3>

<p>In ESIM's module representation, each module is either:</p>

<ul>

<li>a primitive, defined by an explicit representation of outputs/next-state
bits in terms of inputs/previous-states, or</li>

<li>a compound module, defined by a list of submodule instances.</li>

</ul>

<p>This approach meant that to translate a typical Verilog module containing
assignments as well as submodules, the assignments first needed to be broken
down and represented as a series of submodules themselves.  Historically this
was done by @(see vl2014) transforms such as in the @(see vl2014::split) and
@(see vl2014::occform).</p>

<p>In SV, we eliminate this process by directly representing assignments of
expressions to wires in the modules; this removes the need for these two steps,
and helps to make the actual SV representation look more like the original
Verilog.  (Well, slightly, anyway.)</p>


<h3>Flattening</h3>

<p>One advantage of ESIM's module representation is that the semantics of a
module hierarchy are relatively straightforward and well-defined: each module
has its output and next-state functions in terms of its inputs and previous
states, and the functions for a parent module are computed by taking a fixpoint
of the compositions of the functions of all submodules.</p>

<p>In SV, rather than expressing the semantics in terms of a module hierarchy,
only the expression language has a real concrete interpretation.  To obtain the
meaning of a module hierarchy, we first <b>flatten</b> it and resolve aliasing
between wires, obtaining a flattened set of assignments and state updates.  We
then compose these together to obtain update functions for each wire and state
element in terms of primary inputs and previous states.</p>

<p>While arguably some meaning is lost here&mdash;the flattening and
alias-normalization transforms are sufficiently complicated that we can't claim
that the module hierarchy has a nice, crisp semantics&mdash;an important
advantage is that this process offers a much simpler way to deal with Verilog
constructs that violate the module hierarchy.  For example, consider a Verilog
assignment to a hierarchical identifier.  This sort of construct can't be
accommodated in ESIM without drastically modifying its simple, elegant
hierarchical semantics, but it is fairly straightforward in SV.</p>

<p>Meanwhile, ESIM's support for bidirectionally-driven wires relies on a
subtle, unverified transformation to the module hierarchy which is necessary to
ensure a fundamental assumption that every wire has only one driving module.
In contrast, with SV's flattening approach, a wire that is bidirectionally
driven reduces to one that is just multiply driven; it is relatively easy to
resolve any multiply-driven wires after flattening and before composition.</p>


<h3>SystemVerilog support</h3>

<p>SV's approach to deriving an FSM from a module hierarchy via flattening,
alias normalization, and composition has proven to be very convenient for
expressing many SystemVerilog features such as compound data structures.
Thanks to this, SV can support a richer set of SystemVerilog designs than
ESIM.</p>

<h3>Performance statistics</h3>

<p>The following timings and performance discussion are for one of <a
href=\"http://www.oracle.com\">Oracle</a>'s main hardware proof stacks.
Perhaps these statistics should be taken lightly, as they were only single
runs, and it's possible (though somewhat unlikely) that there was contention
for the cores.  These were run with @('-j 1').

The reported \"user\" time is only the time that ACL2 itself was running.  The
time spent in the SAT solver is left out of the \"user\" time but very
relevant.  As such, we focus on the wall-clock time.</p>

<ul>
<li>In Esim:  12 hours and 14 minutes of time<br />
@('19758.892u 434.856s 12:14:18.48 45.8% 0+0k 692208+2144728io 18pf+0w')
</li>
<li>In SV: 7 hours and 7 minutes of time<br />
@('16128.279u 410.741s 7:07:16.04 64.5% 0+0k 520448+1000408io 12pf+0w')</li>
</ul>

<p>Generally speaking, proofs are either the same speed or faster under the SV
framework.  One <em>composition</em> (@(see sv::svex-decomp)) proof using @(see
acl2::gl) (which is the old method for doing such proofs) took approximately
5386 seconds in Esim and now takes 69 seconds in SV.  As another example, one
proof that describes the functionality of a Verilog circuit took 166 seconds in
Esim and now takes 170 seconds in SV.</p>")



;; <h5>SVEX Expressions and @(see 4vec) Values</h5>

;; <p>The SVEX expression language simply consists of s-expressions with functions
;; applied to variables or constants.  The functions are predefined;
;; there are no lambdas or user-defined primitives.</p>

;; <p>The values on which these functions operate are @(see 4vec) objects, which
;; can be thought of as signed integers whose bits may take any of the four values
;; 1, 0, X, or Z.</p>

;; <p>The expressions of the language are @(see svex) objects.  This is a sum of
;; products type with the following kinds/fields:</p>

;; <ul>
;; <li>kind @(':quote') has field @('val'), a @(see 4vec)</li>
;; <li>kind @(':var') has field @('name'), an @(see svar)</li>
;; <li>kind @(':call') has fields @('fn'), a @(see fnsym), and @('args'), an svexlist.</li>
;; </ul>


;; <h5>LHS Expressions</h5>

;; <p>An @(see LHS) expression is a special format representing a concatenation of
;; finite segments of wires (variables).  An LHS expression may be
;; straightforwardly converted to an svex, and a particular subset of svex
;; expressions may be converted to LHS expressions.</p>

;; <h5>SVEX Modules</h5>

;; <p>Svex has an associated module format; see @(see svmods) and @(see design).
;; Verilog designs can be converted into this format using @(see
;; vl::vl-design->svex-design).  Each module contains:</p>

;; <ul>
;; <li>a list of wire names and dimensions (width, lower bit index, and range direction)</li>
;; <li>a list of submodule instances (instance name and submodule name)</li>
;; <li>a list of assignments (pairings of LHS expressions and svex right-hand-sides)</li>

;; <li>a list of aliases (pairings of LHS expressions), representing port
;; connections and any other constructs that cause a single wire to have more than
;; one name</li>
;; </ul>

;; <h5>FSM Conversion</h5>

;; <p>A hardware design may be expressed hierarchically as an svex @(see design),
;; but for reasoning usually it is best to have a finite-state machine
;; representation; that is, a set of states with update functions and a set of
;; outputs with value functions, each in terms of inputs and previous states.  See
;; @(see svex-compilation) for a description of the process of obtaining an FSM
;; representation from a hierarchical one.</p>

;; <h5>Rewriting and Masks</h5>

;; <p>The svex library contains a rewriting routine, @(see svex-rewrite), that
;; applies a series of rules in order to simplify expressions.  The rewriter is
;; unconditional and memoized so that it runs in time linear in the size of the
;; expression set.  The rewrite rules are somewhat conservative in that they are
;; careful to avoid transformations that might increase the total number of nodes.
;; The rewriter uses a table of bitmasks that signify which bits of each
;; subexpression are used; for example, if we have a concatenation
;; @({
;;   (concat 4 a b)
;;  })
;; but the mask for this subexpression is, say, 5 -- which has no bits set past
;; the lowest 4 -- then this expression may be rewritten to just @('a').</p>

;; <h5>Composition and Apparent Loops</h5>

;; <p>Most of the time, expressions may be composed together into full update
;; functions by recursively traversing them down to the variables and replacing
;; the variables the update functions produced by recurring on their assigned
;; expressions.  However, because our variables represent multi-bit vectors,
;; sometimes a variable appears to depend on itself.  We then must stop this
;; process early and leave an unresolved non-input variable in the update
;; functions; otherwise the process would not terminate.  However, we can get rid
;; of these self-looping variables in the cases where there is no dependency of
;; any bit of the variable on itself, only dependencies among different bits.  In
;; this case, we can use the care-masks introduced in the previous section to
;; determine how many times we need to unroll the expression in order to eliminate
;; the apparent self-dependency.</p>

;; <h5>Symbolic Execution and Translation to AIGs</h5>

;; <p>See @(see svex-symbolic-evaluation).  The book \"symbolic.lisp\" provides a
;; connection to GL that allows symbolic evaluations of SVEXes to be done by
;; translating the svexes into AIGs and composing those AIGs with the symbolic
;; representations of the variable bindings.</p>

;; <h5>Decomposition Proofs</h5>

;; <p>See @(see svex-decomp).  The book \"decomp.lisp\" provides automation for
;; proving that a composition of several slices of a circuit are equivalent to a
;; whole circuit.</p>

;; ")



(defxdoc symbolic-test-vector
  :parents (sv)
  :short "An object describing a finite run of a hardware model."
  :long "<p>Originally, symbolic test vectors (STVs) were conceived as an aid
to concretely and symbolically simulating E/@(see esim) modules.  Now, a
similar library exists for <see topic='@(url sv)'>@(csym svex)</see> which is
nearly a drop-in replacement for @(see esim) STVs.  See @(see
acl2::symbolic-test-vectors) for description of the original esim-based
library, and @(see svex-stvs) for a description of the differences in the new
svex version.</p>")


(defxdoc vl-to-svex
  :parents (sv)
  :short "Translation of @(see vl::vl) designs into an SVEX design.")

(local (xdoc::set-default-parents sv::vl-to-svex))
