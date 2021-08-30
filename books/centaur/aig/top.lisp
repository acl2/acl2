; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "ACL2")
(include-book "accumulate-nodes-vars")
(include-book "aig2c")
(include-book "aig-base")
(include-book "aig-equivs")
(include-book "aiger")
(include-book "aig-print")
(include-book "aig-sat")
; Avoid dependence of this top.lisp book on glucose, so that running the
; command " make everything USE_QUICKLISP=1" with ACL2 will build the
; manual:
; (include-book "aig-sat-tests")
(include-book "aig-vars-ext")
(include-book "aig-vars-fast")
(include-book "aig-vars")
(include-book "bddify-correct")
(include-book "bddify")
(include-book "best-aig")
(include-book "eval-restrict")
(include-book "faig-base")
(include-book "faig-constructors")
(include-book "faig-equivs")
(include-book "faig-purebool-p")
(include-book "g-aig-eval")
(include-book "induction")
(include-book "misc")
(include-book "portcullis")
(include-book "random-sim")


(defxdoc aig
  :parents (boolean-reasoning)
  :short "A @(see hons)-based <a
href='http://en.wikipedia.org/wiki/And-inverter_graph'>And-Inverter
Graph</a> (AIG) library for representing and manipulating Boolean functions."

  :long "<h3>Introduction</h3>

<p>And-Inverter Graphs are a way to represent Boolean functions using only the
operations <i>and</i> and <i>not</i>.</p>

<p>This AIG library, found in @('centaur/aig'), is sometimes called the
<b>Hons-AIG library</b> to distinguish it from another AIG library, @(see
aignet).  Very briefly:</p>

<ul>
 <li>Hons-AIGs are simpler, easier to work with, and easier to reason about.</li>
 <li>@(see aignet) is faster.</li>
</ul>

<p>We won't say anything more about Aignet here.  A much more detailed
comparison of the libraries is available in: Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a> In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</p>


<h3>Representation of AIGs</h3>

<p>We always construct AIGs with @(see hons) so that existing pieces of AIGs
will be automatically reused.  We represent AIGs as arbitrary cons trees, which
we interpret as follows:</p>

<ul>

<li>@('T') represents the constant-true function.</li>

<li>@('NIL') represents the constant-false function.</li>

<li>Any other atom represents a Boolean variable (i.e., an input to the
function.)</li>

<li>A cons of the form @('(A . NIL)') represents the negation of @('A').</li>

<li>Any other cons, @('(A . B)'), represents the conjunction of @('A') and
@('B').</li>

</ul>

<p>Note that every ACL2 object is a well-formed AIG under this definition.</p>

<p>This meaning of cons trees is given by the evaluation function @(see
aig-eval), which returns the (Boolean) value of an AIG under some particular
assignment to its variables.  This function naturally induces an equivalence
relation, @(see aig-equiv): two AIGs are semantically equivalent if they have
the same evaluation under every possible variable assignment.</p>

<p>You might wonder why we would restrict ourselves to using only <i>and</i>
and <i>not</i>?  On the surface, using a richer language like S-expressions
might seem more compact.  For instance, with S-expressions we could represent
@('(or a b)') is much smaller looking than its and/not equivalent:
@('(not (and (not a) (not b)))').</p>

<p>But another critical part of memory efficiency is structure sharing.  That
is, suppose that we already need @('(not a)') and @('(not b)') elsewhere in the
function.  With s-expressions, these terms would have nothing in common with
@('(or a b)'), but with AIGs we can reuse the existing parts of
@('(not (and (not a) (not b)))').</p>


<h3>Library Functions</h3>

<p>Besides the @(see aig-semantics) functions like @(see aig-eval) and @(see
aig-equiv), the real core of the library includes:</p>

<ul>

<li>Basic, low-level @(see aig-constructors) for building
AIGs (<i>and</i>, <i>or</i>, etc.).  We prove these operations correct with
respect to @(see aig-eval).</li>

<li>Somewhat higher-level @(see aig-substitution) operations, like @(see
aig-restrict), @(see aig-compose), and @(see aig-partial-eval).</li>

<li>Operations for collecting the variables from an AIG, such as @(see
aig-vars).</li>

</ul>

<p>We provide some tools to \"solve\" AIGs.  Historically we have heavily used
the @(see bddify) algorithm, which constructs a BDD from an AIG.  More
recently, @(see aig-sat) provides a nice alternative using @(see aignet) and
@(see satlink) to give the problem to a SAT solver.</p>

<p>Beyond this, the rest of the library is a hodgepodge of @(see aig-other)
algorithms for working with AIGs.</p>


<h3>AIGs versus BDDs</h3>

<p>Another option for representing Boolean functions would be to use <see
topic='@(url ubdds)'>BDDs</see>.  In comparison with BDDs, AIGs are:</p>

<ul>

<li>cheaper to construct, e.g., if we want to <i>or</i> together the functions
@('f') and @('g'), it only takes a few conses with AIGs, whereas with BDDs we
need to walk through @('f') and @('g') to construct a new structure (which
might be quite large); but</li>

<li>more expensive to compare, e.g., with BDDs we can determine if @('f') and
@('g') are equal via pointer equality, whereas with AIGs this is a
satisfiability problem.</li>

</ul>

<p>This tradeoff is often worth it.  For instance, it can often be more faster
to construct an AIG and then @(see bddify) it than to just directly build the
BDD.  Why?  With the whole AIG visible, the bddify algorithm can often
\"prune\" branches of the AIG that turn out to be irrelevant, and hence avoid
constructing large parts of the BDD that aren't really needed.</p>




")

(defxdoc aig-substitution
  :parents (aig)
  :short "AIG operations for carrying out substitutions, compositions, and
  partial evaluations.")

(defxdoc aig-constructors
  :parents (aig)
  :short "Low-level functions for constructing AIGs."
  :long "<p>Note that you can enable/disable these together using the <see
topic='@(url rulesets)'>ruleset</see> @('aig-constructors').</p>")

(defxdoc aig-other
  :parents (aig)
  :short "Various hard-to-categorize algorithms for working with AIGs.")

(defxdoc aig-semantics
  :parents (aig)
  :short "Functions related to the semantic meaning of AIGs, e.g., @(see
aig-eval) and @(see aig-equiv).")
