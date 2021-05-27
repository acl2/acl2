; ACL2 System+Books Combined XDOC Manual
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)


(defsection math
  :parents (top)
  :short "Math-related libraries: arithmetic, algebra, bit-vectors.")

(defsection algebra
  :parents (math)
  :short "Libraries to reason about algebraic structures, e.g. groups, rings, fields, polynomials.")

(defsection arithmetic
  :parents (math)
  :short "Libraries for reasoning about basic arithmetic, bit-vector
arithmetic, modular arithmetic, etc.")

(defsection arithmetic-2
  :parents (arithmetic)
  :short "A newer arithmetic library that is considered deprecated in favor of arithmetic-5."
  :long "For more information, see @('[books]/arithmetic-2/README')."
  )

(defsection arithmetic-3
  :parents (arithmetic)
  :short "Another newer arithmetic library that is considered deprecated in favor of arithmetic-5."
  :long "For more information, see @('[books]/arithmetic-3/README').")

(defsection arithmetic-5
  :parents (arithmetic)
  :short "A powerful arithmetic library."
  :long "For more information, see @('[books]/arithmetic-5/README').")

(defsection bit-vectors
  :parents (math)
  :short "Libraries for reasoning about bit vectors.")

(defsection boolean-reasoning
  :parents (top)
  :short "Libraries related to representing and processing Boolean functions,
geared toward large-scale automatic reasoning, e.g., via SAT solving and AIG or
BDD packages."

  :long "<h3>Introduction</h3>

<p><a href='http://en.wikipedia.org/wiki/Boolean_function'>Boolean
functions</a> are widely useful throughout mathematical logic, computer
science, and computer engineering.  In formal verification, they are especially
interesting because many high-capacity, fully automatic techniques are known
for analyzing, comparing, and simplifying them; for instance, see <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>binary decision
diagrams</a> (bdds), <a
href='http://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>SAT
solvers</a>, <a
href='http://en.wikipedia.org/wiki/And-inverter_graph'>and-inverter
graphs</a> (aigs), <a href='http://en.wikipedia.org/wiki/Model_checking'>model
checking</a>, <a
href='http://en.wikipedia.org/wiki/Formal_equivalence_checking'>equivalence
checking</a>, and so forth.</p>

<h3>Libraries for Boolean Functions</h3>

<p>We have developed some libraries for working with Boolean functions, for
instance:</p>

<ul>

<li>@(see satlink) provides a representation of <a
href='http://en.wikipedia.org/wiki/Conjunctive_normal_form'>conjunctive normal
form</a> formulas and a way to call SAT solvers from ACL2 and trust their
results.</li>

<li>Libraries like @(see aig) and @(see ubdds) provide @(see hons)-based AIG and
BDD packages.</li>

<li>@(see aignet) provides a more efficient, @(see stobj)-based AIG
representation similar to that used by <a
href='http://www.eecs.berkeley.edu/~alanmi/abc/'>ABC</a>.</li>

</ul>

<p>These libraries are important groundwork for the @(see gl) framework for
bit-blasting ACL2 theorems, and may be of interest to anyone who is trying to
develop new, automatic tools or proof techniques.</p>

<h3>Libraries for Four-Valued Logic</h3>

<p>Being able to process large-scale Boolean functions is especially important
in @(see hardware-verification).  But actually, here, to model certain circuits
and to implement certain algorithms, it can be useful to go beyond Boolean
functions and consider a richer logic.</p>

<p>You might call Boolean functions or Boolean logic a two-valued logic, since
there are just two values (true and false) that any variable can take.  It is
often useful to add a third value, usually called X, to represent an
\"unknown\" value.  In some systems, a fourth value, Z, is added to represent
an undriven wire.  For more on this, see @(see why-4v-logic).</p>

<p>We have developed two libraries to support working in four-valued logic.  Of
these, the @(see 4v) library is somewhat higher level and is generally simpler
and more convenient to work with.  It serves as the basis of the @(see esim)
hardware simulator.  Meanwhile, the @(see faig) library is a bit lower-level
and does not enjoy the very nice @(see 4v-monotonicity) property of @(see
4v-sexprs).  On the other hand, @(see faig)s are closer to @(see aig)s, and can
be useful for loading expressions into @(see aignet) or @(see satlink).</p>

<h3>Related Papers</h3>

<p>Besides the documentation here, you may find the following papers
useful:</p>

<p>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a>  In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</p>

<p>Sol Swords and Jared Davis.  <a
href='http://dx.doi.org/10.4204/EPTCS.70.7'>Bit-Blasting ACL2 Theorems</a>.
In ACL2 Workshop 2011.  November, 2011.  EPTCS 70.  Pages 84-102.</p>

<p>Sol Swords and Warren A Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010,LNCS 6172, Springer.  Pages
435-449.</p>")


(defsection hardware-verification
  :parents (top)
  :short "Libraries for working with hardware description languages, modeling
 circuits, etc."
 :long "Also see the (probably incomplete) <a
 href='http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html'>page
 of ACL2-related publications</a>.")

(defsection software-verification
  :parents (top)
  :short "Software verification projects, tools, etc."
  :long "Also see the (probably incomplete) <a
 href='http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html'>page
 of ACL2-related publications</a>.")

(defxdoc macro-libraries
  :parents (top macros)
  :short "Generally useful macros for writing more concise code, and frameworks
 for quickly introducing concepts like typed structures, typed lists, defining
 functions with type signatures, and automating other common tasks.")

(defxdoc proof-automation
  :parents (top)
  :short "Tools, utilities, and strategies for dealing with particular kinds
of proofs.")

(defxdoc testing-utilities
  :parents (top)
  :short "Tools for developing and running tests.")


(defxdoc hint-utils
  :parents (proof-automation)
  :short "Tools that produce hints to guide the prover.")
