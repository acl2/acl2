; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; doc.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "GL")
(include-book "xdoc/top" :dir :system)


(defxdoc gl
  :parents (acl2::proof-automation acl2::hardware-verification)
  :short "A symbolic simulation framework for proving finitely bounded ACL2
theorems by bit-blasting with a <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>Binary Decision
Diagram</a> (BDD) package or a <a
href='http://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>SAT
solver</a>."

  :long "<h3>Overview</h3>

<p>GL is a convenient and efficient tool for solving many finite ACL2 theorems
that arise in @(see acl2::hardware-verification) and other contexts.  It has
played an important role in the verification of arithmetic units and microcode
routines at Centaur Technology.</p>

<p>GL makes extensive use of @(see acl2::hons-and-memoization).  Some
optional parts of GL also require <see topic='@(url defttag)'>trust
tags</see>.</p>

<p>GL translates ACL2 problems into Boolean problems that can be solved by
automatic @(see acl2::boolean-reasoning) tools.  When this approach can be
used, there are some good reasons to prefer it over @(see acl2::the-method) of
traditional, interactive theorem proving.  For instance, it can:</p>

<ul>

<li>Reduce the level of human understanding needed in the initial process of
developing the proof;</li>

<li>Provide clear counterexamples, whereas failed ACL2 proofs can often be
difficult to debug; and</li>

<li>Ease the maintenance of the proof, since after the design changes they can
often find updated proofs without help.</li>

</ul>

<p>How does this translation work?  You can probably imagine writing a
bit-based encoding of ACL2 objects.  For instance, you might represent an
integer with some structure that contains a 2's-complement list of bits.  GL
uses an encoding like this, except that Boolean expressions take the place of
the bits.  We call these structures @(see symbolic-objects).</p>

<p>GL provides a way to effectively compute with symbolic objects; e.g., it can
\"add\" two integers whose bits are expressions, producing a new symbolic
object that represents their sum.  GL can perform similar computations for most
ACL2 primitives.  Building on this capability, it can <b>symbolically
execute</b> terms. The result of a symbolic execution is a new symbolic object
that captures all the possible values the result could take.</p>

<p>Symbolic execution can be used as a <b>proof procedure</b>.  To prove a
theorem, we first symbolically execute its goal formula, then show the
resulting symbolic object cannot represent @('nil').  GL provides a @(see
def-gl-thm) command that makes it easy to prove theorems with this approach.
It handles all the details of working with symbolic objects, and only needs to
be told how to represent the variables in the formula.</p>

<h3>GL Documentation</h3>

<box><p><b>New users</b> should begin with the @(see basic-tutorial), which walks
through the basic ideas behind how GL works, and includes some examples that
cover how to use GL.</p></box>

<p>Once you start to use GL, you will likely be interested in the @(see
reference) section of this documentation.</p>

<p>Like any automatic procedure, GL has a certain capacity.  But when these
limits are reached, you may be able to work around the problem in various ways.
The @(see optimization) section explains various ways to improve GL's
performance.</p>

<p>Occasionally GL proofs will fail due to resource limitations or limitations
of its symbolic evaluation strategy.  When you run into problems, you may be
interested in some tools and techniques for @(see debugging) failed proofs.</p>

<p>If you want to go further with GL, you will probably want to explore @(see
other-resources) beyond just this documentation, which include Sol Swords'
Ph.D. dissertation, as well as many other academic papers and talks.</p>")


(defxdoc reference
  :parents (gl)
  :short "Reference documentation for using GL.")


(defxdoc other-resources
  :parents (gl)
  :short "Additional resources (talks, academic papers, a dissertation) for
learning about GL."

  :long "<p>Besides this @(see xdoc::xdoc) documentation, most GL users will
probably want to be aware of at least the following resources:</p>

<dl>

<dt>Sol Swords and Jared Davis.  <a
href='http://dx.doi.org/10.4204/EPTCS.70.7'>Bit-Blasting ACL2 Theorems</a>.
In ACL2 Workshop 2011.  November, 2011.  EPTCS 70.  Pages 84-102.</dt>

<dd>This is an approachable, user-focused introduction to GL as of 2011, which
also contains many pointers to related work.  It's probably a good idea to read
this first, noting that a few details have changed.  Much of this paper has now
been incorporated into this @(see xdoc::xdoc) documentation.</dd>

<dt>Sol Swords.  <a
href='http://repositories.lib.utexas.edu/handle/2152/ETD-UT-2010-12-2210'>A
Verified Framework for Symbolic Execution in the ACL2 Theorem Prover</a>.
Ph.D. thesis, University of Texas at Austin.  December, 2010.</dt>

<dd>This is the most comprehensive guide to GL's internals.  It covers tricky
topics like the handling of <i>if</i> statements and the details of BDD
parametrization.  It also covers the logical foundations of GL, such as
correctness claims for symbolic counterparts, the introduction of symbolic
interpreters, and the definition and verification of the GL clause processor.
Some topics are now somewhat dated, but it is good general background for
anyone who wants to extend GL.</dd>

<dt>The documentation for @(see acl2::hons-and-memoization).</dt>

<dd>GL makes heavy use of hash consing and memoization.  GL users will likely
want to be aware of the basics of @(see hons-and-memoization), and of commands
like @(see hons-summary), @(see hons-wash), and @(see acl2::set-max-mem).</dd>

</dl>


<h4>Back-end Solvers</h4>

<dl>

<dt>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a> In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</dt>
<dd>This is a more recent paper that's not especially focused on GL, but which
covers @(see aignet::aignet) and @(see satlink::satlink), which can be used by
GL in its new @(see gl-satlink-mode).  Many problems that are difficult to
solve using @(see acl2::ubdds) can be solved using @(see
satlink::satlink).</dd>

<dt>Sol Swords and Warren A Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010, LNCS 6172, Springer.  Pages
435-449.</dt>
<dd>This is an older paper about the details of the @('bddify') algorithm that
is used as the engine for @(see gl-aig-bddify-mode).</dd>

</dl>

<h4>GL Applications</h4>

<p>GL has been used at Centaur Technology to verify RTL implementations of
floating-point addition, multiplication, and conversion operations, as well as
hundreds of bitwise and arithmetic operations on scalar and packed integers.
Some papers describing some of this work include:</p>

<ul>

<li>Anna Slobodova, Jared Davis, Sol Swords, and Warren A. Hunt, Jr.  <a
href='http://dx.doi.org/10.1109/MEMCOD.2011.5970515'>A Flexible Formal
Verification Framework for Industrial Scale Validation</a>.  In Memocode 2011,
IEEE.  Pages 89-97.</li>

<li>Warren A. Hunt, Jr., Sol Swords, Jared Davis, and Anna Slobodova.  <i>Use
of Formal Verification at Centaur Technology</i>.  In David Hardin, editor, <a
href='http://dl.acm.org/citation.cfm?id=1841184'>Design and Verification of
Microprocessor Systems for High-Assurance Applications</a>, Pages 65-88.
Springer, 2010.</li>

</ul>

<h4>History</h4>

<p>GL is the successor of Boyer and Hunt's <b>G</b> system, the best
description of which may be found in:</p>

<ul>
<li>Robert S. Boyer and Warren A. Hunt, Jr.  <a
href='http://dx.doi.org/10.1145/1637837.1637840'>Symbolic Simulation in
ACL2</a>.  In ACL2 Workshop 2009, ACM, 2009.  Pages 20-24.</li>
</ul>

<p>The name, GL, its name stands for <i>G in the Logic</i>.  The G system was
written as a raw Lisp extension of the ACL2 kernel, so using it meant trusting
this additional code.  In contrast, GL is implemented as ACL2 books and its
proof procedure is formally verified by ACL2, so the only code we have to trust
is in ACL2, including its @(see acl2::hons-and-memoization) features.</p>")


(defxdoc debugging
  :parents (gl)
  :short "Advice and tools for debugging performance problems and failed @(see
gl) proofs."

:long "<p>A GL proof attempt can end in several ways.  Ideally, GL will either
quickly prove your conjecture, or disprove it and show you counterexamples to
help diagnose the problem.  But things will not always end so well.</p>


<h4>Capacity Problems</h4>

<dl>

<dt>GL is running out of memory.</dt>

<dd>Symptoms: your ACL2 process is using too much memory and your machine is
<i>swapping</i>, or you are seeing <i>frequent garbage collection</i> messages
that seem unsuccessful&mdash;that is, few bytes are freed by each GC.</dd>

<dd>There are @(see memory-management) tools that may help to avoid these
problems.  You may need to look into @(see optimization) techniques.</dd>

<dt>GL has enough memory, but is running forever.</dt>

<dd>You may be running into a bad case for GL's symbolic execution strategy, or
your problem may be too hard for the back-end solver (BDDs, SAT).  See @(see
performance-problems) for some tools and advice for dealing with these
situations.</dd>

</dl>


<h4>Other Problems</h4>

<dl>

<dt>GL is failing to prove coverage.</dt>

<dd>Symptoms: You are seeing <i>failed ACL2 proof goals</i> after GL says
it is proving coverage.</dd>

<dd>It might be that your :g-bindings aren't sufficient to cover your theorem's
hypotheses, or GL's strategy for proving coverage is misbehaving.  See @(see
coverage-problems) for advice on debugging this situation.</dd>

<dt>GL produces false counterexamples.</dt>

<dd>This is easy to identify because GL will print @('False counterexample!')
and direct you to @(see false-counterexamples).</dd>

</dl>")


(defxdoc performance-problems
  :parents (debugging)
  :long "

<p>Any bit-blasting tool has capacity limitations.  However, you may also run into
cases where GL is performing poorly due to preventable issues.  When GL seems
to be running forever, it can be helpful to trace the symbolic interpreter to
see which functions are causing the problem.  To trace the symbolic
interpreter, run</p>

@({
     (gl::trace-gl-interp :show-values t)
})

<p>Here, at each call of the symbolic interpreter, the term being interpreted
and the variable bindings are shown, but since symbolic objects may be too
large to print, any bindings that are not concrete are hidden.  You can also
get a trace with no variable bindings using @(':show-values nil').  It may also
be helpful to simply interrupt the computation and look at the Lisp backtrace,
after executing</p>

@({
     (set-debugger-enable t)
})

<p>In many cases, performance problems are due to BDDs growing too large.  This
is likely the case if the interpreter appears to get stuck (not printing any
more trace output) and the backtrace contains a lot of functions with names
beginning in @('q-'), which is the convention for BDD operators.  In some
cases, these performance problems may be solved by choosing a more efficient
BDD order.  But note that certain operations like multiplication are
exponentially hard.  If you run into these limits, you may need to refactor or
decompose your problem into simpler sub-problems, e.g., with @(see
def-gl-param-thm).</p>

<p>There is one kind of BDD performance problem with a special solution.
Suppose GL is asked to prove @('(equal spec impl)') when this does not actually
hold.  Sometimes the symbolic objects for @('spec') and @('impl') can be
created, but the BDD representing their equality is too large to fit in memory.
The goal may then be restated with @(see acl2::always-equal) instead of
@('equal') as the final comparison.  Logically, @('always-equal') is just
@('equal').  But @('always-equal') has a custom symbolic counterpart that
returns @('t') when its arguments are equivalent, or else produces a symbolic
object that captures just one counterexample and is indeterminate in all other
cases.</p>

<p>Another possible problem is that the symbolic interpreter never gets stuck,
but keeps opening up more and more functions.  These problems might be due to
@(see redundant-recursion), which may be avoided by providing a more efficient
@(see preferred-definitions).</p>")


(defxdoc false-counterexamples
  :parents (debugging)
  :long "

<p>Occasionally, GL will abort a proof after printing:</p>

@({
    False counterexample!  See :xdoc gl::false-counterexamples.
})

<p>Most of the time, you might think of GL as an \"exact\" system where we have
an explicit Boolean function representation of every bit in all the objects in
your conjecture.  Ideally, this should allow GL to either prove your theorem or
find a counterexample.</p>

<p>This isn't always the case. Sometimes GL represents objects more abstractly.
For example, GL tends not to support operations on non-integer rational
numbers.  If it runs into a call of @('(* 1/3 x)'), it may represent the result
abstractly, as a term-like symbolic object:</p>

@({
    (:g-apply binary-*  1/3  (:g-integer ...))
})

<p>(assuming @('x') is represented as a @(':g-integer) object).  This sort of
abstraction can help to avoid creating potentially very-expensive symbolic
objects, and is an important part of GL's @(see term-level-reasoning).</p>

<p>This kind of abstraction can be contagious.  For example, if we are trying
to prove @('(not (equal (* 1/3 x) 'not-a-number))'), then using the
@(':g-apply') representation for the @('*') subterm will likely cause GL to
also use a @(':g-apply') representation for the whole term.  But now, how is GL
supposed to give this to a SAT solver?</p>

<p>When GL finds a @(':g-apply') object in a Boolean context, such as an IF
test or a theorem's hypothesis or conclusion, it will create a fresh Boolean
variable to represent that term.  But if, say, that term is something like</p>

@({
     (:g-apply equal (:g-apply binary-* 1/3 ...)
                     not-a-number)
})

<p>which is always false, then this Boolean variable is too general, and by
replacing the term with the Boolean variable, GL has lost track of the fact
that the term is actually always false.  This generally leads to false
counterexamples.</p>

<h3>Dealing with False Counterexamples</h3>


<p>The first things to check for when you encounter a false counterexample:</p>

<ul>

<li>Missing @(':g-bindings'): When a variable is omitted from the
@(':g-bindings') form, a warning is printed and the missing variable is
assigned a @(':g-var') object.  A @(':g-var') can represent any ACL2 object,
without restriction.  Symbolic counterparts typically produce @(':g-apply')
objects when called on @(':g-var') arguments, and this can easily lead to false
counterexamples.</li>

<li>The stack depth limit, or \"clock\", was exhausted.  This may happen when
symbolically executing a recursive function if the termination condition can't
be detected, though this is often caused by previous introduction of an
unexpected G-APPLY object.</li>

<li>An unsupported primitive was called.  For example, as of August 2013 we do
not yet support UNARY-/, so any call of UNARY-/ encountered during symbolic
execution will return a G-APPLY of UNARY-/ to the input argument.  It may be
that you can avoid calling such functions by installing an <see topic='@(url
alternate-definitions)'>alternate definition</see>.</li>

<li>A primitive was called on an unsupported type of symbolic object.  For
example, the symbolic counterparts for most arithmetic primitives will produce
a G-APPLY object if an input seems like it might represent a non-integer
rational.  Since symbolic operations on rationals are absurdly expensive, we
simply don't implement them for the most part.</li>

</ul>

<p>It is common to use GL in such a way that G-VAR forms are not used, and
G-APPLY forms are unwelcome if they appear at all; when they do, they typically
result in a symbolic execution failure of some sort.  However, there are ways
of using GL in which G-VAR and G-APPLY forms are expected to exist; see @(see
term-level-reasoning).  If you are not expecting GL to create G-APPLY objects
but you are encountering false counterexamples, we suggest using the following
form to determine why a G-APPLY object is first being created:</p>

@({
 (gl::break-on-g-apply)
})

<p>Then when GL::G-APPLY is called in order to create the form, @('(BREAK$)')
will be called.  Usually this will allow you to look at the backtrace and
determine in what context the first G-APPLY object is being created.</p>

<p>Alternatively, if you are expecting some G-APPLY forms to be created but
unexpected ones are cropping up, you can make the break conditional
on the function symbol being applied:</p>

@({
 (gl::break-on-g-apply :allowed-fns (foo bar))
})")




(defxdoc memory-management
  :parents (optimization debugging)
  :long "

<p>Memory management can play a significant role in symbolic execution
performance.  In some cases GL may use too much memory, leading to swapping and
slow performance.  In other cases, garbage collection may run too frequently or
may not reclaim much space.  We have several recommendations for managing
memory in large-scale GL proofs.  Some of these suggestions are specific to
Clozure Common Lisp.</p>


<h4>Use set-max-mem</h4>

<p>You can load the @('centaur/misc/memory-mgmt') book and use the @(see
set-max-mem) command to indicate how large you would like the Lisp heap to be.
For instance,</p>

@({
     (set-max-mem (* 8 (expt 2 30)))
})

<p>says to allocate 8 GB of memory.  To avoid swapping, you should use somewhat
less than your available physical memory.  This book disables ephemeral garbage
collection and configures the garbage collector to run only when the threshold
set above is exceeded, which can boost performance.</p>


<h4>Optimize hash-consing performance.</h4>

<p>GL's representations of BDDs and AIGs use @(see hons) for structure-sharing.
The @(see hons-summary) command can be used at any time to see how many honses
are currently in use, and hash-consing performance can be improved by
pre-allocating space for these honses with @(see hons-resize).</p>


<h4>Manage hash-consing and memoization overhead.</h4>

<p>Symbolic execution can use a lot of hash conses and can populate the
memoization tables for various functions.  The memory used for these purposes
is <b>not</b> automatically freed during garbage collection, so it may
sometimes be necessary to manually reclaim it.</p>

<p>A useful function is @('(maybe-wash-memory n)'), which frees this memory and
triggers a garbage collection only when the amount of free memory is below some
threshold @('n').  A good choice for @('n') might be 20\% of the @(see
set-max-mem) threshold.</p>

<p>It can be useful to call @(see acl2::maybe-wash-memory) between proofs, or
between the cases of parametrized theorems; see for instance the
@(':run-before-cases') argument of @(see def-gl-param-thm).</p>")



(defxdoc symbolic-objects
  :parents (reference)
  :short "Format of symbolic objects in @(see gl)."

  :long "<p>Symbolic objects represent functions from the set of
environments (described below) to the set of ACL2 objects.  The value of an
object at an environment is given by an evaluator function.  Symbolic objects
are recursively structured and have a number of constructors.  We first briefly
describe evaluators (and why there can be more than one), then the structure of
environment objects, and then the symbolic object constructors.</p>


<h4>Evaluators</h4>

<p>A symbolic object evaluator is a function with the interface</p>

@({
 (EV symbolic-object environment) => value.
})

<p>There may be several evaluators defined.  The differences between evaluators
have to do with the G-APPLY symbolic object type, which represents a function
applied to symbolic arguments.  In order to evaluate such an object, the
evaluator must be defined such that it recognizes the particular function
symbol used in the G-APPLY object.  An evaluator may not evaluate a symbolic
object containing a G-APPLY construct with an unrecognized function symbol.
One evaluator, named EVAL-G-BASE, is initially defined in the GL library, and
recognizes function symbols of the predefined primitives included with the
library.</p>

<h4>Environments</h4>

<p>The basic components of symbolic objects are data structures containing
Boolean functions, represented either by BDDs or AIGs (see @(see modes)), and G-VAR
constructs, which represent unconstrained variables.  To evaluate a symbolic
object, each of these needs to be evaluated to a constant.  An environment
contains the information necessary to evaluate either kind of expression:</p>
<ul>
<li>a truth assignment for the Boolean variables used in the Boolean function
representation; in AIG mode, this is an alist mapping variable names to
Booleans, and in BDD mode, an ordered list of Booleans corresponding to the
decision levels of the BDDs.</li>
<li>an alist mapping unconstrained variable names to their values.</li>
</ul>

<h4>Symbolic Object Representation</h4>

<p>There are eight basic constructions of symbolic objects, some of which may
recursively contain other symbolic objects.  We now describe each such
construction and its evaluation.</p>

<dl>

<dt>Representation: (:G-BOOLEAN . bfr)</dt>
<dt>Constructor: (G-BOOLEAN bfr)</dt>

<dd>Takes the values T and NIL.  The evaluation of a G-BOOLEAN object is simply
the evaluation of @('<bdd>') using the list of Booleans in the
environment.</dd>

<dt>Representation: (:G-INTEGER . list-of-bfrs)</dt>
<dt>Constructor: (G-INTEGER list-of-bfrs)</dt>

<dd>Evaluates to an integer.  @('<list-of-bfrs>') gives the bits of the
integer, least significant first.  The representation is two's-complement,
i.e. the last bit represents 0 if false or -1 if true.  The enpty list
represents 0.</dd>

<dt>Representation (:G-CONCRETE . object)</dt>
<dt>Constructor: (G-CONCRETE object)</dt>

<dd>Evaluates to @('<object>').  While most ACL2 objects evaluate to themselves
anyway, this construct is useful for representing symbolic objects or objects
structured similarly to symbolic objects.  For example, @({
 (:G-CONCRETE . (:G-BOOLEAN . (T . NIL))) evaluates to
 (:G-BOOLEAN . (T . NIL)), whereas
 (:G-BOOLEAN . (T . NIL)) evaluates to either T or NIL.
})</dd>

<dt>Representation: (:G-VAR . name)</dt>
<dt>Constructor: (G-VAR . name)</dt>

<dd>@('<name>') may be any object.  Evaluates to the object bound to
@('<name>') in the environment.</dd>

<dt>Representation: (:G-ITE test then . else)</dt>
<dt>Constructor: (G-ITE test then else)</dt>

<dd>Each of @('<test>'), @('<then>'), and @('<else>') must be symbolic objects.
If @('<test>') evaluates to a nonnil value, then this object evaluates to the
evaluation of @('<then>'); otherwise this evaluates to the evaluation of
@('<else>').</dd>

<dt>Representation: (:G-APPLY fn . arglist)</dt>
<dt>Constructor: (G-APPLY fnsym arglist)</dt>

<dd>@('<fn>') should be a symbol and @('<arglist>') should be a symbolic
object.  If the evaluator recognizes @('<fn>') and @('<arglist>') evaluates to
@('<args>'), a true-list of length equal to the arity of the function
@('<fn>'), then this object evaluates to the application of @('<fn>') to
@('<args>').  Otherwise, the evaluation is undefined.</dd>

<dt>Representation: atom</dt>

<dd>Every atom evaluates to itself.  However, the keyword symbols
:G-BOOLEAN, :G-INTEGER, :G-CONCRETE, :G-VAR, :G-ITE, and :G-APPLY are not
themselves well-formed symbolic objects.</dd>

<dt>Representation: @('(car . cdr)')</dt>

<dd>A cons of two symbolic objects evaluates to the cons of their evaluations.
Note that since the keyword symbols that distinguish symbolic object
constructions are not themselves well-formed symbolic objects, this
construction is unambiguous.</dd>

</dl>

<h4>Miscellaneous notes about symbolic objects and evaluation</h4>

<ul>

<li>Any function from finitely many Boolean values to the universe of
ACL2 objects can be expressed using only the G-ITE, G-BOOLEAN, and
G-CONCRETE forms.</li>

<li>Most ACL2 objects are themselves well-formed symbolic objects which
evaluate to themselves.  The exceptions are ones which contain the special
keyword symbolis :G-BOOLEAN, :G-INTEGER :G-CONCRETE, :G-VAR,
:G-ITE, and :G-APPLY.  These atoms (and out of all atoms, only these)
are not well-formed symbolic objects.  Since a cons of any two
well-formed symbolic objects is itself a well-formed symbolic objects,
only objects containing these atoms may be non-well-formed.</li>

<li>The function that checks well-formedness of symbolic objects is GOBJECTP,
and the initial evaluator function is GL::EVAL-G-BASE.  It may be useful to
read the definitions of these functions for reference in case the above
symbolic object documentation is unclear.</li>

</ul>")





(defxdoc alternate-definitions
  :parents (optimization)
  :short "Specifying alternative definitions to be used for symbolic
  execution."

  :long "<p>Sometimes the definition of some function is ill-suited for
automatic methods of symbolic execution.  For example, @('(EVENP X)') is defined
as</p>

@({
 (integerp (* x (/ 2)))
})

<p>and because currently multiplication by a non-integer is not supported in
GL, this yields a G-APPLY form in most cases.</p>

<p>In this case and several others, one may instead provide an alternate
definition for the function in question and use that as the basis for GL
symbolic execution.</p>

<p>In the case of EVENP, the following theorem works as an alternate
definition:</p>

@({
 (defthm evenp-is-logbitp
   (equal (evenp x)
          (or (not (acl2-numberp x))
              (and (integerp x)
                   (equal (logbitp 0 x) nil))))
   :rule-classes nil)
})

<p>After proving this theorem, the following form sets this alternate
definition as the one GL will use when symbolically interpreting EVENP:</p>

@({
 (gl::set-preferred-def evenp evenp-is-logbitp)
})

<p>This form produces one or more @(see table) events.</p>")


(defxdoc coverage-problems
  :parents (debugging)
  :short "Proving the coverage obligation in GL-based proofs."

  :long "<p>In order to prove a theorem using GL, one must show that the
symbolic objects chosen to represent the inputs are sufficiently general to
cover the entire set of interest.  See @(see SHAPE-SPECS) for a more in-depth
discussion.  The @(see DEF-GL-THM) and @(see DEF-GL-PARAM-THM) events as well
as the @(see GL-HINT) hints all provide some degree of automation for coverage
proofs; often this is enough to satisfy the coverage obligation without further
user interaction.  Here we discuss how to debug coverage proofs that do not
succeed.</p>

<p>First, it is probably important to be able to re-run a coverage proof easily
without also re-running the associated symbolic execution, which may be quite
time-consuming.  To do this, in either the @(see DEF-GL-THM) or @(see
DEF-GL-PARAM-THM) forms, add the keyword argument @(':TEST-SIDE-GOALS T').
This form will then try to prove the coverage obligation in exactly the manner
it would do during the real proof, but it will not attempt to prove the theorem
itself, and will not record a new ACL2 theorem even if the proof is
successful.</p>

<p>During proof output, GL prints a message \"Now proving coverage\" when it
begins the coverage proof.  The initial goal of a coverage proof will also have
a hypothesis @('(GL::GL-CP-HINT 'GL::COVERAGE)'); this hypothesis is logically
meaningless, but a useful indicator of the beginning of a coverage proof.</p>

<p>When GL's usual set of heuristics is used, a coverage proof proceeds as
follows.  The initial goal is as follows:</p>

@({
 (implies <theorem-hyps>
          (gl::shape-spec-obj-in-range
            <list-of-input-bindings>
            <list-of-input-variables>))
})

<p>The coverage heuristics proceed by repeatedly opening up the
@('GL::SHAPE-SPEC-OBJ-IN-RANGE') function.  This effectively splits the proof
into cases for each component of each variable; for example, if one variable's
shape specifier binding is a cons of two :G-INTEGER forms, then its CAR and CDR
will be considered separately.  Eventually, this results in several subgoals,
each with conjunction of requirements for some component of some input.</p>

<p>During this process of opening the @('GL::SHAPE-SPEC-OBJ-IN-RANGE')
conclusion, the coverage heuristics also examine and manipulate the hypotheses.
When the conclusion is focused on a certain input variable or component of that
variable, and some hypothesis does not mention that variable, that hypothesis
will be dropped so as to speed up the proof.  If a hypothesis does mention that
variable, it may be expanded (if it is not a primitive) so as to try and gain
more information about that variable.  This is a useful heuristic because often
the hypotheses consist of a conjunction of predicates about different input
variables or components of input variables, and some of these predicates are
often themselves defined as conjunctions of predicates about subcomponents.</p>

<p>However, sometimes this expansion goes too far.  In many cases, some
conjuncts from the hypothesis have nothing to do with the coverage obligation.
In these cases, the @(':DO-NOT-EXPAND') keyword argument to @('DEF-GL-THM') and
@('DEF-GL-PARAM-THM') may be used.  This argument should evaluate to a list of
function symbols; the coverage heuristic is then prohibited from expanding any
of these functions.</p>

<p>For efficiency, the set of rules used in coverage proofs is very restricted.
Because of this, you may see in the proof output a goal which should be
obvious, but is not proven because the necessary rule is not included.  The
keyword argument @(':COV-THEORY-ADD') may be used to enable certain additional
rules that are not included.  The set of rules that are used is defined in the
ruleset @('GL::SHAPE-SPEC-OBJ-IN-RANGE-OPEN'), which can be listed using</p>

@({
 (get-ruleset 'gl::shape-spec-obj-in-range-open (w state)).
})

<p>The default heuristics for coverage proofs may not always be useful.
Therefore, the user may also supplement or replace the coverage heuristics with
arbitrary computed hints.  The keyword argument @(':COV-HINTS') gives a list of
computed hint forms which, according to the value of the keyword argument
@(':COV-HINTS-POSITION'), either replaces or supplements the default hints.
@(':COV-HINTS-POSITION') may be either @(':REPLACE'), in which case the
defaults are not used at all; @(':FIRST'), in which case the user-provided
@(':COV-HINTS') are tried first and the defaults afterward, or the default,
@(':LAST'), in which case the default coverage heuristic is tried before the
user-provided hints.</p>

<p>Note that subgoal names will be different between a @(':TEST-SIDE-GOALS')
and an actual attempt at proving the theorem.  Therefore, it is best not to
write computed hints that depend on the @('ID') variable.</p>")





(defxdoc optimization
  :parents (gl)
  :short "How to optimize GL's symbolic simulations for faster or
larger-scale proofs."

  :long "

<ul>

<li>Using different @(see modes) to solve the problem.  Some modes vastly
outperform others on particular problems and it is very easy to switch modes,
so this is often a good first thing to try when you run into a performance
problem.</li>

<li>Decomposing difficult problems into easier subgoals.  GL provides some
support for @(see case-splitting) hard proofs, and in some cases this kind of
decomposition can tremendously boost performance.</li>

<li>Using other @(see optimization) techniques to make GL's symbolic execution
strategy more efficient.</li>

</ul>


<p>The scope of theorems GL can handle is directly impacted by its symbolic
execution performance.  It is actually quite easy to customize the way certain
terms are interpreted, and this can sometimes provide important speedups.</p>

<p>GL's symbolic interpreter operates much like a basic Lisp interpreter.  To
symbolically interpret a function call, GL first eagerly interprets its
arguments to obtain symbolic objects for the actuals.  Then GL symbolically
executes the function in one of three ways:</p>

<ul>

<li>As a special case, if the actuals evaluate to concrete objects, then GL may
be able to stop symbolically executing and just call the actual ACL2 function
on these arguments.</li>

<li>For primitive ACL2 functions like @(see +), @(see consp), @(see equal), and
for some defined functions like @(see logand) and @(see ash) where performance
is important, GL uses hand-written functions called <b>symbolic
counterparts</b> that can operate on symbolic objects.  The advanced GL user
can write new @(see custom-symbolic-counterparts) to speed up symbolic
execution.</li>

<li>Otherwise, GL looks up the definition of the function, and recursively
interprets its body in a new environment binding the formals to the symbolic
actuals.  The way a function is written can impact its symbolic execution
performance; see @(see redundant-recursion).  It is easy to instruct GL to use
more efficient, @(see preferred-definitions) for particular functions.</li>

</ul>

<p>GL symbolically executes functions strictly according to the ACL2 logic and
does not consider guards.  An important consequence is that when @(see mbe) is
used, GL's interpreter follows the @(':logic') definition instead of the
@(':exec') definition, since it might be unsound to use the @(':exec') version
of a definition without establishing the guard is met.  Also, while GL can
symbolically simulate functions that take user-defined stobjs or even the ACL2
@(see state), it does not operate on \"real\" @(see acl2::stobj)s; instead, it
uses the logical definitions of the relevant stobj operations, which do not
provide the performance benefits of destructive operations.  Non-executable
functions cannot be symbolically executed.</p>

<p>In the event that one is performing a very large decomposition proof (e.g.,
the theorem @('boothmul-decomp-is-boothmul-via-GL') in book
@('centaur/esim/tutorial/boothmul.lisp'), one should consider using book
@('centaur/esim/stv/stv-decomp-proofs').</p>")


(defxdoc modes
  :parents (optimization)
  :short "GL modes allow you to control major aspects of how GL carries out its
symbolic simulation and how it should solve Boolean formulas that arise during
proofs."

  :long "<p>For some general background, see section
@(see |4. Proving Theorems by Symbolic Execution|) of the @(see basic-tutorial).</p>

<p>By default, GL operates in @(see gl-bdd-mode).  In this mode, the Boolean
formulas within @(see symbolic-objects) are represented using @(see ubdds), and
questions about these formulas are resolved using BDD operations.</p>

<p>But GL also supports other modes, and you can easily switch between modes on
a proof-by-proof basis.  Typically this looks like:</p>

@({
   (local (gl::gl-bdd-mode))
   (def-gl-thm foo ...)

   (local (gl::gl-satlink-mode))
   (def-gl-thm bar ...)
})

<p>GL's other modes use And-Inverter Graphs (@(see aig)s) as the Boolean
function representation.  Unlike BDDs, AIGs are non-canonical, and this affects
performance in fundamental ways: AIGs are generally much cheaper to construct
than BDDs, but it can be hard to determine whether AIGs are equivalent, whereas
with BDDs this is just a pointer-equality check.</p>

<p>A very convenient feature of AIGs is that you do not have to come up with a
good variable ordering&mdash;this may be especially helpful on problems where
@(see case-splitting) would be necessary because there's not a universally good
BDD ordering.  On the other hand, BDDs can provide especially nice
counterexamples, whereas with AIGs we typically get just one, essentially
random counterexample.</p>

<p>Performance-wise, AIGs are better for some problems and BDDs for others.
Many operations combine bits from data buses in a regular, orderly way; in
these cases, there is often a good BDD ordering and BDDs may be faster than our
AIG modes.  But when the operations are less regular, when no good BDD ordering
is apparent, or when case-splitting seems necessary to get good BDD
performance, the AIG modes may do better.  For many of our proofs, AIG mode
performs well and saves us the trouble of finding a good BDD ordering.</p>

<h4>Solving AIGs</h4>

<p>When AIGs are used to carry out GL proofs, we need some way to answer
whether the final AIG is satisfiable.  To do this, GL can use one of two
back-end solvers.</p>

<p>Usually the better and higher-performance option is to send the AIG to an
external SAT solver; see @(see gl-satlink-mode).  In this mode, GL uses the
@(see satlink) library to call upon an off-the-shelf SAT solver.  Using
external SAT solvers raises questions of trust, and GL does not yet implement
any sort of proof-checking for the SAT solver's output.  But pragmatically, for
most verification efforts, it is probably reasonable to trust a SAT solver.</p>

<p>Another option is to simply convert the AIG into BDDs; see @(see
gl-aig-bddify-mode).  This isn't necessarily a good idea, and you still have to
worry about the variable order in this case.  Occasionally this <i>may</i>
out-perform just using BDDs to begin with, because there are certain
optimizations you can make when converting from AIGs to BDDs that aren't
possible when you just use BDDs for everything.  This is also a high-confidence
mode, where the whole proof is carried out within ACL2, with just some minimal
trust-tags to boost performance.</p>

")

(defxdoc gl-mode-implementation
  :parents (modes)
  :short "Implementation details about switching between GL reasoning modes"
  :long "

<p>GL's various reasoning modes are implemented using @(see defattach).  There
are several functions that need to have proper attachments in order for GL to
function; when the GL library is loaded, they are set up to a default
configuration in which GL will use BDD-based reasoning.</p>

<p>The functions that need attachments follow.  Here, BFR stands for Boolean
function representation.</p>

<ul>
<li><p>BFR-MODE: 0-ary with no constraints.  This detemines whether the Boolean
function components in the symbolic object representation are BDDs or AIGs, and
thus the functions used to combine them.  E.g., the definition of BFR-NOT
is (basically):</p>

@({
 (if (bfr-mode) (aig-not x) (q-not x)).
})

<p>Similarly, BFR-EVAL either applies EVAL-BDD or AIG-EVAL, depending on
BFR-MODE.</p>

<p>By default the function BFR-BDD (which returns NIL) is attached to BFR-MODE,
and thus BFR-NOT uses the BDD operation Q-NOT.  To use AIGs instead, attach
BFR-AIG, which returns T.</p></li>

<li><p>BFR-SAT: Unary, returning three values: SAT, SUCCEEDED, CTREX.  The main
constraint of BFR-SAT is that if it returns SAT=NIL and SUCCEEDED=T, then
BFR-EVAL of the input on any environment must be NIL, i.e., the input must be
an unsatisfiable BDD or AIG (depending on the BFR-MODE.)  The CTREX value
should be a counterexample in the case of a SAT result, represented either as a
BDD or an alist mapping variables to Boolean values; see below under
BFR-COUNTEREX-MODE.</p>

<p>To satisfy the constraint in the BDD case, it suffices to simply check whether
the input BDD is NIL; if so, it is satisfiable, and otherwise, it isn't.  This
method is implemented as BFR-SAT-BDD, which is the default attachment of
BFR-SAT.  For AIG mode, we provide an attachment BFR-SAT-BDDIFY which solves an
AIG satisfiability query by transforming the input AIG into a BDD.  However,
one might instead hook up a SAT solver into ACL2 so that it can take an AIG as
input.  Given a way of calling such an external tool, it would not be difficult
to produce a function that conforms to the constraint described above. :-)</p></li>

<li><p>BFR-COUNTEREX-MODE: 0-ary, no constraints.  This says whether the
counterexample value sometimes returned by BFR-SAT is in the form of a BDD or
an association list.  If it is set up wrong, then output in case of a
counterexample will be garbled.  In both the default BDD mode and in the AIG
BDDIFY mode provided, the counterexample is in the form of a BDD, and so we
attach BFR-COUNTEREX-BDD by default.  However, if an external SAT solver is
used, then there will likely be a single assignment returned, which might more
conveniently be provided as an alist.  Then one would instead attach
BFR-COUNTEREX-ALIST.</p></li></ul>")

(defxdoc redundant-recursion
  :parents (optimization)
  :long "

<p>Here is a way to write a list-filtering function.</p>

@({
     (defun filter1 (x)
       (cond ((atom x)
              nil)
             ((element-okp (car x))               ;; keep it
              (cons (car x) (filter1 (cdr x))))
             (t                                   ;; skip it
              (filter1 (cdr x)))))
})

<p>This definition can be inefficient for symbolic execution.  Suppose we are
symbolically executing @('filter1'), and the @('element-okp') check has
produced a symbolic object that can take both @('nil') and non-@('nil') values.
Then, we proceed by symbolically executing both the keep- and skip-branches,
and construct a @(':g-ite') form for the result.  Since we have to evaluate the
recursive call twice, this execution becomes exponential in the length of
@('x').</p>

<p>We can avoid this blow-up by consolidating the recursive calls, as
follows.</p>

@({
    (defun filter2 (x)
      (if (atom x)
          nil
        (let ((rest (filter2 (cdr x))))
          (if (element-okp (car x))
              (cons (car x) rest)
            rest))))
})

<p>Of course, @('filter1') is probably slightly better for concrete execution
since it has a tail call in at least some cases.  If we do not want to change
the definition of @('filter1'), we can simply tell GL to use the @('filter2')
definition instead, as described in the next section.</p>")


(defxdoc preferred-definitions
  :parents (optimization)
  :long "<p>To instruct GL to symbolically execute @('filter2') in place of
@('filter1'), we can do the following:</p>

@({
    (defthm filter1-for-gl
      (equal (filter1 x) (filter2 x))
      :rule-classes nil)

    (gl::set-preferred-def filter1 filter1-for-gl)
})

<p>The @('set-preferred-def') form extends a table that GL consults when
expanding a function's definition.  Each entry in the table pairs a function
name with the name of a theorem.  The theorem must state that a call of the
function is unconditionally equal to some other term.</p>

<p>When GL encounters a call of a function in this table, it replaces the call
with the right-hand side of the theorem, which is justified by the theorem.  So
after the above event, GL will replace calls of @('filter1') with
@('filter2').</p>

<p>As another example of a preferred definition, GL automatically optimizes the
definition of @(see evenp), which ACL2 defines as follows:</p>

@({
    (evenp x) = (integerp (* x (/ 2)))
})

<p>This definition is basically unworkable since GL provides little support for
rational numbers.  However, GL has an efficient, built-in implementation of
@(see logbitp).  So to permit the efficient execution of @('evenp'), GL proves
the following identity and uses it as @('evenp')'s preferred definition.</p>

@({
     (defthm evenp-is-logbitp
       (equal (evenp x)
              (or (not (acl2-numberp x))
                  (and (integerp x)
                       (equal (logbitp 0 x) nil)))))
})")


(defxdoc custom-symbolic-counterparts
  :parents (optimization)
  :long "

<p>The advanced GL user can write custom symbolic counterparts to get better
performance.</p>

<p>This is somewhat involved.  Generally, such a function operates by cases on
what kinds of symbolic objects it has been given.  Most of these cases are
easy; for instance, the symbolic counterpart for @(see consp) just returns
@('nil') when given a @(':g-boolean') or @(':g-integer').  But in other cases
the operation can require combining the Boolean expressions making up the
arguments in some way, e.g., the symbolic counterpart for @(see binary-*)
implements a simple binary multiplier.</p>

<p>Once the counterpart has been defined, it must be proven sound with respect
to the semantics of ACL2 and the symbolic object format.  This is an ordinary
ACL2 proof effort that requires some understanding of GL's implementation.</p>

<p>An example of a more sophisticated symbolic counterpart is an @(see aig) to
<see topic='@(url ubdds)'>ubdd</see> conversion algorithm.  This function
serves as a symbolic counterpart for AIG evaluation.  This algorithm and its
correctness proof can be found in the book @('centaur/aig/g-aig-eval').</p>")



(defxdoc case-splitting
  :parents (optimization)
  :long "

<p>BDD performance can sometimes be improved by breaking a problem into
subcases.  The standard example is floating-point addition, which benefits from
separating the problem into cases based on the difference between the two
inputs' exponents.  (See for instance work by <a
href='http://dx.doi.org/10.1007/BFb0028769'>Chen and Bryant</a> and <a
href='http://dx.doi.org/10.1145/309847.309968'>Aagard, Jones, and
Seger</a>.)</p>

<p>For each exponent difference, the two mantissas are aligned differently
before being added together, so a different BDD order is necessary to
interleave their bits at the right offset.  Without case splitting, a single
BDD ordering has to be used for the whole problem; no matter what ordering we
choose, the mantissas will be poorly interleaved for some exponent differences,
causing severe performance problems.  Separating the cases allows the
appropriate order to be used for each difference.</p>

<p>GL provides a @(see def-gl-param-thm) command that supports this technique.
This command splits the goal formula into several subgoals and attempts to
prove each of them using the @(see def-gl-thm) approach, so for each subgoal
there is a symbolic execution step and coverage proof.  To show the subgoals
suffice to prove the goal formula, it also does another @(see def-gl-thm)-style
proof that establishes that any inputs satisfying the hypothesis are covered by
some case.</p>

<h3>A First Example</h3>

<p>Here is how we might split the proof for @('fast-logcount-32') into five
subgoals.  One goal handles the case where the most significant bit is 1.  The
other four goals assume the most significant bit is 0, and separately handle
the cases where the lower two bits are 0, 1, 2, or 3.  Each case has a
different symbolic binding for @('x'), giving the BDD variable order. Of
course, splitting into cases and varying the BDD ordering is unnecessary for
this theorem, but it illustrates how the @(see def-gl-param-thm) command
works.</p>

@({
    (def-gl-param-thm fast-logcount-32-correct-alt
      :hyp (unsigned-byte-p 32 x)
      :concl (equal (fast-logcount-32 x)
                    (logcount x))
      :param-bindings
      `((((msb 1) (low nil)) ((x ,(g-int 32 -1 33))))
        (((msb 0) (low 0))   ((x ,(g-int  0  1 33))))
        (((msb 0) (low 1))   ((x ,(g-int  5  1 33))))
        (((msb 0) (low 2))   ((x ,(g-int  0  2 33))))
        (((msb 0) (low 3))   ((x ,(g-int  3  1 33)))))
      :param-hyp (and (equal msb (ash x -31))
                      (or (equal msb 1)
                          (equal (logand x 3) low)))
      :cov-bindings `((x ,(g-int 0 1 33))))
})

<p>We specify the five subgoals to consider using two new variables, @('msb')
and @('low').  Here, @('msb') will determine the most significant bit of
@('x'); @('low') will determine the two least significant bits of @('x'), but
only when @('msb') is 0.</p>

<p>The @(':param-bindings') argument describes the five subgoals by assigning
different values to @('msb') and @('low').  It also gives the @('g-bindings')
to use in each case.  We use different bindings for @('x') for each subgoal to
show how it is done.</p>

<p>The @(':param-hyp') argument describes the relationship between @('msb'),
@('low'), and @('x') that will be assumed in each subgoal.  In the symbolic
execution performed for each subgoal, the @(':param-hyp') is used to reduce the
space of objects represented by the symbolic binding for @('x').  For example,
in the subgoal where @('msb = 1'), this process will assign @('t') to
@('x[31]').  The @(':param-hyp') will also be assumed to hold for the coverage
proof for each case.</p>

<p>How do we know the case-split is complete?  One final proof is needed to
show that whenever the hypothesis holds for some @('x'), then at least one of
the settings of @('msb') and @('low') satisfies the @(':param-hyp') for this
@('x').  That is:</p>

@({
    (implies (unsigned-byte-p 32 x)
             (or (let ((msb 1) (low nil))
                   (and (equal msb (ash x -31))
                        (or (equal msb 1)
                            (equal (logand x 3) low))))
                 (let ((msb 0) (low 0)) ...)
                 (let ((msb 0) (low 1)) ...)
                 (let ((msb 0) (low 2)) ...)
                 (let ((msb 0) (low 3)) ...)))
})

<p>This proof is also done in the @(see def-gl-thm) style, so we need we need
one last set of symbolic bindings, which is provided by the @(':cov-bindings')
argument.</p>

<h3>Another Example</h3>

<p>Suppose we want to prove the commutativity of @('*') for two finite natural
numbers, @('a') and @('n'), but that GL isn't able to prove this property
unless we case-split on the eight possible values for @('n').  We can do so
with the following call of @(see def-gl-param-thm)</p>

@({

    (def-gl-param-thm finite-commute-of-*
      :hyp (and (natp a)
                (< a (expt 2 16))
                (natp n)
                (< n 8))
      :concl (equal (* n a)
                    (* a n))
      :param-bindings `((((lsb 0) (mid-sb 0) (high-sb 0))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 0) (mid-sb 0) (high-sb 1))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 0) (mid-sb 1) (high-sb 0))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 0) (mid-sb 1) (high-sb 1))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 1) (mid-sb 0) (high-sb 0))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 1) (mid-sb 0) (high-sb 1))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 1) (mid-sb 1) (high-sb 0))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3)))
                        (((lsb 1) (mid-sb 1) (high-sb 1))
                         ,(gl::auto-bindings (:nat a 16)
                                             (:nat n 3))))
      :param-hyp (equal n
                        (logapp 1 lsb
                                (logapp 1 mid-sb
                                        high-sb)))

      :cov-bindings (gl::auto-bindings (:nat a 16)
                                       (:nat n 3)))

})

<p>The @(':hyp') and @(':concl') are the same as in a @('def-gl-thm').  The
@(':gl-bindings') becomes @(':cov-bindings').  And we must add the
@(':param-bindings') and @(':param-hyp').</p>

<p>As in the previous example, the @(':param-hyp') specifies the relationship
between the variables in the theorem that we want to case-split and the values
given in @(':param-bindings').  In this example, we essentially encode a truth
table into @(':param-bindings') using the least significant bit (@('lsb')),
middle significant bit
(@('mid-sb')), and most significant bit (@('high-sb')).  We then indicate that
these three significant-bit variables appended together represent the variable
@('n') in our theorem.</p>

<p>The syntax for specifying the variable ordering for each case-split is a bit
strange.  Currently, for each @(':param-bindings') entry, one must specify the
symbolic objects (BDD ordering, number of bits required, etc.) for each
case-split.  Thus, in this example, you see the bindings specified many times.
We could write a macro (perhaps using @(see ACL2::pairlis$)) so we didn't
have to type so much, but for clarity of instruction, we leave the expansion in
this example.</p>
")




(defxdoc term-level-reasoning
  :parents (gl optimization)
  :short "GL's term-level proof support"
  :long

  "<p>The traditional way of using GL to prove a theorem is to give a bit-level
description of each variable of the theorem as a shape spec in the :g-bindings
argument of def-gl-thm -- X is a 10-bit integer, Y is a three-entry Boolean
list, etc.  In this mode of operation, the goal is for every function to be
able to symbolically execute and produce a purely bit-level symbolic object as
its output.</p>

<p>This style of reasoning is somewhat restrictive.  ACL2 code is often
written in a way that makes this sort of symbolic execution expensive.  For
example, suppose we want a structure that maps integer keys to values.  For
best execution speed, we might represent this as a stobj array.  For best
ease of reasoning, we might represent it as a record (as in
books/misc/records.lisp), since these have nice, intuitive, hypothesis-free
rules about them.  For symbolic execution performance, on the other hand,
we might decide that a simple alist is the best representation.  But if we've
written the code in one of the other styles, then we'd like to be able to
escape the suboptimal symbolic execution this entails.</p>

<p>We have added features to GL which provide a way around these problems by
allowing for term-level reasoning as well as bit-level:</p>


<ul>

<li>rewrite rules, conditional/unconditional, supporting syntaxp hypotheses</li>

<li>uninterpreted functions</li>

<li>rules for merging IF branches that resolve to term- rather than bit-level
objects</li>

<li>automatic generation of new Boolean variables for IF tests that resolve to
terms rather than bits</li>

</ul>

<p>Warning: These features require careful setup of a rewriting theory with good
normal forms.  It's difficult to debug problems with them.  In many ways
they may not yet be ready for prime time.</p>

<h3>Rewriting</h3>

<p>Elaborating on our memory example, suppose we are trying to prove something
about a program that loads and stores from computed addresses in a 1024-entry
memory of 32-bit unsigned numbers.  For good execution speed when running
concrete simulations, we might represent this memory as a stobj containing a
1024-element array.  However, this doesn't perform well when proving theorems
about this representation using GL, because at each update to a symbolic
address we must modify several (perhaps all) entries in the array
representation: if our update is</p>

@({
  (update-mem <sym_address> <sym_value> <arr>)
})

<p>then at each address i of the array we must store an object representing:</p>

@({
  if (sym_address == i) then sym_value else arr[i].
})

<p>We might do better if we didn't try to compute an explicit interpretation of
the array after each update, but instead simply tracked the updates in
chronological order, as in an alist.  To illustrate how to do this, suppose
that our updater, accessor, and creator functions are, respectively,</p>

<ul>
<li>@('(update-mem addr val mem)')</li>
<li>@('(access-mem addr mem)')</li>
<li>@('(create-mem)')</li>
</ul>

<p>First, tell GL never to open the definitions of these functions:</p>

@({
 (gl::gl-set-uninterpreted update-mem)
 (gl::gl-set-uninterpreted access-mem)
 (gl::gl-set-uninterpreted create-mem)
})

<p>Now, when GL encounters updates, rather than computing a new explicit
symbolic representation for the memory, it will return a term representation,
such as</p>

@({
  (update-mem addr1 val1 (update-mem addr2 val2 (create-mem))).
})

<p>To make this work, we just need to provide rewrite rules so that GL can reason
about accesses:</p>

@({
 (gl::def-gl-rewrite access-of-create
    (equal (access-mem addr (create-mem))
           (and (natp addr) (< addr 1024) 0)))

 (gl::def-gl-rewrite access-of-update
    (equal (access-mem addr (update-mem waddr val mem))
           (if (equal (nfix addr) (nfix waddr))
               val
             (access-mem addr mem))))
})

<h3>Branch Merging</h3>

<p>Suppose that somewhere in our program we have an update as follows:</p>

@({
  (let ((mem (if special-condition
                 (update-mem addr val mem)
               mem)))
      ...)
})

<p>At this point, simulating with just the rules we have above, our proof will
probably fail because a subsequent access of the memory won't be resolved by
the access-of-update rule: we no longer have a term of the form</p>

@({
  (access-mem addr (update-mem waddr val mem))
})

<p>but rather</p>

@({
 (access-mem addr (if cond (update-mem waddr val mem) mem)).
})

<p>We could fix this by introducing a new rule:</p>

@({
 (gl::def-gl-rewrite access-of-if
     (equal (access-mem addr (if c mem1 mem2))
            (if c (access-mem addr mem1) (access-mem addr mem2))))
})

<p>This is probably the easiest solution if ACCESS-MEM is the only important
function that must interact with UPDATE-MEM.  An alternative is to write a rule
that merges the two branches into a single term.  A branch merge rule can
accomplish this:</p>

@({
 (gl::def-gl-branch-merge merge-conditional-update
   (equal (if cond (update-mem addr val mem) mem)
          (update-mem addr (if cond val (access-mem addr mem)) mem)))
})

<p>This isn't necessarily cheap -- in order to apply this rule, we need to find
the previous value of addr in mem, and this symbolic lookup is relatively
expensive, since it may need to traverse all the updates in mem to construct
the symbolic value of the access.</p>


<h3>Term-level shape specifiers</h3>

<p>Traditionally, to do a proof in GL one must supply, for each free variable of
the theorem, a shape specifier, which tells GL how to create a symbolic object
to represent that variable.  After GL finishes the symbolic execution portion
of the proof, the shape specifiers must be shown to be appropriate given the
assumptions about each variable; it therefore generates proof obligations of
the form:</p>

@({
 (implies (<hypotheses> var)
          (shape-spec-obj-in-range <shape-spec> var))
})

<p>These are called coverage obligations.  Shape-spec-obj-in-range says that the
value var is expressible by the given shape-spec; that is, the shape-spec
covers all possible values of var satisfying the hyps.  For example, if the
shape-spec is the :g-integer construct for a 10-bit integer, then the
shape-spec-obj-in-range term reduces to:</p>

@({
  (and (integerp var)
       (< var (expt 2 9))
       (<= (- (expt 2 9)) var)).
})

<p>Since the new GL capabilities described above allow manipulation of
term-level symbolic objects, it can be useful to supply term-level shape
specifiers.  This can be done using the G-CALL and G-VAR constructs.</p>

<p>A G-VAR construct is simply a free variable; it can represent any object
whatsoever, so its coverage obligations are trivial.</p>

<p>A G-CALL represents a function call.  It takes three arguments:</p>

<ul>
<li>FN, a function symbol</li>
<li>ARGS, a list of arguments, each (recursively) a shape spec</li>
<li>INV, a 1-argument function symbol or lambda, the inverse function.</li>
</ul>

<p>The symbolic term resulting from this shape spec is simply the
application (G-APPLY) of FN to the symbolic objects derived from ARGS.  INV is
an extra piece of information that tells us how to prove coverage.  Its usage
is discussed in @(see g-call).</p>

<h3>Automatic Boolean Variable Generation</h3>

<p>GL now has the ability to generate fresh Boolean variables in addition to
the ones existing in the user-provided shape spec.  It does this anytime an IF
condition's value ends up as a term-level object, i.e. a G-APPLY (function
call) or G-VAR (free variable).  The mapping between these term-level objects
and the generated Boolean variables are stored as we symbolically execute and
can be reused if the same condition is encountered again.  Careful use of this
feature can allow GL to work without giving such detailed shape specifiers.</p>

<p>For example, suppose that we don't want to assume anything about our memory
variable, but we know that for any slot we access, we'll only use 5 bits of the
stored value: perhaps our accessors always take (LOGHEAD 5 x) of the slot.  We
can assign a G-VAR object to the memory; that way it can represent any object
at all.  We then want to arrange things so that at every access, we generate 5
new Boolean variables for the integer bits of that access (if we haven't
already done so).  Here is one rule that will accomplish that:</p>

@({
 (gl::def-gl-rewrite loghead-5-of-access-mem
    ;; We don't want this rule to apply to an update-mem term, so this syntaxp
    ;; hyp prevents that.  We also should only apply this if ADDR is a concrete
    ;; object; we'd need a different strategy for symbolic addresses.
    (implies (syntaxp (and (not (and (consp mem)
                                     (gl::g-apply-p mem)
                                     (eq (gl::g-apply->fn mem) 'update-mem)))
                           (gl::general-concrete-p addr)))
              (equal (loghead 5 (access-mem addr mem))
                     (logcons
                      (if (logbitp 0 (access-mem addr mem)) 1 0)
                      (logcons
                       (if (logbitp 1 (access-mem addr mem)) 1 0)
                       (logcons
                        (if (logbitp 2 (access-mem addr mem)) 1 0)
                        (logcons
                         (if (logbitp 3 (access-mem addr mem)) 1 0)
                         (logcons
                          (if (logbitp 4 (access-mem addr mem)) 1 0)
                          0))))))))
})

<p>Performing this rewrite will cause GL to generate a Boolean variable for each
of these LOGBITP terms, because they produce term-level objects that are then
used in IF tests.</p>

<p>Using this strategy makes it harder to generate counterexamples.  In fact, it
is impossible to generally solve the problem of generating counterexamples when
using this strategy.  A satisfying assignment from a SAT solver gives us an
assignment of values to our Boolean variables.  But these Boolean variables
each just correspond to some term, which may be an arbitrary nesting of
functions.  To map this Boolean-level counterexample to an ACL2-level
counterexample, we are then left with finding an assignment for some variables
that makes a series of terms take certain truth values, which is undecidable.
In the next section, we describe a heuristic method for generating
counterexamples that works in practice when applied carefully.</p>

<p>Furthermore, unless this strategy is used with utmost care, it is likely
that proofs will fail due to detection of \"counterexamples\" that are actually
impossible.  For example, we might generate a Boolean variable for (integerp x)
and another one for (logbitp 0 x).  But these two terms are not independent; in
fact, (logbitp 0 x) implies (integerp x).  If we don't let the SAT solver know
about these constraints, it might find false counterexamples. This can't render
GL unsound, but may lead to failed proofs.  You may provide rules for
generating constraints among these Boolean variables to solve this kind of
problem: see @(see def-gl-boolean-constraint).</p>

<p>The situation described above (where every field is accessed via LOGHEAD and
via concrete address) is a particularly good one for this strategy, since then
all we need to know about each field are its LOGBITPs, which are all
independent.</p>

<h3>Counterexamples with Automatic Boolean Variable Generation</h3>

<p>Our strategy for generating counterexamples when using automatic Boolean
variable generation is to provide rules for manipulating assignments.  For
example:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) t)
   (x (logior (ash 1 n) x)))

 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) nil)
   (x (logand (lognot (ash 1 n)) x)))
})

<p>These two rules, respectively, say:</p>

<ul>
<li>\"if (logbitp n x) should be T, then assign X = (logior (ash 1 n) x)\"</li>
<li>\"if (logbitp n x) should be NIL, then assign X = (logand (lognot (ash 1 n)) x)\".</li>
</ul>

<p>DEF-GLCP-CTREX-REWRITE can also take a keyword argument :test, which can do
a syntactic check on the variables matched. E.g., we could ensure that N was a
constant in the rules above:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) t)
   (x (logior (ash 1 n) x))
   :test (quotep n))
})

<p>Note that these rules are purely heuristic, have no bearing on the soundness of
GL, and do not require any proofs.  Getting them wrong may cause GL to generate
false counterexamples, however.</p>

<p>Another rule that would be useful in the memory example above:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ((access-mem addr mem) val)
   (mem (update-mem addr val mem))
   :test (quotep addr))
})")
