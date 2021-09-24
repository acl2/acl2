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
; tutorial.lisp
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "GL")
(include-book "xdoc/top" :dir :system)

(defxdoc basic-tutorial
  :parents (gl)
  :short "An introductory guide, recommended for new users of @(see GL)."

  :long "<p>This is a tutorial introduction to using GL to prove ACL2 theorems.
We recommend going through the entire tutorial before beginning to use GL.</p>

<p>You can think of this tutorial as a quick-start guide.  By the time you're
done with it, you should have a good understanding of how GL works, and be able
to use GL to easily prove many theorems.</p>

<p>We don't try to cover more advanced topics, like @(see optimization) and
@(see term-level-reasoning).  You'll probably want to get some practice using
GL before exploring these topics.</p>")


(defxdoc |1. An Example GL Proof|
  :parents (basic-tutorial)
  :long "

<p>The usual way to load GL is to start with</p>
@({
    (include-book \"centaur/gl/gl\" :dir :system)
})

<p>Let's use GL to prove a theorem.  The following C code, from Sean
Anderson <a href='http://graphics.stanford.edu/~seander/bithacks.html'>Bit
Twiddling Hacks</a> page, is a fast way to count how many bits are set in a
32-bit integer.</p>

@({
     v = v - ((v >> 1) & 0x55555555);
     v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
     c = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
})

<p>We can model this in ACL2 as follows.  It turns out that using
arbitrary-precision addition and subtraction does not affect the result, but we
must take care to use a 32-bit multiply to match the C code.</p>

@({
    (defun 32* (x y)
      (logand (* x y) (1- (expt 2 32))))

    (defun fast-logcount-32 (v)
      (let* ((v (- v (logand (ash v -1) #x55555555)))
             (v (+ (logand v #x33333333)
                   (logand (ash v -2) #x33333333))))
        (ash (32* (logand (+ v (ash v -4)) #xF0F0F0F)
                  #x1010101)
             -24)))
})

<p>We can then use GL to prove @('fast-logcount-32') computes the same
result as ACL2's built-in @('logcount') function for all unsigned 32-bit
inputs.</p>

@({
    (def-gl-thm fast-logcount-32-correct
      :hyp   (unsigned-byte-p 32 x)
      :concl (equal (fast-logcount-32 x)
                    (logcount x))
      :g-bindings `((x ,(g-int 0 1 33))))
})

<p>The @(':g-bindings') form is the only help GL needs from the user.  It tells
GL how to construct a symbolic object that can represent every value for @('x')
that satisfies the hypothesis (we'll cover this shortly).  No arithmetic books
or lemmas are required&mdash;we actually don't even know why this algorithm
works.  The proof completes in 0.09 seconds and results in the following ACL2
theorem.</p>

@({
    (defthm fast-logcount-32-correct
      (implies (unsigned-byte-p 32 x)
               (equal (fast-logcount-32 x)
                      (logcount x)))
      :hints ((gl-hint ...)))
})

<p>GL can generate counterexamples to non-theorems.  At first, we didn't
realize we needed to use a 32-bit multiply in @('fast-logcount-32'), and we
just used an arbitrary-precision multiply instead.  The function still worked
for test cases like @('0'), @('1') @('#b111'), and @('#b10111'), but when we
tried to prove its correctness, GL showed us three counterexamples:
@('#x80000000'), @('#xFFFFFFFF'), and @('#x9448C263').  By default, GL
generates a first counterexample by setting bits to 0 wherever possible, a
second by setting bits to 1, and a third with random bit settings.</p>")

(defxdoc |2. Symbolic Objects|
  :parents (basic-tutorial)
  :long "

<p>At its heart, GL works by manipulating Boolean expressions.  There are
many ways to represent Boolean expressions.  GL currently supports a hons-based
<see topic='@(url ubdds)'>BDD package</see> and also has support for using a
hons-based @(see aig) representation.</p>

<p>For any particular proof, you can choose which representation to use by
picking one of the available proof @(see modes).  Each representation has
strengths and weaknesses, and the choice of representation can significantly
impact performance.  We give some advice about choosing these modes in @(see
modes).</p>

<p>The GL user does not need to know how BDDs and AIGs are represented; in this
documentation we will just adopt a conventional syntax to describe Boolean
expressions, e.g., @('true'), @('false'), @('A & B'), @('~C'), etc.</p>

<p>GL groups Boolean expressions into <b>symbolic objects</b>.  Much like a
Boolean expression can be evaluated to obtain a Boolean value, a symbolic
object can be evaluated to produce an ACL2 object.  There are several kinds of
symbolic objects, but numbers are a good start.  GL represents symbolic, signed
integers as</p>

@({
    (:g-integer . <lsb-bits>)
})

<p>Where @('lsb-bits') is a list of Boolean expressions that represent the
two's complement bits of the number.  The bits are in lsb-first order, and the
last, most significant bit is the sign bit.  For instance, if @('p') is the
following @(':g-integer'),</p>

@({
    p = (:g-integer true   false   A & B   false)
})

<p>Then @('p') represents a 4-bit, signed integer whose value is either 1 or 5,
depending on the value of @('A & B').</p>

<p>GL uses another kind of symbolic object to represent ACL2 Booleans.
In particular,</p>

@({
    (:g-boolean . <val>)
})

<p>represents @('t') or @('nil'), depending on the Boolean expression
@('<val>').  For example,</p>

@({
     (:g-boolean . ~(A & B))
})

<p>is a symbolic object whose value is @('t') when @('p') has value 1, and
@('nil') when @('p') has value 5.</p>

<p>GL has a few other kinds of symbolic objects that are also tagged with
keywords, such as @(':g-var') and @(':g-apply').  But an ACL2 object
that does not have any of these special keywords within it is <i>also</i>
considered to be a symbolic object, and just represents itself.  Furthermore, a
cons of two symbolic objects represents the cons of the two objects they
represent.  For instance,</p>

@({
    (1 . (:g-boolean .  A & B))
})

<p>represents either @('(1 . t)') or @('(1 . nil)').  Together, these
conventions allow GL to avoid lots of tagging as symbolic objects are
manipulated.</p>

<p>One last kind of symbolic object we will mention represents an if-then-else
among other symbolic objects.  Its syntax is:</p>

@({
     (:g-ite  <test>  <then>  .  <else>)
})

<p>where @('<test>'), @('<then>'), and @('<else>') are themselves symbolic
objects.  The value of a @(':g-ite') is either the value of @('<then>') or
of @('<else>'), depending on the value of @('<test>').  For example,</p>

@({
     (:g-ite  (:g-boolean . A)
              (:g-integer B  A  false)
              . #\\C)
})

<p>represents either 2, 3, or the character @('C').</p>

<p>GL doesn't have a special symbolic object format for ACL2 objects other than
numbers and Booleans.  But it is still possible to create symbolic objects that
take any finite range of values among ACL2 objects, by using a nesting of
@(':g-ite')s where the tests are @(':g-boolean')s.</p>")


(defxdoc |3. Computing with Symbolic Objects|
  :parents (basic-tutorial)
  :long "

<p>Once we have a representation for symbolic objects, we can perform symbolic
executions on those objects.  For instance, recall the symbolic number @('p')
which can have value 1 or 5,</p>

@({
    p = (:g-integer  true   false   A & B   false)
})

<p>We might symbolically add 1 to @('p') to obtain a new symbolic number, say
@('q'),</p>

@({
    q = (:g-integer  false   true    A & B   false)
})

<p>which represents either 2 or 6.  Suppose @('r') is another symbolic number,</p>

@({
    r = (:g-integer  A   false   true   false)
})

<p>which represents either 4 or 5.  We might add @('q') and @('r') to obtain
@('s'),</p>

@({
    s = (:g-integer  A    true    ~(A & B)    (A & B)    false)
})

<p>whose value can be 6, 7, or 11.</p>

<p>Why can't @('s') be 10 if @('q') can be 6 and @('r') can be 4?  This
combination isn't possible because @('q') and @('r') involve the same
expression, @('A').  The only way for @('r') to be 4 is for @('A') to be false,
but then @('q') must be 2.</p>

<p>The underlying algorithm GL uses for symbolic additions is just a
ripple-carry addition on the Boolean expressions making up the bits of the two
numbers.  Performing a symbolic addition, then, means constructing new @(see
ubdds) or @(see aig)s, depending on which mode is being used.</p>

<p>GL has built-in support for symbolically executing most ACL2 primitives.
Generally, this is done by cases on the types of the symbolic objects being
passed in as arguments.  For instance, if we want to symbolically execute @(see
consp) on @('s'), then we are asking whether a @(':g-integer') may ever
represent a cons, so the answer is simply @('nil').  Similarly, if we ever try
to add a @(':g-boolean') to a @(':g-integer'), by the ACL2 axioms the
@(':g-boolean') is simply treated as 0.</p>

<p>Beyond these primitives, GL provides what is essentially a <a
href='http://www-formal.stanford.edu/jmc/recursive.pdf'>McCarthy-style
interpreter</a> for symbolically executing terms.  By default, it expands
function definitions until it reaches primitives, with some special handling
for @(see if).  For better performance, its interpretation scheme can be
customized with more efficient definitions and other @(see optimization)s.</p>
")

(defxdoc |4. Proving Theorems by Symbolic Execution|
  :parents (basic-tutorial)
  :long "

<p>To see how symbolic execution can be used to prove theorems, let's return to
the bit-counting example, where our goal was to prove</p>

@({
    (implies (unsigned-byte-p 32 x)
             (equal (fast-logcount-32 x)
                    (logcount x)))
})

<p>The basic idea is to first symbolically execute the above formula, and then
check whether it can ever evaluate to @('nil').  But to do this symbolic
execution, we need some symbolic object to represent @('x').</p>

<p>We want our symbolic execution to cover all the cases necessary for proving
the theorem, namely all @('x') for which the hypothesis @('(unsigned-byte-p 32
x)') holds.  In other words, the symbolic object we choose needs to be able to
represent any integer from 0 to @('2^32 - 1').</p>

<p>Many symbolic objects cover this range.  As notation, let @('b0, b1, ...')
represent independent Boolean variables in our Boolean expression
representation.  Then, one suitable object is:</p>

@({
    Xinit = (:g-integer b0 b1 ... b31 b32).
})

<p>Why does this have 33 variables?  The final bit, @('b32'), represents the
sign, so this object covers the integers from @('-2^32') to @('2^32 - 1').  We
could instead use a 34-bit integer, or a 35-bit integer, or some esoteric
creation involving @(':g-ite') forms.  But perhaps the best object to use would
be:</p>

@({
   Xbest = (:g-integer b0 b1 ... b31 false).
})

<p>since it covers exactly the desired range using the simplest possible
Boolean expressions.</p>

<p>Suppose we choose @('Xbest') to stand for @('x'). We can now symbolically
execute the goal formula on that object.</p>

<p>What does this involve?  First, @('(unsigned-byte-p 32 x)') produces the
symbolic result @('t'), since it is always true of the possible values of
@('Xbest').  It would have been equally valid for this to produce
@('(:g-boolean . true)'), but GL prefers to produce constants when
possible.</p>

<p>Next, the @('(fast-logcount-32 x)') and @('(logcount x)') forms each yield
@(':g-integer') objects whose bits are Boolean expressions in the variables
@('b0, ..., b31').  For example, the least significant bit will be an
expression representing the XOR of all these variables.</p>

<p>Finally, we symbolically execute @(see equal) on these two results.  This
compares the Boolean expressions for their bits to determine if they are
equivalent, and produces a symbolic object representing the answer.</p>

<p>So far we have basically ignored the differences between using @(see ubdds)
or @(see aig)s as our Boolean expression representation.  But here, the two
approaches produce very different answers:</p>

<ul>
<li>Since UBDDs are canonical, the expressions for the bits of the two numbers
  are syntactically equal, and the result from @(see equal) is simply @('t').</li>

<li>With AIGs, the expressions for the bits are semantically equivalent but not
  syntactically equal.  The result is therefore @('(:g-boolean . phi)'), where
  @('phi') is a large Boolean expression in the variables @('b0, ..., b31').
  The fact that @('phi') always evaluates to @('t') is not obvious just from
  its syntax.</li>
</ul>

<p>At this point we have completed the symbolic execution of our goal formula,
obtaining either @('t') in BDD mode, or this @(':g-boolean') object in AIG
mode.  Recall that to prove theorems using symbolic execution, the idea is to
symbolically execute the goal formula and then check whether its symbolic
result can represent @('nil').  If we are using BDDs, it is obvious that @('t')
cannot represent @('nil').  With AIGs, we simply ask a SAT solver whether
@('phi') can evaluate to @('false'), and find that it cannot.  This completes
the proof.</p>

<p>GL automates this proof strategy, taking care of many of the details
relating to creating symbolic objects, ensuring that they cover all the
possible cases, and ensuring that @('nil') cannot be represented by the
symbolic result.  When GL is asked to prove a non-theorem, it can generate
counterexamples by finding assignments to the Boolean variables that cause the
result to become @('nil').</p>")


(defxdoc |5. Using def-gl-thm|
  :parents (basic-tutorial)
  :long "

<p>The @(see def-gl-thm) command is the main interface for using GL to prove
theorems.  Here is the command we used in the bit-counting example from @(csee
|1. An Example GL Proof|):</p>

@({
    (def-gl-thm fast-logcount-32-correct
      :hyp   (unsigned-byte-p 32 x)
      :concl (equal (fast-logcount-32 x)
                    (logcount x))
      :g-bindings `((x ,(g-int 0 1 33))))
})

<p>Unlike an ordinary @(see defthm) command, @(see def-gl-thm) takes separate
hypothesis and conclusion terms (its @('hyp') and @(':concl') arguments).  This
separation allows GL to use the hypothesis to limit the scope of the symbolic
execution it will perform.  You also have to provide GL with @(':g-bindings')
that describe the symbolic objects to use for each free variable in the
theorem.</p>

<p>What are these bindings?  In the @('fast-logcount-32-correct') theorem, we
used a convenient function, @('g-int'), to construct the @(':g-bindings').
Expanding this away, here are the actual bindings:</p>

@({
   ((x (:g-integer 0 1 2 ... 32)))
})

<p>The @(':g-bindings') argument uses a slight modification of the symbolic
object format where the Boolean expressions are replaced by distinct natural
numbers, each representing a Boolean variable.  In this case, our binding for
@('x') stands for the following symbolic object:</p>

@({
    Xinit = (:g-integer b0 b1 ... b31 b32)
})

<p>Note that @('Xinit') is not the same object as @('Xbest') from @(see
|4. Proving Theorems by Symbolic Execution|)&mdash;its sign bit is @('b32')
instead of @('false'), so @('Xinit') can represent any 33-bit signed integer
whereas @('Xbest') only represents 32-bit unsigned values.  In fact, the
@(':g-bindings') syntax does not even allow us to describe objects like
@('Xbest'), which has the constant @('false') instead of a variable as one of
its bits.</p>

<p>There is a good reason for this restriction.  One of the steps in our proof
strategy is to prove <b>coverage</b>: we need to show the symbolic objects we
are starting out with have a sufficient range of values to cover all cases for
which the hypothesis holds; more on this in @(see |7. Proving Coverage|).  The
restricted syntax permitted by @(':g-bindings') ensures that the range of
values represented by each symbolic object is easy to determine.  Because of
this, coverage proofs are usually automatic.</p>

<p>Despite these restrictions, GL will still end up using @('Xbest') to carry
out the symbolic execution.  GL optimizes the original symbolic objects
inferred from the @(':g-bindings') by using the hypothesis to reduce the space
of objects that are represented.  In BDD mode this optimization uses <a
href='http://dx.doi.org/10.1145/309847.309968'>BDD parametrization</a>, which
restricts the symbolic objects so they cover exactly the inputs recognized by
the hypothesis.  In AIG mode we use a lighter-weight transformation that
replaces variables with constants when the hypothesis sufficiently restricts
them.  In this example, either optimization transforms @('Xinit') into
@('Xbest').</p>")

(defxdoc |6. Writing :g-bindings forms|
  :parents (basic-tutorial)
  :long "

<p>In a typical @(see def-gl-thm) command, the @(':g-bindings') should have an
entry for every free variable in the theorem.  Here is an example that shows
some typical bindings.</p>

@({
    :g-bindings '((flag   (:g-boolean . 0))
                  (a-bus  (:g-integer 1 3 5 7 9))
                  (b-bus  (:g-integer 2 4 6 8 10))
                  (mode   (:g-ite (:g-boolean . 11) exact . fast))
                  (opcode #b0010100))
})

<p>These bindings allow @('flag') to take an arbitrary Boolean value,
@('a-bus') and @('b-bus') any five-bit signed integer values, @('mode') either
the symbol @('exact') or @('fast'), and @('opcode') only the value 20.</p>

<p>(Aside: Note that since @('#b0010100') is not within a @(':g-boolean') or
@(':g-integer') form, it is <b>not</b> the index of a Boolean variable.
Instead, like the symbols @('exact') and @('fast'), it is just an ordinary ACL2
constant that stands for itself, i.e., 20.)</p>

<p>These @(':g-boolean') and @(':g-integer') are called @(see shape-specs).
They are similar to the symbolic objects GL uses to compute with, except that
natural number indices take the places of Boolean expressions.  The indices
used throughout all of the bindings must be distinct, and represent free,
independent Boolean variables.</p>

<p>In BDD mode, these indices have additional meaning: they specify the BDD
variable ordering, with smaller indices coming first in the order.  This
ordering can greatly affect performance.  In AIG mode the choice of indices has
no particular bearing on efficiency.</p>

<p>How do you choose a good BDD ordering?  It is often good to interleave the
bits of data buses that are going to be combined in some way.  It is also
typically a good idea to put any important control signals such as opcodes and
mode settings before the data buses.</p>

<p>Often the same @(':g-bindings') can be used throughout several theorems,
either verbatim or with only small changes.  In practice, we almost always
generate the @(':g-bindings') forms by calling functions or macros.  One
convenient function is</p>

@({(g-int start by n)})

<p>which generates a @(':g-integer') form with @('n') bits, using
indices that start at @('start') and increment by @('by').  This is
particularly useful for interleaving the bits of numbers, as we did for the
@('a-bus') and @('b-bus') bindings above:</p>

@({
     (g-int 1 2 5)  ---> (:g-integer 1 3 5 7 9)
     (g-int 2 2 5)  ---> (:g-integer 2 4 6 8 10)
})

<p>Writing out @(':g-bindings') and getting all the indices can be tedious.
See @(see auto-bindings) for a convenient macro that helps ensure that all the
indices are different.</p>")


(defxdoc |7. Proving Coverage|
  :parents (basic-tutorial)
  :long "

<p>There are really two parts to any GL theorem.  First, we need to
symbolically execute the goal formula and ensure it cannot evaluate to
@('nil').  But in addition to this, we must ensure that the objects we use to
represent the variables of the theorem cover all the cases that satisfy the
hypothesis.  This part of the proof is called the <b>coverage
obligation</b>.</p>

<p>For @('fast-logcount-32-correct'), the coverage obligation is to show that
our binding for @('x') is able to represent every integer from 0 to @('2^32 -
1').  This is true of @('Xinit'), and the coverage proof goes through
automatically.</p>

<p>But suppose we forget that @(':g-integer')s use a signed representation, and
attempt to prove @('fast-logcount-32-correct') using the following (incorrect)
g-bindings.</p>

@({
    :g-bindings `((x ,(g-int 0 1 32)))
})

<p>This looks like a 32-bit integer, but because of the sign bit it does not cover
the intended unsigned range.  If we submit the @(see def-gl-thm) command
with these bindings, the symbolic execution part of the proof is still successful.
But this execution has only really shown the goal holds for 31-bit unsigned
integers, so @(see def-gl-thm) prints the message</p>

@({
     ERROR: Coverage proof appears to have failed.
})

<p>and leaves us with a failed subgoal,</p>

@({
    (implies (and (integerp x)
                  (<= 0 x)
                  (< x 4294967296))
             (< x 2147483648))
})

<p>This goal is clearly not provable: we are trying to show @('x') must be less
than @('2^31') (from our @(':g-bindings')) whenever it is less than
@('2^32') (from the hypothesis).</p>

<p>Usually when the @(':g-bindings') are correct, the coverage proof will be
automatic, so if you see that a coverage proof has failed, the first thing to
do is check whether your bindings are really sufficient.</p>

<p>On the other hand, proving coverage is undecidable in principle, so
sometimes GL will fail to prove coverage even though the bindings are
appropriate.  For these cases, there are some keyword arguments to @(see
def-gl-thm) that may help coverage proofs succeed.</p>

<p>First, as a practical matter, GL does the symbolic execution part of the
proof <b>before</b> trying to prove coverage.  This can get in the way of
debugging coverage proofs when the symbolic execution takes a long time.  You
can use @(':test-side-goals t') to have GL skip the symbolic execution and go
straight to the coverage proof.  Of course, no @(see defthm) is produced when
this option is used.</p>

<p>By default, our coverage proof strategy uses a restricted set of rules and
ignores the current theory.  It heuristically expands functions in the
hypothesis and throws away terms that seem irrelevant.  When this strategy
fails, it is usually for one of two reasons.</p>

<ol>

<li>The heuristics expand too many terms and overwhelm ACL2.  GL tries to avoid
this by throwing away irrelevant terms, but sometimes this approach is
insufficient.  It may be helpful to disable the expansion of functions that are
not important for proving coverage.  The @(':do-not-expand') argument allows
you to list functions that should not be expanded.</li>

<li>The heuristics throw away a necessary hypothesis, leading to unprovable
goals.  GL's coverage proof strategy tries to show that the binding for each
variable is sufficient, one variable at a time.  During this process it throws
away hypotheses that do not mention the variable, but in some cases this can be
inappropriate.  For instance, suppose the following is a coverage goal for
@('b'):

@({
    (implies (and (natp a)
                  (natp b)
                  (< a (expt 2 15))
                  (< b a))
             (< b (expt 2 15)))
})

Here, throwing away the terms that don't mention @('b') will cause the proof to
fail.  A good way to avoid this problem is to separate type and size hypotheses
from more complicated assumptions that are not important for proving coverage,
along these lines:

@({
    (def-gl-thm my-theorem
      :hyp (and (type-assms-1 x)
                (type-assms-2 y)
                (type-assms-3 z)
                (complicated-non-type-assms x y z))
      :concl ...
      :g-bindings ...
      :do-not-expand '(complicated-non-type-assms))
})

</li>
</ol>

<p>For more control, you can also use the @(':cov-theory-add') argument to
enable additional rules during the coverage proof, e.g., @(':cov-theory-add
'(type-rule1 type-rule2)').</p>")


(defxdoc |8. Exercises|
  :parents (basic-tutorial)
  :long "<p>Here are some exercises you can use to get some experience with
using GL.</p>

<p>These exercises will get you into some rough spots, so that you can learn
how to get out.  If you get stuck, you can see our solutions in the file
@('centaur/gl/solutions.lsp').</p>

<p>We recommend trying to carry out these exercises in a new file.  You will
probably want to start your file with:</p>

@({
    (in-package \"ACL2\")
    (include-book \"centaur/gl/gl\" :dir :system)
})

<p>At certain points in the exercises, we assume your computer has at least
<b>8 GB</b> of memory.</p>


<h3>Arithmetic Exercises</h3>

<p><b>1a.</b> Use GL to prove that addition commutes for 4-bit unsigned
numbers:</p>

@({
     (implies (and (unsigned-byte-p 4 x)
                   (unsigned-byte-p 4 y))
              (equal (+ x y) (+ y x)))
})

<p><b>1b.</b> Carry out the same proof as in 1a, but construct your
G-bindings:</p>

<ul>
 <li>Using @(see auto-bindings)</li>
 <li>Using @(see g-int)</li>
 <li>\"Manually\", without using either of these.</li>
</ul>

<p>Hints: you may want to consult @(see |6. Writing :g-bindings forms|) and
@(see shape-specs).</p>


<p><b>1c.</b> Extend your proof from 1a to 20-bit numbers.  How long does the
proof take?  How much memory did it use?  Try the @(see hons-summary) command
get a sense of the memory usage.</p>


<p><b>1d.</b> In the same ACL2 session, undo your proof of 1c and submit it
again.  How long did it take this time?  Can you explain what happened?</p>


<p><b>1e.</b> Figure out how to optimize your G-bindings to make the proof in
1c go through quickly.  For reliable timings, use @(see clear-memoize-tables)
and @(see hons-clear) before each proof attempt.  Implement your solution using
both @(see g-int) and @(see auto-bindings).</p>


<p><b>1f.</b> Use GL to prove that addition commutes up to 3,000 bits.
Hint: the @(see debugging) section might be able to help you.</p>


")
