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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "xdoc/top" :dir :system)

(defxdoc fgl
  :parents (acl2::proof-automation acl2::hardware-verification)
  :short "A prover framework that supports bit-blasting."
  :long "

<p>FGL is the successor to @(see gl::gl).  It mainly consists of a clause
processor that calls on a custom rewriter/term interpreter which features
support for efficient representations of Boolean functions.  Compared to GL,
FGL offers the following new features:</p>

<ul>

<li>Support for representing Boolean functions using the @(see
aignet::aignet) package.</li>

<li>Support for calling incremental SAT while rewriting/symbolic execution.</li>

<li>Less functionality included in built-in primitives, but better able to be
programmed using rewrite rules.</li>

<li>Explicit representation of the entire interpreter state, potentially
allowing global simplifications (e.g. combinational-equivalence-preserving
AIGNET transformations).</li>

<li>The symbolic object representation includes a new primitive kind
representing a fast alist or array.</li>

<li>Better debugging capabilities, including a tracing facility for the
rewriter and the ability to examine the full interpreter stack at any
point.</li>

</ul>

<p>FGL is currently missing some important features of GL.  In particular, BDD
and hons-AIG modes are not complete.  Shape specifiers don't exist yet.
Parametrization doesn't exist yet.  Many of the usual ways of doing things in
GL are done differently in FGL.</p>

<p>Here are some places to get started:

<ul>
<li>@(see gl-object)</li>
<li>@(see fgl-rewrite-rules)</li>
<li>@(see fgl-idioms)</li>
<li>@(see fgl-primitives)</li>
</ul>
")

(defxdoc fgl-rewrite-rules
  :parents (fgl)
  :short "Differences between FGL and ACL2 rewrite rules"
  :long "<p>FGL rewrite rules are really just ACL2 rewrite rules.  But this
doesn't mean that any good ACL2 rewrite rule is a good FGL rewrite rule, or
vice versa.  A particularly important difference is that @(see syntaxp) and
@(see bind-free) forms receive <see topic='@(url gl-object)'>GL symbolic
objects</see> as their inputs, rather than ACL2 terms.  GL rewrite rules also
allow a special form called @(see syntax-bind) which allows free variables to
be bound as with @(see bind-free), but in the RHS of the rewrite rule rather
than in the hyps.  They additionally support a form @(see abort-rewrite) which
causes the application of the rule to be aborted when encountered in the RHS,
similarly to if a hypothesis was not relieved.</p>

<h3>Creating and Removing FGL Rewrite Rules</h3>
<p>An FGL rewrite rule is an ACL2 rewrite rule.  You can register an existing
ACL2 rewrite rule for use in FGL using:</p>
@({
 (fgl::add-gl-rewrite my-rule)
 })
<p>And you can disable that rule for use by FGL using:</p>
@({
 (fgl::remove-gl-rewrite my-rule)
 })
<p>To create a new rewrite rule and enable it for FGL, you may use:</p>
@({
 (fgl::def-gl-rewrite my-rule
    body
   :hints ...)
 })
<p>This just expands to:</p>
@({
 (defthmd my-rule ...)
 (fgl::add-gl-rewrite my-rule)
 })

<p>FGL also supports rewrite rules that are triggered not on the leading
function symbol of the LHS, but on the leading function symbol of an
if-then-else branch.  These rules can be added using
@('(fgl::add-gl-branch-merge my-rule)') and they can be created using
@({
 (fgl::def-gl-branch-merge my-rule
    body
    ...)
 })

<p>A suitable branch merge rule has a left-hand side of the form @('(if test
then else)') where @('test') and @('else') are variables and @('then') is a
function call.</p>


<h3>Advanced Features</h3>

<p>FGL rewrite rules support ACL2's @(see syntaxp) and @(see bind-free)
hypothesis forms.  However, it generally won't work to use the same rewrite
rule in both the ACL2 and FGL rewriters if it has syntaxp or bind-free
hypotheses, because in FGL the variables in the syntaxp/bind-free forms will be
bound to symbolic objects, whereas in ACL2 they will be bound to
terms. Therefore to use syntaxp, bind-free, and syntax-bind (discussed below),
one needs to be familiar with FGL symbolic objects -- see @(see gl-object).</p>

<p>Two additional features support a new style of programming rewrite rules.
@('Syntax-bind') allows functionality similar to bind-free, but available
within the right-hand side of a rewrite rule.  @('Abort-rewrite') allows the
rewrite operation to be cancelled partway through interpreting the right-hand
side.</p>

<p>Here is an example that uses both syntax-bind and abort-rewrite, from
\"bitops.lisp\":</p>

@({
  (def-gl-rewrite logtail-to-logtail-helper
    (implies (syntaxp (not (gl-object-case n :g-concrete)))
             (equal (logtail n x)
                    (b* ((x (int x))
                         (n (nfix (int n)))
                         ((when (syntax-bind n-concrete (gl-object-case n :g-concrete)))
                          (logtail n x))
                         (n-width (syntax-bind n-width (gl-object-case n
                                                         :g-integer (max 0 (1- (len n.bits)))
                                                         :otherwise nil)))
                         ((unless (and n-width
                                       (check-unsigned-byte-p n-width n)))
                          (abort-rewrite (logtail n x)))
                         (n-rev (int-revapp n-width n 0)))
                      (logtail-helper n-rev n-width x)))))
 })

<p>When attempting to apply this rewrite rule, the FGL rewriter starts in much
the same way as the ACL2 rewriter.  As a precondition for attempting to apply
this rule, the term we are rewriting must be a call of logtail, and that call
must unify with the LHS of this rule -- in this case any call of logtail will
do so.</p>

<p>Next, we relieve the hyps.  This rule only has one hyp, which is a
syntaxp call; we check that @('n') is not a @(':g-concrete') object.</p>

<p>Then we proceed by interpreting the RHS.  We bind @('x') to the result of
rewriting @('(int x)') (where @('int') is an alias for @('ifix') and rebind
@('n') to the result of rewriting @('(nfix (int n))'), and then we encounter
our first syntax-bind form.  The syntax-bind form has the free variable
@('n-concrete'), which is here to logically represent the result we get from
evaluating the syntax-bind form.  A syntax-bind form is logically equivalent to
its first argument, so when we prove @('logtail-to-logtail-helper') correct we
prove it with the free variable @('n-concrete') in place of the syntax-bind.
That means we are logically justified in returning anything we want from the
syntax-bind form -- since n-concrete is a free variable not previously bound,
the rule is applicable for any value of n-concrete.  In this case we evaluate
@('(gl-object-case n :g-concrete)').  This will produce a Boolean value, which
is a concrete GL object representing itself.  If true, then n is concrete and
we will produce the result of again rewriting @('(logtail n x)') -- note that
we haven't created a loop here because the syntaxp hyp required that the
original @('n') was not concrete. Otherwise, we proceed with the next
syntax-bind form.</p>

<p>This next syntax-bind form (note it must use a different free variable than
the other form!) returns either some natural number value or else NIL.  Again,
either way it is a concrete object representing itself.  We bind this to
@('n-width').  We then require that n-width is nonnil and that we can show
@('n') satisfies @('(unsigned-byte-p n-width n)') (note: check-unsigned-byte-p
is an alias for unsigned-byte-p which has rules that try to prove it cheaply).
If not, then we come to an @('abort-rewrite') form.  When FGL arrives at an
abort-rewrite form, it aborts the current rewrite rule attempt, ignoring the
form inside the abort-rewrite.  (In this case the form @('(logtail n x)')
inside the abort-rewrite was selected to make it easy to prove
@('logtail-to-logtail-helper') correct.)  Otherwise, we go on with our rewrite.</p>

<p>Note we needed to know @('(unsigned-byte-p n-width n)') in order to prove
@('logtail-to-logtail-helper').  The @('syntax-bind') form produces the correct
number, but while proving @('logtail-to-logtail-helper') we don't know that.
Fortunately, it's fairly efficient to verify that after the fact using
@('check-unsigned-byte-p').</p>

")

(defxdoc fgl-idioms
  :parents (fgl))

(defxdoc fgl-primitives
  :parents (fgl))
