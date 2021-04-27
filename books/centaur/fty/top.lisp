; FTY type support library
; Copyright (C) 2014 Centaur Technology
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

(in-package "FTY")
(include-book "fixtype")
(include-book "fixequiv")
(include-book "deftypes")
(include-book "basetypes")
(include-book "baselists")
(include-book "visitor")

(defxdoc fty
  :parents (acl2::macro-libraries)
  :short "FTY is a macro library for introducing new data types and writing
type-safe programs in ACL2.  It automates a systematic discipline for working
with types that allows for both efficient reasoning and execution."

  :long "<p>FTY, short for <i>fixtype</i>, is a library for type-safe
programming in ACL2.  It provides significant automation for introducing new
data types and using data types according to the ``<see topic='@(url
fty-discipline)'>fixtype discipline</see>.''  Following this discipline allows
you to write type-safe programs that support efficient reasoning (by minimizing
the need for type-related hypotheses) and also have good execution
efficiency.</p>

<p>FTY is now used extensively at <a href='http://www.centtech.com/'>Centaur
Technology</a> for data structures in large libraries like @(see acl2::vl) and
@(see acl2::sv).</p>

<p>Here are the major components of FTY, roughly in order from low-level to
high-level utilities:</p>

<ul>

<li>@(see deffixtype) &mdash; Records the associations between type predicates,
fixing functions, and equivalence relations, and can automatically generate
equivalence relations for your types.  These associations are used by the
higher-level fty macros.</li>

<li>@(see basetypes) &mdash; Sets up the @('deffixtype') associations for many
common ACL2 base types (numbers, symbols, strings, ...).</li>

<li>@(see deffixequiv) and @(see deffixequiv-mutual) &mdash; Macros that
automate the (otherwise tedious) congruence proofs required for each function
that follows the fixtype discipline.</li>

<li>@(see defprod), @(see deflist), etc. &mdash; Macros for introducing new
simple data types.</li>

<li>@(see deftypes) &mdash; Macro for generating mutually recursive data types,
built on top of @(see defprod), (see deflist), etc.</li>

</ul>")


(defxdoc fty-discipline
  :parents (fty)
  :short "The fixtype approach to type-safe programming in ACL2."

  :long "<p>The @(see FTY) library is based on a systematic discipline for
using types in ACL2 definitions.  This discipline is easy on the prover and
provides good execution performance.</p>

<h3>The FTY Discipline</h3>

<p>The FTY discipline consists of five conditions on data types and the
functions that use those types:</p>

<ol>

<li>A ``type'' <color rgb='#900090'>foo</color> corresponds to a
<b>recognizer</b>, say @('foo-p'), which is a predicate that returns true when
its argument is a valid <color rgb='#900090'>foo</color> object.</li>

<li>Each type <color rgb='#900090'>foo</color> has an associated <b>fixing
function</b>, say @('foo-fix').  This function must be the identity on <color
rgb='#900090'>foo</color> objects, and must coerce any other ACL2 object to
some valid <color rgb='#900090'>foo</color>.  That is, @('foo-fix') must
satisfy:

@({
    (foo-p (foo-fix x)),

    (implies (foo-p x)
             (equal (foo-fix x) x))
})</li>

<li>Each type <color rgb='#900090'>foo</color> has an associated <b>
equivalence relation</b>, say @('foo-equiv').  This must be an ordinary ACL2
@(see acl2::equivalence) relation that is essentially defined by the fixing
function.  That is, @('foo-equiv') must satisfy:

@({
    (equal (foo-equiv x y)
           (equal (foo-fix x) (foo-fix y)))
})</li>

<li>Every function that takes an argument of the <color
rgb='#900090'>foo</color> type should have an equality @(see acl2::congruence)
with @('foo-equiv') on that argument.  For instance, if @('use-foo') takes a
single <color rgb='#900090'>foo</color> argument, then it should satisfy:

@({
     (implies (foo-equiv x y)
              (equal (use-foo x) (use-foo y)))
})</li>

<li>Every function that returns a value of the <color rgb='#900090'>foo</color>
type should do so unconditionally.  For instance, if @('update-foo') returns a
<color rgb='#900090'>foo</color>, then it should satisfy:

@({
    (foo-p (update-foo x))
})</li>

</ol>

<h3>How does the FTY Library Help?</h3>

<p>To support items 1-3, the FTY library provides macros to automate the
introduction of many common kinds of types, their associated fixing functions,
and their corresponding equivalence relations.  It also keeps track of the
associations for all ``known types'' that obey this discipline (see @(see
deffixtype)).</p>

<p>To support items 4-5 requires some care when writing your functions.  But
this is usually not too bad.  If your types already have associated fixing
functions and equivalence relations, then 4-5 are easy to engineer:</p>

<ul>

<li>If you build on existing functions that already satisfy these requirements,
they are likely to follow naturally.</li>

<li>Otherwise, you can simply fix each of the inputs to a function to their
appropriate types for free, using @(tsee mbe).</li>

</ul>

<p>For instance, here is a function that obeys the FTY discipline for natural
numbers by simply fixing its argument before operating on it.  Observe that
thanks to the @('mbe'), execution efficiency is unaffected by the additional
step of fixing @('n').</p>

@({
    (defun nat-add-5 (n)
      (declare (xargs :guard (natp n)))
      (let ((n (mbe :logic (nfix n) :exec n)))
        (+ n 5)))
})

<p>However, writing these @('mbe') forms at the beginning of all of your
functions can be unwieldy.  A more convenient approach is to put the @('mbe')
inside the fixing function itself and inline the fixing function.  This enables
you to call the fixing function anywhere without any execution penalty, though
it does add a guard obligation.</p>

@({
    (define foo-fix ((x foo-p))
      :inline t
      (mbe :logic ...
           :exec x))

    (define munge-foo ((x foo-p))
      (b* ((x (foo-fix x)))
        (bar (baz x) (xyzzy x))))
})

<p>There are versions of the ACL2 built-in fixing functions @(tsee nfix) and
@(tsee ifix) which follow the above discipline, called @(tsee lnfix) and @(tsee
lifix):</p>

@({
    (define nat-add-5 ((n natp))
      (b* ((n (lnfix n)))
        (+ n 5)))
})

<p>FTY provides macro support for automatically proving the congruence rules
mentioned in item 4; see @(see deffixequiv) and @(see deffixequiv-mutual).
Meanwhile, for a convenient way to prove the unconditional return-value
theorems mentioned in item 5, see the @(see std::returns-specifiers) feature of
@(see std::define).</p>

<p>Having unconditional return types and congruences is beneficial in and of
itself.  But the main advantage of using the fixtype discipline is that in
complex programs, program reasoning can be done while largely avoiding
extensive <see topic=\"@(url acl2::backchaining)\">backchaining</see> involving
proofs about type information.</p>

<p>Because each function's inputs are fixed to the appropriate type before
being used, theorems about the function do not typically need hypotheses
stating that the inputs are of that type.  And when a FTY-disciplined
function's result is passed into some other function, the unconditional returns
theorem for the first function allows us to instantly discharge any
type-related goals that arise in guard theorems or other theorems about the
second function.</p>")


(defxdoc deffixtype
  :parents (fty)
  :short "Define a new type for use with the @(see fty-discipline)."

  :long "<p>In its most basic form, @('deffixtype') just associates a new type
name with the corresponding predicate, fixing function, and equivalence
relation.  It stores this association in a @(see table), @('fty::fixtypes').
The type then becomes ``known'' to other @(see fty) macros such as @(see
deffixequiv), @(see defprod), and so on.</p>


<h4>Basic Example</h4>

<p>You could use the following to define the <color rgb='#900090'>nat</color>
type with the recognizer @(see natp), the fixing function @(see nfix), the
equivalence relation @(see nat-equiv), and @(see natp) as the preferred @(see
xdoc::xdoc) topic when linking to this type.</p>

@({
  (fty::deffixtype nat
    :pred  natp
    :fix   nfix
    :equiv nat-equiv
    :topic natp)
})

<p>For this to be sensible, the recognizer, fixing function, and equivalence
relation should satisfy the constraints described in @(see fty-discipline), and
the equivalence relation must have already be admitted by @(see defequiv).</p>

<p>In practice, you shouldn't really need to introduce @('deffixtype') forms
for basic ACL2 types like @(see natp) by yourself.  Instead, see the @(see
basetypes) book.</p>


<h4>More Typical Example</h4>

<p>Very often, the equivalence relation for a new type is ``induced'' by the
fixing function in a completely standard way.  Once you have introduced your
recognizer and fixing function, you can just have @('deffixtype') introduce the
equivalence relation for you.  For example:</p>

@({
    (defun foop (x)
      (declare (xargs :guard t))
      (and (consp x)
           (equal (car x) 'foo)))

    (defun-inline foo-fix (x)
      (declare (xargs :guard (foop x)))
      (mbe :logic (if (foop x) x '(foo . nil))
           :exec x))

    (deffixtype foo
      :pred   foop
      :fix    foo-fix
      :equiv  foo-equiv
      :define t         ;; define foo-equiv for me
      :forward t        ;; prove some useful theorems about foo-equiv
      )
})

<p>Besides registering the <color rgb='#900090'>foo</color> type with FTY, this
will introduce @('foo-equiv') essentially as if you had written:</p>

@({
      (defun-inline foo-equiv (x y)
        (declare (xargs :guard (and (foop x)
                                    (foop y))))
        (equal (foo-fix x) (foo-fix y)))
})

<p>It will then prove @('foo-equiv') is an equivalence relation and prove some
minor boilerplate theorems.</p>


<h4>General Form</h4>

@({
  (deffixtype widget       ;; name of the new type for fty
    :pred  widget-p
    :fix   widget-fix
    :equiv widget-equiv

    ;; optional arguments           ;; default
    :executablep bool               ;; t
    :define      bool               ;; nil
    :inline      bool               ;; t
    :equal       {eq,eql,equal,...} ;; equal
    :forward     bool               ;; nil
    :hints       ((\"Goal\"...))    ;; nil
    :verbosep    bool               ;; nil
    :topic       symbol
    )
})

<h4>Optional arguments</h4>


<h5>:verbosep</h5>

<p>@(':verbosep') can be set to T to avoid suppressing theorem prover output
during the resulting forms.  This can be useful if the macro causes an error
and you need to debug it.</p>


<h5>:define</h5>

<p>@(':define') is NIL by default; if set to T, then the equivalence relation
is assumed not to exist yet, and is defined as equality of fix, with
appropriate rules to rewrite the fix away under the equivalence and to
propagate the congruence into the fix.</p>


<h5>:forward</h5>

<p>Only matters when @('define') is T.  When @(':forward') is T, four
additional lemmas will be proved about the new equivalence relation and stored
as @(see acl2::forward-chaining) rules.  In particular, the following will all
forward-chain to @('(widget-equiv x y)'):</p>

<ul>
 <li>@('(equal (widget-fix x) y)')</li>
 <li>@('(equal x (widget-fix y))')</li>
 <li>@('(widget-equiv (widget-fix x) y)'), and</li>
 <li>@('(widget-equiv x (widget-fix y))')</li>
</ul>


<h5>:hints</h5>

<p>Only matters when @('define') is NIL.  This allows you to give @(see
acl2::hints) for the theorem that shows the new equivalence relation holds
between @('x') and @('y') exactly when @('(equal (widget-fix x) (widget-fix
y))').</p>

<p>(When @('define') is T we don't need to prove this, because it's exactly the
definition of the equivalence relation we introduce.)</p>


<h5>:inline</h5>

<p>Minor efficiency option, only matters when @(':define') is T.  When
@(':inline') is T (which is the default), the new equivalence relation's
function will be introduced using @(see defun-inline) instead of @(see
defun).</p>


<h5>:equal</h5>

<p>Minor efficiency option, only matters when @('define') is T.  By default,
the new equivalence relation will compute the @('equal') of the fixes.  In some
cases, your type may be so restrictive that a more efficient equality check
like @(see eq) or @(see eql) can be used instead.  For instance, if you are
defining character equivalence, you might use @(':equal eql') so that your new
equivalence relation will compute the @('eql') of the fixes instead of the
@('equal') of the fixes.</p>


<h5>:executablep</h5>

<p>@(':executablep') should be set to NIL if either the fixing function or
predicate are @(see acl2::non-executable) or especially expensive.  This mainly
affects, in @('deffixequiv') and @('deffixequiv-mutual'), whether a theorem is
introduced that normalizes constants by applying the fixing function to
them.</p>


<h5>:topic</h5>

<p>Set up a preferred @(see xdoc::xdoc) documentation topic name for this type.
When other documentation topics want to refer to this type, they should link to
the preferred @(':topic').  This may be useful when your type is embedded
within some larger @(see defprod) or similar.</p>

<p>Usually you don't need to provide a @(':topic') explicitly.  The @(':topic')
will default to the name of the new type name being defined, e.g., @('widget').
We usually use the type name as the ``main'' topic.  For instance, @('widget')
would typically be the parent topic for @('widget-p'), @('widget-fix'),
@('widget-equiv'), and related functions.  This convention is followed
throughout the @(see deftypes) family of macros.</p>

<p>However, this convention is sometimes inappropriate, especially for built-in
ACL2 types such as @(see natp) and @(see booleanp).  In these cases, we'd
prefer to link to existing documentation such as the recognizers.</p>")


(defxdoc deffixequiv
  :parents (fty)
  :short "A macro for automatically proving boilerplate theorems that show a
function has the appropriate @(see congruence)s for its typed arguments."

  :long "<p>The @('deffixequiv') macro can be used to automate certain tedious
theorems that arise when following the @(see fty-discipline).  In particular,
it is intended to help achieve condition 4:</p>

<blockquote><i>Every function that takes an argument of the <color
rgb='#900090'>foo</color> type should have an equality @(see congruence) with
@('foo-equiv') on that argument.</i></blockquote>


<h3>Example</h3>

<p>As an example, consider the following trivial function, introduced
with @(see std::define).</p>

@({
    (define multiply-and-add ((a natp)
                              (b natp)
                              (c natp))
      :returns (ans natp :rule-classes :type-prescription)
      (let ((a (lnfix a))
            (b (lnfix b))
            (c (lnfix c)))
        (+ (* a b)
           c)))
})

<p>Given this definition, the following @('deffixequiv') form will
automatically prove @(see nat-equiv) congruences and certain related rules for
each of the three arguments of @('multiply-and-add'):</p>

@({
    (fty::deffixequiv multiply-and-add)
})


<p>This example is especially concise and automatic because @('deffixequiv')
has a special integration with @(see std::define): it ``knows'' how to:</p>

<ul>
<li>look up the @(see std::extended-formals) from the definition,</li>
<li>notice that these arguments are @(see natp)s,</li>
<li>look up the corresponding fixing function and equivalence relation
    (assuming the @(see basetypes) book has been loaded), and then</li>
<li>generate and prove the correct theorems.</li>
</ul>

<p>It is possible, but less automatic, to use @('deffixequiv') on functions
that have not been introduced with @('define'); see the <i>Advanced Form</i>
below.</p>

<p>It is also possible, and even <b>more automatic</b>, to instruct @(see
std::define) to automatically attempt a @(see deffixequiv) on its own: see
@(see fixequiv-hook).</p>


<h3>Theorems Generated</h3>

<p>In most cases, three theorems are generated for each argument.  Continuing
the @('multiply-and-add') example, here are the theorems that will be generated
for the @('c') argument:</p>

@({
    (defthm multiply-and-add-of-nfix-c
      (equal (multiply-and-add a b (nfix c))
             (multiply-and-add a b c)))

    (defthm multiply-and-add-of-nfix-c-normalize-const
      (implies (syntaxp (and (quotep c)
                             (not (natp (cadr c)))))
               (equal (multiply-and-add a b c)
                      (multiply-and-add a b (nfix c)))))

    (defthm multiply-and-add-nat-equiv-congruence-on-c
      (implies (nat-equiv c c-equiv)
               (equal (multiply-and-add a b c)
                      (multiply-and-add a b c-equiv)))
      :rule-classes :congruence)
})

<p>In rare cases, certain types may have a predicate and/or fixing function
that is either expensive to execute or even @(see acl2::non-executable).  In
this case, the second theorem, which normalizes constant values by fixing them
to the correct type, will not work well.</p>

<p>The recommended way to suppress this theorem is to add @(':executablep nil')
to the @(see deffixtype) form.  It is also possible to skip the
@('normalize-const') theorem on an individual argument-basis (see below for
details), but this is usually going to be much more tedious: you will typically
have many functions that operate on your type, and you probably don't want to
have to suppress this theorem for each argument of each function!</p>



<h3>General Forms</h3>

<p>In the general case, there are two ways to invoke @('deffixequiv').</p>

<h4>Basic Form &mdash; :omit</h4>

@({
     (deffixequiv function-name
       :omit (a b)     ;; optional
       :hints (...)    ;; applied to all arguments
       )
})

<p>This form only works for functions introduced with @(see define).  It tries
to prove the theorems described above for each argument that has a known type,
unless the argument is explicitly listed in @(':omit').</p>


<h4>Advanced Form &mdash; :args</h4>

@({
    (deffixequiv function-name
      :args (a                 ;; derive type from DEFINE
             (b :hints (...))  ;; derive type from DEFINE, custom hints
             (c natp ...))     ;; explicitly use type NATP
      :hints (...))            ;; hints for all arguments
})

<p>This form provides finer-grained control over exactly what will be proven.
In this form, the @(':args') say which formals to generate theorems about, and
no theorems will be generated about any formals that are omitted from
@(':args').  The @(':args') also allow you to manually control what type the
argument will be assumed to have, specify hints, and so forth.</p>

<p>This form can work even on functions that are not introduced with @(see
define) <b>if</b> a type is given explicitly for each argument.  On the other
hand, if the function is introduced with @('define'), then you can either infer
the type of the argument (e.g., @('a') above) or manually override it (e.g.,
@('c') above).</p>

<p>As a special consideration, you can also skip the @('normalize-const')
theorem for a certain argument like this:</p>

@({
     (deffixequiv foo
       :args ((c nat :skip-const-thm t)))
})

<h3>Support for Mutual Recursion</h3>

<p>The @('deffixequiv') form typically cannot be used successfully for mutually
recursive functions, e.g., those created with @(see defines).  Instead, see
@(see deffixequiv-mutual).</p>")


(defxdoc deffixequiv-mutual
  :parents (fty)
  :short "Like @(see deffixequiv), but for mutually-recursive functions."

  :long "<p>See @(see deffixequiv).  The @('deffixequiv-mutual') macro attempts
to prove the same theorems, but for a clique of mutually recursive functions.
This is trickier because, as per usual with mutually recursive functions, we
typically need to prove the congruences all together, for all of the functions
in the clique at once, using a mutually inductive proof.</p>

<p>Accordingly, the @('deffixequiv-mutual') macro attempts to prove a
mutually-inductive theorem of which the individual @('function-of-fix-arg')
theorems are corollaries, then uses these to prove the constant-normalization
and congruence theorems.  (These three theorems are discussed in @(see
deffixequiv).</p>

<p>Important Note: @('deffixequiv-mutual') will not work if the mutual
recursion in question was not created using @(see defines).</p>

<h3>Examples</h3>

<p>The syntax of @('deffixequiv-mutual') is similar to that of
@('deffixequiv').  You again have the choice of either providing @(':omit'),
@('args'), or both.  However, are also some extensions of these options, as
described below.</p>

<p>As a running example, consider the following mutual recursion:</p>

@({
    (defines foo-bar-mutual-rec
      (define foo ((x integerp) y (z natp))
        :flag f
        ...)
      (define bar ((x integerp) y (z nat-listp))
        :flag b
        ...))
})

<p>Here, then, are some ways to invoke @('deffixequiv-mutual'):</p>

@({

 ;; Derives all argument types from guards and proves
 ;; them all in one mutual induction.
 ;;
 ;; Note: use name of defines form, foo-bar-mutual-rec,
 ;;       not the name of one of the functions!
 (deffixequiv-mutual foo-bar-mutual-rec)

 ;; Proves only things pertaining to the X argument of both functions
 (deffixequiv-mutual foo-bar-mutual-rec :args (x))
 ;; Same:
 (deffixequiv-mutual foo-bar-mutual-rec :omit (y z))

 ;; Proves string congruence of Y on both functions
 (deffixequiv-mutual foo-bar-mutual-rec :args ((y string)))

 ;; Proves string congruence of y in foo and string-listp in bar
 (deffixequiv-mutual foo-bar-mutual-rec
                     :args ((foo (y stringp))
                            (bar (y string-listp))))

 ;; Omit x in foo and y in bar
 (deffixequiv-mutual foo-bar-mutual-rec
                     :omit ((foo x) (bar y)))

 ;; Various combinations of :args usages
 (deffixequiv-mutual foo-bar-mutual-rec
    :args (x                       ;; all functions, automatic type
           (z natp :hints (...))   ;; all functions, explicit type
           (foo (y stringp :skip-const-thm t :hints (...)))
                                   ;; foo only, explicit type
           (bar (z nat-listp)))    ;; override non-function-specific entry
    :hints (...))  ;; hints for the whole inductive proof
})")


(defxdoc fixequiv-hook
  :parents (deffixequiv)
  :short "An @(see std::post-define-hook) for automatically proving @(see fty)
congruences rules."
  :long "<p>The @(':fix') hook allows you to instruct @(see std::define) to
automatically try to infer and prove appropriate congruence rules as in @(see
deffixequiv).</p>

<p>Typical usage, to try to automatically prove congruences everywhere, is to
simply add the following to the top of your file, section, encapsulate, or
similar:</p>

@({
    (local (std::add-default-post-define-hook :fix))
})

<p>You will almost certainly want to ensure that this is done @(see local)ly,
since otherwise it will affect all users who include your book.</p>

<p>For finer-grained control or to suppress equivalences for a particular
function, you can use the @(':hooks') argument to an individual define,
e.g.,</p>

@({
     (define none ((n natp))    ;; don't prove any congruences
        :hooks nil
        n)

     (define custom ((a natp) (b natp))   ;; prove congruences only
        :hooks ((:fix :omit (b)))         ;; for A, not for B
        (list (nfix a) b))

     (define custom2 ((a natp) (b natp))       ;; prove congruences other than
        :hooks ((:fix :args ((a integerp)      ;; those the formals suggest
                             (b rationalp))))
        (list (ifix a) (rfix b)))
})

<p>The arguments beyond @(':fix') get passed to @(see deffixequiv), so see its
documentation for more options.</p>")

(defxdoc set-fixequiv-guard-override
  :parents (deffixequiv)
  :short "Override the type that is associated with a guard function for purposes
          of determining automatic congruences with @(see deffixequiv)."
  :long
  "<p>The form:</p>
@({
 (set-fixequiv-guard-override my-guard my-type)
 })

<p>makes it so that @(see deffixequiv), @(see deffixequiv-mutual), and @(see
fixequiv-hook) will prove congruences appropriate for @('my-type') for @(see
define) formals guarded with @('my-guard').</p>")


(defxdoc deftypes
  :parents (fty)
  :short "Generate mutually recursive types with equivalence relations and
fixing functions."

  :long "<p>@('Deftypes') generates mutually-recursive types. We'll begin with
an example.</p>

@({
 ;; Associate fixing functions and equivalence relations
 ;; with component types.  Note: this is done for most
 ;; basic types in the book centaur/fty/basetypes.lisp.

 (deffixtype integer :pred integerp :fix ifix :equiv int-equiv :define t)
 (deffixtype symbol :pred symbolp :fix symbol-fix :equiv sym-equiv :define t)

 (deftypes intterm
   (defflexsum intterm
     (:num :cond (atom x)
      :fields ((val :type integerp :acc-body x))
      :ctor-body val)
     (:call
      :fields ((fn :type symbol :acc-body (car x))
               (args :type inttermlist :acc-body (cdr x)))
      :ctor-body (cons fn args)))
   (deflist inttermlist
     :elt-type intterm))
})

<p>This generates recognizers and fixing functions for two new types:</p>
<ul>
<li>intterm, which is either a \"num\" consisting of a single integer or a
\"call\" consisting of a symbol consed onto an inttermlist,</li>
<li>inttermlist, which is a list of intterms.</li>
</ul>

<p>The @('deftypes') form just bundles together two other forms -- a @(see
defflexsum) and a @(see deflist).  These two forms would be admissible by
themselves, except that the types they are defining are mutually recursive, and
therefore so are their recognizer predicates and fixing functions.</p>

<p>The syntax and behavior of individual type generators is documented further
in their own topics.  So far, the supported type generators are:</p>
<ul>
<li>@(see deflist): a list of elements of a particular type</li>
<li>@(see defprod): a product (AKA record, aggregate, struct) type</li>
<li>@(see defalist): an alist mapping keys of some type to values of some type</li>
<li>@(see defset): an oset of elements of a particular type</li>
<li>@(see defomap): an omap mapping keys of some type to values of some type</li>
<li>@(see deftagsum): a sum-of-products (AKA tagged union) type</li>
<li>@(see defflexsum): a very flexible (and not as automated) sum-of-products
type used to implement @(see defprod) and @(see deftagsum).</li>
</ul>

<p>@('Deftypes') and its component type generators are intended to
implement the type discipline described in the @(see fty) topic.  In
particular, this means:</p>
<ul>
<li>the type predicates generated by any of these events each have an
associated fixing function and equivalence relation, and these associations
are recorded using a @(see deffixtype) event</li>
<li>accessors and constructors of the sum and product types unconditionally
return values of the appropriate type</li>
<li>accessors and constructors have equality congruences based on the types of
their arguments.</li>
</ul>

<p>To support these nice properties, all the component types (the fields of
products, elements of lists, keys and values of alists) are required to also
have an associated fixing function and equivalence relation, either produced by
a @('deftypes') compatible type generator or recorded by a @(see deffixtype)
event.  (They may also be untyped.)  The \"preparation\" forms in the example
above show how this can be done.  Also see @(see basetypes) for some base types
with fixing functions.</p>")


(defxdoc deflist
  :parents (fty deftypes)
  :short "Define a list type with a fixing function, supported by @(see deftypes)."

  :long "<p>@('Deflist') provides a recognizer predicate, fixing function, and
a few theorems defining a list of elements of a certain type.</p>

<p>@('Deflist') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its element type must
either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  See @(see basetypes) for
some base types with fixing functions.</p>

<p>The syntax of @('deflist') is:</p>
@({
  (deflist foolist
    :elt-type foo      ;; required, must have a known fixing function
    :parents (...)     ;; xdoc
    :short \"...\"       ;; xdoc
    :long \"...\"        ;; xdoc
    :measure (+ 1 (* 2 (acl2-count x)))
                       ;; default: (acl2-count x)
    :xvar x            ;; default: x, or find x symbol in measure
    :prepwork          ;; admit these events before starting
    :pred foolistp     ;; default: foolist-p
    :fix foolistfix    ;; default: foolist-fix
    :equiv foolist-=   ;; default: foolist-equiv
    :count foolistcnt  ;; default: foolist-count
                       ;; (may be nil; skipped unless mutually recursive)
    :no-count t        ;; default: nil, same as :count nil
    :true-listp t      ;; default: nil, require nil final cdr
    :elementp-of-nil   ;; default: :unknown, where nil has type foo or not
  )
 })

<p>Only the name and the @(':elt-type') argument is required.</p>

<p>As part of the event, @('deflist') calls @(see std::deflist) to produce
several useful theorems about the introduced predicate.</p>

<p>@('Deflist') (by itself, not when part of mutually-recursive deftypes form)
also allows previously defined list predicates.  For example, the following
form produces a fixing function for ACL2's built-in @(see string-listp)
predicate:</p>

@({ (deflist string-list :pred string-listp :elt-type stringp) })

<p>If the predicate has been previously defined by @(tsee std::deflist), then
the @(':true-listp') and @(':elementp-of-nil') values of the @('fty::deflist')
must be the same as the ones of the @(tsee std::deflist).  Otherwise, the
@('fty::deflist') may attempt to generate some theorems that have the same name
as, but slightly different formulas from, theorems generated by the @(tsee
std::deflist), causing an error.</p>

<p>The theorems generated by @('deflist') depend on the currently included
books.  For instance, if @('std/lists/sets.lisp') is included, certain theorems
involving @(tsee member) are generated.  This provides more modularity, by not
automatically including something like @('std/lists/top.lisp') with
@('deflist').  If @('deflist') is called again with the same argument after
including more books, additional theorems corresponding to the newly included
books may be generated.  See also the `Pluggable Architecture' section of
@(tsee std::deflist).</p>")


(defxdoc defalist
  :parents (fty deftypes)
  :short "Define an alist type with a fixing function, supported by @(see deftypes)."
  :long "<p>@('Defalist') provides a recognizer predicate, fixing function, and
a few theorems defining an alist with keys of some type mapping to values of some type.</p>

<p>@('Defalist') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its key and value types
must either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  (They may also be
untyped.)  See @(see basetypes) for some base types with fixing
functions.</p>

<p>The syntax of defalist is:</p>
@({
  (defalist fooalist
    :key-type symbol
    :val-type foo
    :parents (...)     ;; xdoc
    :short \"...\"       ;; xdoc
    :long \"...\"        ;; xdoc
    :measure (+ 1 (* 2 (acl2-count x)))
                       ;; default: (acl2-count x)
    :xvar x            ;; default: x, or find x symbol in measure
    :prepwork          ;; admit these events before starting
    :pred fooalistp     ;; default: fooalist-p
    :fix fooalistfix    ;; default: fooalist-fix
    :equiv fooalist-=   ;; default: fooalist-equiv
    :count fooalistcnt  ;; default: fooalist-count
                       ;; (may be nil; skipped unless mutually recursive)
    :no-count t        ;; default: nil, same as :count nil
    :true-listp t      ;; default: nil, require nil final cdr
    :strategy :drop-keys ;; default: :fix-keys
  )
 })

<p>The keyword arguments are all optional, although it doesn't make much sense
to define an alist with neither a key-type nor value-type.</p>

<p>The @(':strategy') keyword changes the way the fixing function works; by
default, every pair in the alist is kept but its key and value are fixed.  With
@(':strategy :drop-keys'), pairs with malformed keys are dropped, but malformed
values are still fixed. @(See Defmap) is an abbreviation for @('defalist') with
@(':strategy :drop-keys').</p>

<p>As part of the event, deflist calls @(see std::deflist) to produce several
useful theorems about the introduced predicate.</p>

<p>Defalist (by itself, not when part of mutually-recursive deftypes form) also
allows previously defined alist predicates.  For example, the following form
produces a fixing function for ACL2's built-in @('timer-alistp') predicate:</p>

@({
 (defalist timer-alist :pred timer-alistp
                       :key-type symbolp
                       :val-type rational-listp)
 })

<p>Similarly to @(tsee deflist), the theorems generated by @('defalist') depend
on the currently included books, and calling @('defalist') again with the same
argument after including more books may generate additional theorem.  See
@(tsee deflist) for more details.</p>")


(defxdoc defmap
  :parents (fty deftypes)
  :short "Define an alist type with a fixing function that drops pairs with malformed keys rather than fixing them."
  :long "<p>@('Defmap') is just an abbreviation for @('defalist') with the option
@(':strategy :drop-keys').</p>")


(defxdoc defprod
  :parents (fty deftypes)
  :short "Define a new product type, like a @('struct') in C, following the
@(see fty-discipline)."

  :long "<p>@('Defprod') is a macro for introducing @('struct')-like types.  It
can be used to conveniently define a recognizer, constructor, accessors, fixing
function, and equivalence relation, and other supporting macros and
documentation for a new struct-like type.  It automatically arranges so that
these new definitions follow the @(see fty-discipline).</p>

<p>@('Defprod') can be used in a standalone fashion to introduce simple (non
mutually-recursive) product types.  But it is also compatible with @(see
deftypes), so it can be used to create products that are mutually-recursive
with other @('deftypes') compatible type generators.</p>

<p>As with all @(see deftypes)-compatible type generators, its field types must
be types that are ``known'' to FTY.  That is, they must either refer to types
that have been introduced with @(see deffixtype) or that have been produced by
other FTY type generating macros.  (Fields can also be completely untyped.)
See also @(see basetypes) for some base types with fixing functions.</p>


<h3>Basic Example</h3>

@({
    (defprod sandwich
      ((bread   symbolp :default 'sourdough)
       (coldcut meatp)
       (spread  condimentp)))
})

<p>This example would produce:</p>

<ul>
<li>A recognizer @('sandwich-p').</li>
<li>A fixing function @('sandwich-fix').</li>
<li>An equivalence relation @('sandwich-equiv').</li>
<li>A constructor @('(sandwich bread coldcut spread)').</li>
<li>A constructor macro @('(make-sandwich :bread bread ...)'), which simply
expands to a constructor call but uses the given defaults.</li>
<li>A changer macro @('(change-sandwich x :bread bread ...)').</li>
<li>An accessor for each field, e.g., @('sandwich->bread').</li>
<li>A @(see b*) binder @('sandwich'), like those in @(see std::defaggregate).</li>
</ul>

<p>Much of this&mdash;the make/change macros, accessor names, b*
binders&mdash;is nearly identical to @(see std::defaggregate).  If you have
used @('defaggregate'), switching to @('defprod') should be very
comfortable.</p>


<p>General Syntax:</p>

@({
 (defprod prodname
    (list-of-fields)
    keyword-options)
 })

<p>The fields are @(see std::extended-formals), except that the guard must be
either simply a predicate or the call of a unary predicate on the field name.
Acceptable keyword arguments for each field are:</p>

<ul>

<li>@(':default'): default value of the field in its constructor macro</li>

<li>@(':rule-classes'): rule-classes for the return type theorem of the
accessor.</li>

</ul>


<h3>Name/Documentation Options</h3>

<dl>

<dt>@(':pred')</dt>
<dt>@(':fix')</dt>
<dt>@(':equiv')</dt>
<dt>@(':count')</dt>

<dd>These allow you to override the default function names, which
are (respectively) @('name-p'), @('name-fix'), @('name-equiv'), and
@('name-count').</dd>

<dd>As a special case, @(':count') may be nil, meaning no count function is
produced.  (A count function is only produced when this is mutually-recursive
with other type generators.)</dd>


<dt>@(':parents')</dt>
<dt>@(':short')</dt>
<dt>@(':long')</dt>

<dd>These let you customize the @(see xdoc) documentation produced for this
type.  The documentation generated for products will automatically list the
fields and link to their types; it's often convenient to put additional notes
directly in the fields, e.g.,

@({
    (defprod monster
      :parents (game)
      :short \"A monster to fight.\"
      ((name   stringp \"Name of the monster\")
       (health natp    \"How many hit points does the monster have?\")
       ...)
      :long \"<p>More details about monsters could go here.</p>\")
})</dd>

</dl>


<h3>Performance/Efficiency Options</h3>

<dl>

<dt>@(':tag')</dt>

<dd>Defaults to @('nil'), meaning that the product is untagged.  Otherwise it
must be a keyword symbol and this symbol will be consed onto every occurrence
of the object.</dd>

<dd>Having tags on your objects adds some execution/memory overhead, but
provides a reasonably nice way to distinguish different kinds of objects from
one another at runtime.</dd>


<dt>@(':layout')</dt>

<dd>Defaults to @(':alist'), but might instead be set to @(':tree'),
@(':fulltree') or @(':list').  This determines how the fields are laid out in
the object's representation.</dd>

<dd>The @(':alist') format provides the best readability/debuggability but is
the worst layout for execution/memory efficiency.  This layout represents
instances of your product type using an alist-like format where the name of
each field is next to its value.  When printing such an object you can easily
see the fields and their values, but creating these objects requires additional
consing to put the field names on, etc.</dd>

<dd>The @(':tree') or @(':fulltree') layouts provides the best efficiency and
worst readability.  They pack the fields into a compact tree structure, without
their names.  In @(':tree') mode, any @('(nil . nil)') pairs are compressed
into just @('nil').  In @(':fulltree') mode this compression doesn't happen,
which might marginally save time if you know your fields will never be in pairs
of @('nil')s.  Tree-based structures require minimal consing, and each accessor
simply follows some minimal, fixed car/cdr path into the object.  The objects
print as horrible blobs of conses that can be hard to inspect.</dd>

<dd>The @(':list') layout strikes a middle ground, with the fields of the
object laid out as a plain list.  Accessing the fields of such a structure may
require more @('cdr') operations than for a @(':tree') layout, but at least
when you print them it is still pretty easy to tell what the fields are.</dd>

<dd>Example: a tagless product with 5 fields could be laid out as follows:

@({
    `((,a . ,b) . (,c . (,d . ,e)))                  ;; :tree
    `(,a ,b ,c ,d ,e)                                ;; :list
    `((a . ,a) (b . ,b) (c . ,c) (d . ,d) (e . ,e))  ;; :alist
})</dd>


<dt>:hons</dt>

<dd>NIL by default.  When T, the constructor is defined using @(see hons)
rather than @(see cons), so your structures will always be structure shared.
This may improve memory efficiency in certain cases but is probably not a good
idea for most structures.</dd>

<dt>:inline</dt>

<dd>Default: @('(:acc :fix)'), meaning that the accessors and fixing function,
which for execution purposes is just the identity, will be defined as an @(see
inline) function.  This argument may also contain @(':xtor'), which causes the
constructor to be inlined as well, but this is typically less useful as the
constructor requires some amount of consing.  The option @(':all') (not in a
list) is also possible.</dd>

</dl>


<h3>Other Options</h3>

<dl>

<dt>@(':measure')</dt>

<dd>A measure is only necessary in the mutually-recursive case, but is probably
necessary then.  The default measure is @('(acl2-count x)'), but this may not
work in the mutually-recursive case because of the possibility that @('x')
could be (say) an atom, in which case the @('acl2-count') of @('x') will be no
greater than the @('acl2-count') of a field.  Often something like
@('(two-nats-measure (acl2-count x) 5)') is a good measure for the product,
where the other mutually-recursive types have a similar measure with smaller
second component.</dd>


<dt>@(':require')</dt>
<dt>@(':reqfix')</dt>

<dd>This adds a dependent type requirement; see the section on this feature
below.</dd>

</dl>


<h4>Experimental Dependent Type Option</h4>

<p>The top-level keyword @(':require') can add a requirement that the fields
satisfy some relation.  Using this option requires that one or more fields be
given a @(':reqfix') option; it must be a theorem that applying the regular
fixing functions followed by the @(':reqfix') of each field independently
yields fields that satisfy the requirement.  It should also be the case that
applying the reqfixes to fields already satisfying the requirement leaves them
unchanged.  For example:</p>

@({
     (defprod sizednum
       ((size natp)
        (bits natp :reqfix (loghead size bits)))
       :require (unsigned-byte-p size bits))
 })

<p>If there is more than one field with a @(':reqfix') option, these reqfixes
are applied to each field independently, after applying all of their types'
fixing functions.  For example, for the following to succeed:</p>

@({
     (defprod foo
       ((a atype :reqfix (afix a b c))
        (b btype :reqfix (bfix a b c))
        (c       :reqfix (cfix a b c)))
       :require (foo-req a b c))
})

<p>the following must be a theorem (assuming @('afix') and @('bfix') are the
fixing functions for @('atype') and @('btype'), respectively):</p>

@({
  (let ((a (afix a))
        (b (bfix b)))
    (let ((a (afix a b c))
          (b (bfix a b c))
          (c (cfix a b c)))
      (foo-req a b c)))
 })

<p>Notice the LET, rather than LET*, binding the fields to their reqfixes.  It
would NOT be sufficient for this to be true with a LET*.</p>")


(defxdoc deftagsum
  :parents (fty deftypes)
  :short "Define a (possibly recursive) tagged union, a.k.a. ``sum of
          products'' type."

  :long "<p>@('Deftagsum') produces a tagged union type consisting of several
product types, each with a tag to distinguish them.  It is similar in spirit to
ML or Haskell's recursive data types, although without the dependent-type
features.</p>

<p>@('Deftagsum') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, the types of the fields of
its products must each either be one produced by a compatible type generator or
else have an associated fixing function given by @(see deffixtype).  (Fields
can also be untyped.)  See @(see basetypes) for some base types with fixing
functions.</p>

<h3>Example</h3>

<p>Note: It may be helpful to be familiar with @(see defprod).</p>

@({
    (deftagsum arithtm
      (:num ((val integerp)))
      (:plus ((left arithtm-p)
              (right arithtm-p)))
      (:minus ((arg arithtm-p))))
 })

<p>This defines the following functions and macros:</p>

<ul>
<li>Recognizer @('arithtm-p')</li>
<li>Fixing function @('arithtm-fix')</li>
<li>Equivalence relation @('arithtm-equiv')</li>
<li>@('arithtm-kind'), which returns either @(':num'), @(':plus'), or
@(':minus') to distinguish the different kinds of arithtm objects</li>
<li>Constructors @('arithtm-num'), @('arithtm-plus'), @('arithtm-minus')</li>
<li>Accessors @('arithtm-num->val'), @('arithtm-plus->left'),
@('arithtm-plus->right'), and @('arithtm-minus->arg')</li>
<li>Constructor macros @('make-aritherm-num'), @('make-arithtm-plus'),
@('make-arithtm-minus')</li>
<li>Changer macros @('change-arithtm-num'), @('change-arithtm-plus'),
@('change-arithtm-minus')</li>
<li>@(see B*) binders @('arithtm-num'), @('arithtm-plus'),
@('arithtm-minus')</li>
<li>@('arithtm-case'), a macro that combines case splitting and accessor binding.</li>
</ul>



<p>Note: The individual products in a @('deftagsum') type are not themselves
types: they have no recognizer or fixing function of their own.  The guard for
accessors is the sum type and the kind, e.g., for @('arithtm-plus->right'),</p>
@({
 (and (arithtm-p x) (equal (arithtm-kind x) :plus))
 })

<h4>Using Tagsum Objects</h4>

<p>The following example shows how to use an arithtm object.  We define an
evaluator function that computes the value of an arithtm and a transformation
that doubles every leaf in an arithtm, and prove that the doubling function
doubles the value according to the evaluator.  The doubling function also shows
how the arithtm-case macro is used.  Note that the return type theorems and
the theorem about the evaluation of arithtm-double are all hypothesis-free --
a benefit of following a consistent type-fixing convention.</p>

@({
  (define arithtm-eval ((x arithtm-p))
    :returns (val integerp :rule-classes :type-prescription)
    :measure (arithtm-count x)
    :verify-guards nil
    (case (arithtm-kind x)
      (:num (arithtm-num->val x))
      (:plus (+ (arithtm-eval (arithtm-plus->left x))
                (arithtm-eval (arithtm-plus->right x))))
      (:minus (- (arithtm-eval (arithtm-minus->arg x)))))
    ///
    (verify-guards arithtm-eval))


  (define arithtm-double ((x arithtm-p))
    :returns (xx arithtm-p)
    :measure (arithtm-count x)
    :verify-guards nil
    (arithtm-case x
     :num (arithtm-num (* 2 x.val))
     :plus (arithtm-plus (arithtm-double x.left)
                         (arithtm-double x.right))
     :minus (arithtm-minus (arithtm-double x.arg)))
    ///
    (verify-guards arithtm-double)

    (local (include-book \"arithmetic/top-with-meta\" :dir :system))

    (defthm arithtm-eval-of-double
      (equal (arithtm-eval (arithtm-double x))
             (* 2 (arithtm-eval x)))
      :hints((\"Goal\" :in-theory (enable arithtm-eval)))))
 })

<h3>Deftagsum Usage and Options</h3>

<p>A @('deftagsum') form consists of the type name, a list of product
specifiers, and some optional keyword arguments.</p>

<h4>Product specifiers</h4>

<p>A product specifier consists of a tag (a keyword symbol), a list of fields
given as @(see std::extended-formals), and some optional keyword arguments.
The possible keyword arguments are:</p>

<ul>
<li>@(':layout'), one of @(':tree'), @(':list'), or @(':alist'), determining
the arrangement of fields within the product object (as in @(see defprod)),</li>
<li>@(':inline'), determining whether the constructor and accessors are inlined
or not.  This may be @(':all') or a subset of @('(:xtor :acc)').  Defaults to
@('(:acc)') if not overridden.</li>
<li>@(':hons'), NIL by default, determining whether objects are constructed
with @(see hons).</li>
<li>@(':base-name'), overrides the name of the constructor and the base name
used to generate accessors.</li>
<li>@(':require') adds a dependent type requirement; see the section on this
feature in @(see defprod).</li>
</ul>

<h4>Tagsum Options</h4>

<p>The following keyword options are recognized at the top level of a
@('deftagsum') form (as opposed to inside the individual product forms):</p>
<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':kind'), @(':count'): override
default function names.  @(':count') may also be set to NIL, to turn of
generation of the count function.</li>

<li>@(':parents'), @(':short'), @(':long'): add xdoc about the type.</li>

<li>@(':measure'): override the measures used to admit the recognizer, fixing
function, and count function; the default is @('(acl2-count x)').</li>

<li>@(':prepwork'): events submitted before</li>

<li>@(':inline'): sets default for inlining of products and determines whether
the kind and fixing functions are inlined.  This may be @(':all') or a subset
of @('(:kind :fix :acc :xtor)'), defaulting to @('(:kind :fix :acc)').</li>

<li>@(':layout'): sets default layout for products</li>

<li>@(':base-case-override'): Override which product is the base case.  This
may affect termination of the fixing function; see below.</li>

</ul>

<h3>Dealing with Base Cases</h3>

<p>Consider the following type definition:</p>

@({
  (deftypes fntree
    (deftagsum fntree
      (:pair ((left fntree-p) (right fntree-p)))
      (:call ((fn symbol) (args fntreelist-p))))
    (deflist fntreelist-p :elt-type fntree))
 })

<p>As is, deftypes will fail to admit this event, saying:</p>

<blockquote>
We couldn't find a base case for tagsum FNTREE, so we don't know what its
fixing function should return when the input is an atom.  To override this, add
keyword arg :base-case-override [product], where [product] is one of your
product keywords, and provide a measure that will allow the fixing function to
terminate.
</blockquote>

<p>What is the problem?  As the text suggests, the problem lies in what we
should do when given an atom as input to the fixing function.  With the default
measure of @('(acl2-count x)'), we're not allowed to recur on, say, @('NIL'),
because its acl2-count is already 0.  This is fine as long as we can pick a
product type that has no recursive components, but in this case, the @(':pair')
and @(':call') product both do.  However, the @(':call') product could have an
empty list as its arguments, and this seems like a reasonable thing to use as
the fix of an atom.  To give @('deftagsum') the hint to do this, we need to
tell it which product to fix an atom to, and what measure to use.  The
following modification of the above form works:</p>

@({
  (deftypes fntree
    (deftagsum fntree
      (:pair ((left fntree-p) (right fntree-p)))
      (:call ((fn symbol) (arg fntreelist-p)))
      :base-case-override :call
      :measure (two-nats-measure (acl2-count x) 1))
    (deflist fntreelist-p :elt-type fntree
      :measure (two-nats-measure (acl2-count x) 0)))
 }) ")

(defxdoc defflexsum
  :parents (fty deftypes)
  :short "Define a (possibly recursive) sum of products type."
  :long "
<h3>Caveat</h3>

<p>@('Defflexsum') is not very user-friendly or automatic; it is easy to create
instances that fail in incomprehensible ways.  It is used as a backend to
define the @(see deftagsum) and @(see defprod) type generators, which are easier to
use.</p>

<h4>Example</h4>

<p>This is essentially the same as the example in @(see deftagsum).  Logically,
the way these types work are very similar; only the representation is
different.</p>
@({
  (defflexsum arithterm
    (:num :cond (atom x)
          :fields ((val :type integerp :acc-body x))
          :ctor-body val)
    (:plus
     :cond (eq (car x) '+)
     :shape (and (true-listp x) (eql (len x) 3))
     :fields ((left :type arithterm :acc-body (cadr x))
              (right :type arithterm :acc-body (caddr x)))
     :ctor-body (list '+ left right))
    (:minus
     :shape (and (eq (car x) '-)
                 (true-listp x)
                 (eql (len x) 2))
     :fields ((arg :type arithterm :acc-body (cadr x)))
     :ctor-body (list '- arg)))

  (define arithterm-eval ((x arithterm-p))
    :returns (xval integerp :rule-classes :type-prescription)
    :measure (arithterm-count x)
    (case (arithterm-kind x)
      (:num (arithterm-num->val x))
      (:plus (+ (arithterm-eval (arithterm-plus->left x))
                (arithterm-eval (arithterm-plus->right x))))
      (t (- (arithterm-eval (arithterm-minus->arg x)))))
    ///
    (deffixequiv arithterm-eval))

  (define arithterm-double ((x arithterm-p))
    :verify-guards nil ;; requires return type theorem first
    :returns (xx arithterm-p)
    :measure (arithterm-count x)
    (arithterm-case x
      :num (arithterm-num (* 2 x.val))
      :plus (arithterm-plus (arithterm-double x.left)
                            (arithterm-double x.right))
      :minus (arithterm-minus (arithterm-double x.arg)))
    ///
    (verify-guards arithterm-double)

    (deffixequiv arithterm-double)

    (local (include-book \"arithmetic/top-with-meta\" :dir :system))

    (defthm arithterm-double-correct
      (equal (arithterm-eval (arithterm-double x))
             (* 2 (arithterm-eval x)))
      :hints((\"Goal\" :in-theory (enable arithterm-eval)))))
 })

<p>Note: when the constructors are actually defined, @('mbe') is used to allow
the function to logically apply fixing functions to its arguments without a
performance penalty when running with guards checked.</p>

<h3>More on the above Caveat</h3>

<p>@('defflexsum') is less automatic than most other type-defining utilities.
It requires certain information to be provided by the user that must then be
proved to be self-consistent.  For example, the @(':ctor-body') argument in a
product spec determines how that product is constructed, and the @(':acc-body')
argument to a product field spec determines how that field is accessed.  These
could easily be inconsistent, or the @(':ctor-body') could produce an object
that is not recognized as that product.  If either of these is the case, some
proof within the @('defflexsum') event will fail and it will be up to the user
to figure out what that proof was and why it failed.</p>


<h3>Syntax and Options</h3>

<h4>@('Defflexsum') top-level arguments</h4>

<p>@('Defflexsum') takes the following keyword arguments, in addition to a list
of products, which are described further below.</p>

<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':kind'), @(':case'), and @(':count')
override the default names for the various generated functions (and case
macro).  If any of these is not provided, a default name is used instead.  If
@(':kind nil') is provided, then no @('-kind') function is generated and
instead the products are distinguished by their bare @(':cond') fields.  If
@(':count nil') is provided, then no count function is defined for this
type.</li>

<li>@(':xvar') sets the variable name used to represent the SUM object.  By
default, we look for a symbol whose name is \"X\" that occurs in the product
declarations.</li>

<li>@(':measure') provides the measure for the predicate, fixing function, and
count function.  It defaults to @('(acl2-count x)'), which is usually
appropriate for stand-alone products, but sometimes a special measure must be
used, especially when @('defflexsum') is used inside a mutually-recursive
@('deftypes') form.</li>

<li>@(':prepwork') is a list of events to be submitted at the beginning of the
process; usually these are local lemmas needed for the various proofs.</li>

<li>@(':parents'), @(':short'), and @(':long') provide xdoc for the type</li>

<li>@(':inline'): sets default for inlining of products and determines whether
the kind and fixing functions are inlined.  This may be @(':all') or a subset
of @('(:kind :fix :acc :xtor)'), defaulting to @('(:kind :fix :acc)').</li>

</ul>

<h4>Products</h4>

<p>Each product starts with a keyword naming its kind; this is the symbol that
the SUM kind function returns on an object of that product type.  The rest of
the form is a list of keyword arguments:</p>

<ul>

<li>@(':cond') describes how to tell whether an object is of this product type.
To determine the kind of a SUM object, the SUM kind function checks each of
the product conditions in turn, returning the name of the first matching
condition.  So the condition for a given product assumes the negations of the
conditions of the previous listed products.  The @(':cond') field defaults to
@('t'), so typically it can be left off the last product type.</li>

<li>@(':shape') adds well-formedness requirements for a product.  One purpose
these may serve is to make well-formed objects canonical: it must be a theorem
that the fixing function applied to a well-formed object is the same object.
So if a product is (e.g.) a tuple represented as a list, and the constructor
creates it as a true-list, then there should be a requirement that the object
be a true-list of the appropriate length; otherwise, an object that had a
non-nil final cdr would be recognized as well-formed, but fix to a different
value.</li>

<li>@(':fields') list the fields of the product; these are described further
below.</li>

<li>@(':ctor-body') describes how to make a product object from the fields.
This must be consistent with the field accessor bodies (described below) and
with the @(':cond') and @(':shape') fields of this product and the previous
ones (i.e., it can't produce something that could be mistaken for one of the
previous products listed).  The actual constructor function will have fixing
functions added; these should not be present in the @(':ctor-body')
argument.</li>

<li>@(':type-name') overrides the type-name, which by default is
@('[SUMNAME]-[KIND]'), e.g. @('arithterm-plus') from the example above.  This
is used as a base for generating the field accessor names.</li>

<li>@(':ctor-name') overrides the name of the product constructor function,
which by default is the type-name.</li>

<li>@(':inline'), determining whether the constructor and accessors are inlined
or not.  This may be @(':all') or a subset of @('(:xtor :acc)').  Defaults to
@('(:acc)') if not overridden.</li>

<li>@(':require') adds a dependent type requirement; see the section on this
feature in @(see defprod).</li>

</ul>

<h4>Product Fields</h4>

<p>Each product field is a name followed by a keyword list, in which the
following keywords are allowed:</p>
<ul>
<li>@(':acc-body') must be present: a term showing how to fetch the field from
the object.</li>
<li>@(':acc-name') overrides the accessor name</li>
<li>@(':type'), the type (fixtype name or predicate) of the field; may be empty
for an untyped field</li>
<li>@(':default'), the default value of the field in the constructor macro</li>
<li>@(':doc') will eventually generate xdoc, but is currently ignored</li>
<li>@(':rule-classes'), the rule classes for the return type of the accessor
function.  This is @(':rewrite') by default; you may wish to change it to
@(':type-prescription') when the type is something basic like
@('integerp').</li>
</ul>
")

(defxdoc deftranssum
  :parents (deftypes)
  :short "Introduce a transparent sum of products. (beta)"
  :long "<p>BOZO document me.</p>")

(defxdoc defoption
  :parents (fty deftypes)
  :short "Define an option type."
  :long "<p>BOZO document me.  There used to be documentation for this when
it was part of VL.  See @(see vl::defoption).  I don't know how much of it
is the same...</p>")

(defxdoc defvisitor-template
  :parents (defvisitors)
  :short "Create a template that says how to make visitor functions."
  :long "<p>This is used in combination with @(see defvisitors) and @(see
defvisitor) to automatically generate \"visitor\" functions, i.e. functions
that traverse a data structure and do something at specified locations in it.
E.g., they can be used to transform all fields of a certain type, or to collect
some information about all occurrences of a certain product field, etc.  The
types that these visitors may traverse are those defined by @(see deftypes) and
related macros @(see defprod), @(see deftagsum), @(see deflist), @(see
defalist), @(see defoption), @(see deftranssum), and @(see defflexsum).</p>

<p>Visitor templates can be used by @(see defvisitor), @(see defvisitors), and
@(see defvisitor-multi) to automatically generate immense amounts of
boilerplate code for traversing complicated datatypes, especially when the
operation you want to do only really has to do with a few fields or component
types.</p>

<p>Here is a simple example from visitor-tests.lisp, annotated:</p>

@({
 (defvisitor-template

   ;; Name of the template.  This gets referred to later when this template is
   ;; used by defvisitor/defvisitors.
   collect-strings

   ;; Formals, similar to the formals in std::define.  Here :object stands for
   ;; the type predicate of whatever kind of object we're currently visiting; we'll
   ;; typically instantiate this template with several different :object types.
   ((x :object))

   ;; Return specifiers.  These are also like in std::define, but after each return name
   ;; is a description of how the return value gets constructed.  The names here are
   ;; a \"join\" value, which means they get constructed by combining,
   ;; pairwise, the corresponding values returned by sub-calls.  In this case, the
   ;; value (names1) returned from the most recent subcall is appended onto the
   ;; previous value (names).  The initial value is nil, i.e. this is what a
   ;; visitor function returns when run on an empty list or an object with no fields.
   :returns (names (:join (append names1 names)
                    :tmp-var names1
                    :initial nil)
                   string-listp)

   ;; Now we describe what is a base case and what we return in base cases.
   ;; This says, for any string field x, just produce (list x).  (The value
   ;; bound in the alist is a lambda or function that gets applied to the
   ;; formals, in this case just x.)
   :type-fns ((string list))

   ;; Describes how the functions we produce should be named.  Here, <type> gets
   ;; replaced by the type of object each separate visitor function operates on.
   :fnname-template collect-strings-in-<type>)
})

<p>Besides join values, there are two other kinds of visitor return values:
accumulators and updaters.  The following example shows how to use an
accumulator:</p>

@({
 (defvisitor-template collect-names-acc   ;; template name
     ;; formals:
     ((x :object)
      (names string-listp)) ;; accumulator formal

     ;; Names the return value and declares it to be an accumulator, which
     ;; corresponds to the formal NAMES.  The :fix is optional but is needed if
     ;; the return type of your accumulator output is unconditional.
     :returns  (names-out (:acc names :fix (string-list-fix names))
                          string-listp)

     ;; Base case specification.  This says that when visiting a
     ;; simple-tree-leaf product, use the function CONS as the visitor for the
     ;; NAME field.  That is, instead of recurring on name, use (cons x names),
     ;; i.e., add the name to the accumulator.
     :prod-fns ((simple-tree-leaf  (name cons))))
 })

<p>This shows how to use an updater return value:</p>

@({
  (defvisitor-template incr-val  ((x :object)
                                  (incr-amount natp))

    ;; In an :update return value, the type is implicitly the same as :object.
    ;; It can optionally be specified differently.  This means that new-x gets
    ;; created by updating all the fields that we recurred on (or that were base
    ;; cases) with the corresponding results.
    :returns (new-x :update)

    ;; This says that when we visit a simple-tree-leaf, we replace its value field with
    ;; the field's previous value plus (lnfix incr-amount).  (We could just use
    ;; + here instead of the lambda, but this would violate the fixing convention for
    ;; incr-amount.)
    :prod-fns ((simple-tree-leaf  (value (lambda (x incr-amount) (+ x (lnfix incr-amount)))))))
 })

<p>The general form of a @('defvisitor-template') call is:</p>
@({
 (defvisitor-template template-name formals ... keyword-args)
 })

<p>where the accepted keywords are as follows:</p>

<ul>

<li>@(':returns'), required, describing the values returned by each visitor
function and how they are constructed from recursive calls.  The argument to
@(':returns') is either a single return tuple or several return tuples inside
an @('(mv ...)'), and each return tuple is similar to a @(see std::define)
returnspec except that it has an extra form after the return name and before
the rest of the arguments, describing how it is constructed -- either a
@(':join'), @(':acc'), or @(':update') form, as in the examples above.</li>

<li>@(':type-fns') specify base cases for fields of certain types.  The
argument is a list of pairs @('(type function)'), where the function applied to
the visitor formals gives the visitor values for fields of that type.
Alternatively, function may be @(':skip'), meaning that we don't recur on
fields of this type. (This is the default for field types that were not defined
by @(see deftypes).)  The @(':type-fns') entry is only used if there is no
applicable entry in @(':field-fns') or @(':prod-fns'), below.</li>

<li>@(':prod-fns') specify base cases for certain fields of certain products.
The argument is a list of entries @('(prod-name (field-name1
function1) (field-name2 function2) ...)'), where the functions work the same
way as in @(':type-fns').  @(':prod-fns') entries override @(':type-fns') and
@(':field-fns') entries.</li>

<li>@(':field-fns') specify base cases for fields with certain names.  The
argument is a list of pairs @('(field-name function)'), where function is as in
the @(':type-fns').  This is similar to using @(':prod-fns'), but applies to
fields of the given name inside any product.  @(':field-fns') entries override
@(':type-fns') entries, but @(':prod-fns') entries override both.</li>

<li>@(':fnname-template') describes how the generated functions should be
named. The argument is a symbol containing the substring @('<TYPE>'), and
function names are generated by replacing this with the name of the type.</li>

<li>@(':renames') allows you to specify function names that differ from the
ones described by the @(':fnname-template').  The argument is a list of pairs
@('(type function-name)').  It is also possible to use @(':skip') as the
function name, in which case the function won't be generated at all.</li>

<li>@(':fixequivs') -- true by default, says whether to prove
congruence (deffixequiv) theorems about the generated functions.</li>

<li>@(':reversep') -- false by default, says whether to reverse the order in
which fields are processed.</li>

<li>@(':wrapper') -- @(':body') by default; gives a form in which to wrap the
generated body of each function, where @(':body') is replaced by that generated
body.  Advanced use.</li>

</ul>

<p>See also @('defvisitor'), @('defvisitors'), and @('defvisitor-multi').</p>")

(defxdoc defvisitor
  :parents (defvisitors)
  :short "Generate visitor functions for one type or one mutually-recursive clique of types."
  :long "<p>Defvisitor first requires that you have a visitor template defined
using @(see defvisitor-template).  The defvisitor form then instantiates that
template to create a visitor function for a type, or for each type in a
mutually-recursive clique of types.  See also @(see defvisitors), which
generates several defvisitor forms in order to traverse several types, and
@(see defvisitor-multi), which combines defvisitor and defvisitors forms into a
mutual recursion.</p>

<p>For example, the following visitor template was described in @(see
defvisitor-template):</p>

@({
 (defvisitor-template collect-strings ((x :object))
   :returns (names (:join (append names1 names)
                    :tmp-var names1
                    :initial nil)
                   string-listp)
   :type-fns ((string list))
   :fnname-template collect-strings-in-<type>)
})

<p>If we have a type defined as follows:</p>
@({
 (deftagsum simple-tree
   ;; Some simple kind of structure
   (:leaf ((name  stringp)
           (value natp)
           (cost  integerp)))
   (:branch ((left   simple-tree)
             (right  simple-tree)
             (hint   booleanp)
             (family stringp)
             (size   natp))))
 })
<p>then to create a visitor for the simple-tree type, we can do:</p>

@({
 (defvisitor collect-strings-in-simple-tree-definition
             ;; optional event name, for tags etc

   ;; type or mutually-recursive clique of types to visit
   :type simple-tree

   ;; template to instantiate
   :template collect-strings)
 })

<p>This creates (essentially) the following function definition:</p>

@({
  (define collect-strings-in-simple-tree ((x simple-tree-p))
    :returns (names string-listp)
    :measure (simple-tree-count x)
    (simple-tree-case x
      :leaf   (b* ((names (list x.name)))
                 names)
      :branch (b* ((names (collect-strings-in-simple-tree x.left))
                   (names1 (collect-strings-in-simple-tree x.right))
                   (names (append names1 names))
                   (names1 (list x.family))
                   (names (append names1 names)))
                 names)))
 })

<p>Additionally, defvisitor modifies the collect-strings template so that
future instantiations of the template will, by default, use
@('collect-strings-in-simple-tree') when visiting a simple-tree object.  (The
pair @('(simple-tree collect-strings-in-simple-tree)') is added to the
@(':type-fns') of the template; see @(see defvisitor-template).)</p>


<p>If we instead have a mutually-recursive clique of types, like the following:</p>

@({
 (deftypes mrec-tree
   (deftagsum mrec-tree-node
      (:leaf ((name stringp)
              (value natp)
              (cost integerp)))
      (:branch ((children mrec-treelist)
                (family stringp)
                (size natp))))
   (deflist mrec-treelist :elt-type mrec-tree-node))
 })

<p>then we can create a mutual recursion of visitors for these types as follows:</p>

@({
 (defvisitor collect-mrec-tree-strings
    :type mrec-tree   ;; the deftypes form name, not one of the type names
    :template collect-strings)
 })

<p>This creates a definition like this:</p>

@({
  (defines collect-strings-in-mrec-tree
    (define collect-strings-in-mrec-tree-node ((x mrec-tree-node-p))
       :returns (names string-listp)
       :measure (mrec-tree-node-count x)
       (mrec-tree-node-case x
         :leaf ...    ;; similar to the simple-tree above
         :branch ...))
    (define collect-strings-in-mrec-treelist ((x mrec-treelist-p))
       :returns (names string-listp)
       :measure (mrec-treelist-count x)
       (if (atom x)
           nil
         (b* ((names (collect-strings-in-mrec-tree-node (car x)))
              (names1 (collect-strings-in-mrec-treelist (cdr x)))
              (names (append names1 names)))
           names))))
 })

<p>The general form of defvisitor is:</p>

@({
 (defvisitor [ event-name ]
    :type type-name
    :template template-name
    other-keyword-args
    mrec-defines
    ///
    post-events)
 })

<p>One or more additional define forms may be nested inside a defvisitor form;
this means they will be added to the mutual-recursion with the generated
visitor functions.  This can be used to specialize the visitor's behavior on
some field so that when visiting that field the function is called, which then
calls other visitor functions from the clique.</p>

<p>The available keyword arguments (other than @(':type') and @(':template'))
are as follows:</p>

<ul>

<li>@(':type-fns'), @(':field-fns'), @(':prod-fns') -- these add additional
entries to the corresponding arguments of the template; see @(see
defvisitor-template).  When the defvisitor event finishes, these entries are
left in the updated template.</li>

<li>@(':fnname-template'), @(':renames') -- these override the corresponding
arguments of the template, but only for the current defvisitor; i.e., they are
not stored in the updated template.</li>

<li>@(':omit-types'), @(':include-types') -- when defining visitors for a
mutually-recursive clique of types, @(':omit-types') may be used to skip
creation of a visitor for some of the types, or @(':include-types') may be used
to only create visitors for the listed types.</li>

<li>@(':measure') -- Template for generating the measure for the functions;
defaults to @(':count').  In the template, @(':count') is replaced by the count
function for each type visited, and @(':order') is replaced by the current
order value (see below).  E.g., @('(two-nats-measure :count 0)') is often a
useful measure template, and @('(two-nats-measure :order :count)') is sometimes
useful inside @(see defvisitor-multi).</li>

<li>@(':defines-args'), @('define-args') -- Extra keyword arguments provided to
@('defines') or @(':define') respectively; @('defines-args') is only applicable
when there is a mutual recursion.</li>

<li>@(':order') specifies the order value for this clique, which is useful when
combining multiple defvisitor cliques into a single mutual recursion with @(see
defvisitor-multi).</li>
</ul>")


(defxdoc defvisitors
  :parents (fty)
  :short "Generate visitor functions across types using a visitor template."
  :long "<p>To use defvisitors, first see @(see defvisitor-template) and @(see
defvisitor).  Defvisitors automates the generation of several defvisitor forms
that create a system of visitor functions that works on a nest of types.</p>

<p>For example, suppose we have the following types:</p>

@({
  (defprod employee
     ((name stringp)
      (salary natp)
      (title stringp)))

  (deflist employees :elt-type employee)

  (defprod group
    ((lead employee)
     (members employees)
     (budget natp)
     (name stringp)
     (responsibilities string-listp)))

  (defprod division
    ((head employee)
     (operations  group)
     (engineering group)
     (sales       group)
     (service     group)
     (black-ops   group)))
 })

<p>Suppose we want to total up the salaries of all the employees in a division,
including the division head, group leads, and group members.  A visitor
template for this operation might look like this:</p>

@({
  (defvisitor-template salary-total ((x :object))
    :returns (total (:join (+ total1 total)
                     :tmp-var total1
                     :initial 0)
                    natp :rule-classes :type-prescription
                    \"The total salary of all employees\")
    :type-fns ((employee employee->salary)))
 })

<p>Now we need visitor functions for the employees, group, and division types, so we can do:</p>

@({
  (defvisitor :type employees :template salary-total)
  (defvisitor :type group     :template salary-total)
  (defvisitor :type division  :template salary-total)
 })

<p>However, we can automate this more by using defvisitors instead of
defvisitor.  This doesn't seem worthwhile to get rid of just three defvisitor
forms, but oftentimes the type hierarchy is much more specialized than this,
and changes frequently.  Using defvisitors can prevent the need to modify the
code if you add a type to the hierarchy.  To invoke it:</p>

@({
 (defvisitors division-salary-total ;; optional event name
   :types (division)
   :template salary-total)
 })

<p>This searches over the field types of the @('division') type and creates a
graph of the types that need to be visited, then arranges them in dependency
order and creates the necessary defvisitor forms.</p>

<p>The options for @('defvisitors') are somewhat more limited than for
@('defvisitor').  The available keyword arguments are as follows:</p>

<ul>

<li>@(':template') -- the name of the visitor template to instantiate.</li>

<li>@(':types'), @(':dep-types') -- controls the top-level types to visit.
Those listed in @('dep-types') are not themselves visited, but their children
are.  Note that these are type names, NOT deftypes names as in @(see
defvisitor).  (For a single type, the type name and deftypes name is likely the
same, but for a mutually-recursive clique of types, the deftypes name refers to
the whole clique.)</li>

<li>@(':measure') -- measure form to use for each @('defvisitor') form; this is
mostly only useful in the context of a @('defvisitor-multi') form.</li>

<li>@(':order-base') -- starting index from which the order indices assigned to
the deftypes forms are generated; also mostly only useful in the context of a
@('defvisitor-multi') form.  Defvisitors assigns a different order index to
each defvisitor form it submits, with earlier forms having lower indices.  When
the measure is properly formulated in terms of the order, this allows them to
be used together in a mutual recursion.</li>

<li>@(':debug') -- print some information about the graph traversals.</li>

</ul>")

(defxdoc defvisitor-multi
  :parents (defvisitors)
  :short "Put defvisitor, defvisitors, and define forms togeher into a single mutual recursion."
  :long "<p>In a few cases it is useful to have visitors for several types (or
perhaps several different kinds of visitors) together in a mutual recursion.
Here is an example showing how this can work.</p>

@({
  ;; We have sum of product terms.  Each literal in the sum of products is
  ;; either a constant or a variable, which refers to another sum of products
  ;; term via a lookup table.
  (deftagsum literal
    (:constant ((value natp)))
    (:variable ((name symbolp))))

  (defprod product
    ((first  literal-p)
     (second literal-p)
     (third  literal-p)))

  (defprod sum
    ((left  product-p)
     (right product-p)))

  ;; Lookup table mapping each variable to a sum-of-products.
  (defalist sop-env :key-type symbolp :val-type sum-p)

  ;; Suppose we have a lookup table and we want to collect all the dependencies
  ;; of some expression -- i.e., when we get to a variable we want to collect
  ;; it, then look up its formula and collect its dependencies too.  If the
  ;; table doesn't have some strict dependency order, then we might not
  ;; terminate, so we'll use a recursion limit.

  (defvisitor-template collect-deps ((x :object)
                                     (env sop-env-p)
                                     (rec-limit natp))
    :returns (deps (:join (append deps1 deps)
                    :tmp-var deps1 :initial nil)
                    symbol-listp)

    ;; We'll call the function to apply to variable names
    ;; collect-and-recur-on-var.  Note that this hasn't been defined yet -- it
    ;; needs to be mutually recursive with the other functions in the clique.
    :prod-fns ((variable (name collect-and-recur-on-var)))

    :fnname-template <type>-collect-deps)

  ;; A defvisitor-multi form binds together some defvisitor and defvisitors
  ;; forms into a mutual recursion with some other functions.  Here, we'll just have
  ;; the one defvisitors form inside.
  (defvisitor-multi sum-collect-deps

     (defvisitors :template collect-deps :types (sum)
       ;; Normally this defvisitors form would create a visitor for a literal,
       ;; then product, then sum.  Inside a defvisitor-multi, it instead puts
       ;; all of those definitions into one mutual recursion.

       ;; We have to do something special with the measure.  Defvisitors
       ;; assigns an order to each of the types so that calling from one
       ;; visitor to another can generally reduce the measure.  Therefore, we
       ;; only need to decrease the rec-limit when calling from a lower-level
       ;; type to a higher-level one -- e.g. when we reach a variable and will
       ;; recur on a sum.
       :measure (two-nats-measure rec-limit :order)

       ;; Since our lowest-level visitor (literal-collect-deps) is going to
       ;; call an intermediate function (collect-and-recur-on-var) which then
       ;; calls our highest-level visitor (sum-collect-deps), it's convenient
       ;; to set the order of the lowest-level to 1 so that
       ;; collect-and-recur-on-var can use 0 as the order in its measure.
       :order-base 1)

     ;; This function goes in the mutual recursion with the others.
     (define collect-and-recur-on-var ((x symbolp)
                                       (env sop-env-p)
                                       (rec-limit natp))
        :returns (deps symbol-listp)
        :measure (two-nats-measure rec-limit 0)
        (b* ((x (mbe :logic (symbol-fix x) :exec x))
             (lookup (hons-get x (sop-env-fix env)))
             ((unless lookup) (list x))
             ((when (zp rec-limit))
              (cw \"Recursion limit ran out on ~x0~%\" x)
              (list x)))
          (cons x (sum-collect-deps (cdr lookup) env (- rec-limit 1))))))

})

<p>A @('defvisitor-multi') form's syntax is as follows:</p>
@({
  (defvisitor-multi event-name
     defvisitor-defvisitors-define-forms
     keyword-args
     ///
     post-events)
 })

<p>The only keyword arguments currently accepted are @(':defines-args') and
@(':fixequivs'), which are described in @(see defvisitor).  All the usual
arguments to defvisitor and defvisitors are accepted, except for these two.  An
additional difference from non-nested forms is that the nested defvisitor and
defvisitors forms may not have an event name as the first argument.</p>")


#||

;; Doc editing support

(include-book
 "xdoc/save" :dir :system)
(defxdoc acl2::macro-libraries :parents (acl2::top) :short "Placeholder")
(defttag blah)
(deflabel blah)

;; You can now loop { edit docs, save top.lisp, submit this form, view in browser }
(progn!
  (ubt! 'blah)
  (deflabel blah)
  (include-book
   "top")
  (xdoc::save "./fty-manual"
              :import nil
              :redef-okp t
              :zip-p nil))
||#
