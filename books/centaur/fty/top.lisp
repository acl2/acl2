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

#||
(include-book "deftypes-tests")
(include-book "doc-tests")
||#

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
using types in ACL2 definitions.  This discipline easy on the prover and
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
they are likely to follow naturally;</li>

<li>Otherwise, you can simply fix each of the inputs to a function to their
appropriate types for free, using @(see MBE).</li>

</ul>

<p>For instance, here is a function that obeys the FTY discipline for natural
numbers by simply fixing its argument before operating on it:</p>

@({
    (defun nat-add-5 (n)
      (declare (xargs :guard (natp n)))
      (let ((n (mbe :logic (nfix n) :exec n)))
        (+ n 5)))
})

<p>FTY provides macro support for automatically proving the congruence rules;
see @(see deffixequiv) and @(see deffixequiv-mutual).  Meanwhile, for a
convenient way to prove unconditional return-value theorems, see the @(see
std::returns-specifiers) feature of @(see std::define).</p>

<p>Having unconditional return types and congruences are both beneficial for in
themselves.  But the main benefit of using the fixtype discipline is that
reasoning about such functions does not require hypotheses constraining their
inputs to the expected types, because they are fixed to that type (in a
consistent manner) before being used.</p>")


(defxdoc deffixtype
  :parents (fty)
  :short "Define a new type for use with the @(see fty-discipline)."

  :long "<p>In it most basic form, @('deffixtype') just associates an new type
name with the corresponding predicate, fixing function, and equivalence
relation.  It stores this association in a @(see table).  The type then becomes
``known'' to other @(see fty) macros such as @(see deffixequiv), @(see
defprod), and so on.</p>


<h4>Basic Example</h4>

<p>You could use the following to define the <color rgb='#900090'>nat</color>
type with the recognizer @(see natp), the fixing function @(see nfix), and
equivalence relation @(see nat-equiv).</p>

@({
  (fty::deffixtype nat
    :pred  natp
    :fix   nfix
    :equiv nat-equiv)
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
them.</p>")


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
  :short "Define a list type with a fixing function, supported by @(see deftypes)"

  :long "<p>@('Deflist') provides a recognizer predicate, fixing function, and
a few theorems defining a list of elements of a certain type.</p>

<p>@('Deflist') is compatible with @(see deftypes), and can be
mutually-recursive with other @('deftypes') compatible type generators.  As
with all @(see deftypes)-compatible type generators, its element type must
either be one produced by a compatible type generator or else have an
associated fixing function given by @(see deffixtype).  See @(see basetypes) for
some base types with fixing functions.</p>

<p>The syntax of deflist is:</p>
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
  )
 })

<p>Only the name and the @(':elt-type') argument is required.</p>

<p>As part of the event, deflist calls @(see std::deflist) to produce several
useful theorems about the introduced predicate.</p>

<p>Deflist (by itself, not when part of mutually-recursive deftypes form) also
allows previously defined list predicates.  For example, the following form
produces a fixing function for ACL2's built-in @(see string-listp)
predicate:</p>

@({ (deflist string-list :pred string-listp :elt-type stringp) })")

(defxdoc defalist
  :parents (fty deftypes)
  :short "Define an alist type with a fixing function, supported by @(see deftypes)"
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
 })")


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


<h4>Basic Example</h4>

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


<h4>Options</h4>
<p>Keyword options for @('defprod') include:</p>
<ul>

<li>@(':pred'), @(':fix'), @(':equiv'), @(':count'): override default function
names, which are (respectively) @('name-p'), @('name-fix'), @('name-equiv'),
and @('name-count').  As a special case, @(':count') may be nil, meaning no
count function is produced.  (A count function is only produced when this is
mutually-recursive with other type generators.)</li>

<li>@(':parents'), @(':short'), @(':long'): add xdoc about the type.  (Note:
xdoc support is half-baked; e.g. documentation strings for fields are allowed
but not yet used.</li>

<li>@(':layout'): must be one of @(':tree'), @(':list'), or @(':alist'),
defaulting to @(':alist').  This determines how the fields are laid out in the
object; e.g., a 5-element product will be laid out as follows for each case:
@({
  `((,a . ,b) . (,c . (,d . e)))                   ;; :tree
  `(,a ,b ,c ,d ,e)                                ;; :list
  `((a . ,a) (b . ,b) (c . ,c) (d . ,d) (e . ,e))  ;; :alist
 })
</li>

<li>@(':tag'): defaults to NIL, meaning it isn't present; otherwise it must be
a keyword symbol, which is consed onto every occurrence of the object.</li>

<li>@(':measure'): Only necessary in the mutually-recursive case, but probably
necessary then.  The default measure is @('(acl2-count x)'), but this is
unlikely to work in the mutually-recursive case because of the possibility that
@('x') could be (say) an atom, in which case the @('acl2-count') of @('x') will
be no greater than the @('acl2-count') of a field.  Often something like
@('(two-nats-measure (acl2-count x) 5)') is a good measure for the product,
where the other mutually-recursive types have a similar measure with smaller
second component.</li>

<li>@(':hons'), NIL by default; when T, the constructor is defined using @(see
hons) rather than cons.</li>

<li>@(':inline') is @('(:acc :fix)') by default, which causes the accessors and
fixing function (which for execution purposes is just the identity) to be
inlined.  The list may also contain @(':xtor'), which causes the constructor to
be inlined as well; @(':all') (not in a list) is also possible.</li>

<li>@(':require') adds a dependent type requirement; see the section on this feature below.</li>
</ul>

<h4>Experimental Dependent Type Option</h4>

<p>An additional top-level keyword, @(':require'), can add a requirement that
the fields satisfy some relation.  Using this option requires that one or more
fields be given a @(':reqfix') option; it must be a theorem that applying the
regular fixing functions followed by the @(':reqfix') of each field
independently yields fields that satisfy the requirement.  (It should also be
the case that applying the reqfixes to fields already satisfying the
requirement leaves them unchanged.) For example:</p>

@({
 (defprod sizednum
   ((size natp)
    (bits natp :reqfix (loghead size bits)))
   :require (unsigned-byte-p size bits))
 })

<p>If there is more than one field with a @(':reqfix') option, these reqfixes
are applied to each field independently, after applying all of their types' fixing functions.
For example, for the following to succeed:</p>

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
would NOT be sufficient for this to be true with a LET*.</p>
")

(defxdoc deftagsum
  :parents (fty deftypes)
  :short "Define a (possibly recursive) tagged union/sum of products type."

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

<p>@('Mbe') allows the function to logically apply fixing functions to its
arguments without a performance penalty when running with guards checked.</p>

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

