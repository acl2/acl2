; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
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

(in-package "BITOPS")
;; (include-book "defaults")
(include-book "ash-bounds")
(include-book "logbitp-bounds")
;; (include-book "congruences")
(include-book "equal-by-logbitp")
(include-book "extra-defs")
(include-book "fast-logrev")
(include-book "fast-logext")
(include-book "ihs-extensions")
(include-book "ihsext-basics")
(include-book "install-bit")
(include-book "integer-length")
(include-book "merge")
(include-book "parity")
(include-book "part-select")
(include-book "part-install")
(include-book "rotate")
(include-book "fast-rotate")
(include-book "saturate")
(include-book "signed-byte-p")

(defxdoc bitops
  :parents (acl2::bit-vectors)
  :short "Bitops is a library originally developed at Centaur Technology
for reasoning about bit-vector arithmetic.  It grew out of an extension
to the venerable @(see acl2::ihs) library, and is now fairly comprehensive."

  :long "<h3>Introduction</h3>

<p>Bitops is a bit-vector arithmetic library.  It provides:</p>

<ul>

<li>Definitions for single-bit operations like @(see b-and), @(see b-ior),
etc., and for extended bit-vector operations, like @(see loghead), @(see
logapp), @(see logrev), etc.  These are largely inherited from @(see
acl2::ihs).</li>

<li>Support for reasoning about these new operations, and also about the
bit-vector operations that are built into ACL2 like @(see logand), @(see ash),
and @(see logbitp).</li>

<li>Efficient implementations of certain bit-vector operations like @(see
fast-logext), <see topic='@(url bitops/merge)'>merge operations</see>, <see
topic='@(url bitops/fast-logrev)'>fast-logrev</see>, etc., with lemmas or @(see
mbe) to relate them to the logically nicer definitions.  These definitions
generally don't add any logical power, but are useful for developing more
efficient executable models.</li>

</ul>


<h5>Compatibility</h5>

<p>Bitops is <b>not</b> a standalone arithmetic library.  It has almost no
support for non-integer arithmetic (rationals/complexes) and has few lemmas
about elementary operations like @('+') and @('*') beyond how they relate to
the bit-vector operations.</p>

<p>Instead, you will usually include books from both Bitops <b>and</b> from
some other arithmetic library.  Bitops is often used in concert with books from
@('arithmetic'), @('arithmetic-3'), and @('arithmetic-5').  See @(see
bitops-compatibility) for notes about using these libraries with Bitops.</p>

<p>Bitops definitions are typically compatible with @(see gl::gl), a framework
for bit-blasting ACL2 theorems.  GL is mainly applicable to bounded problems,
but is highly automatic.  This nicely complements Bitops, which is a more
traditional library of lemmas that can be applied to unbounded problems.</p>


<h5>Philosophy and Expectations</h5>

<p>Bitops is not especially automatic.  Merely loading it may allow you to
solve some bit-vector problems automatically.  But if you want to use it
<i>well</i> and understand what to do when it doesn't solve your problems, you
should expect to invest some effort in learning the library.</p>

<p>One reason Bitops may be less automatic than other libraries is that we use
it in proofs about microcode routines.  These proofs often involve very large
terms.  This poses a challenge when writing arithmetic rules: to successfully
manage proofs with large terms, case-splitting needs to be carefully
controlled.  To keep the library more controllable, some good rules are kept
disabled by default.  So, to get the most out of the library, you may need to
explicitly enable these rules as appropriate.</p>


<h3>Loading the Library</h3>

<p>Bitops is a somewhat large library that is compartmentalized into several
books, many of which can be loaded independently.</p>

<p>To avoid getting locked into any particular arithmetic library, good
practice is to always only @(see local)ly include arithmetic books, including
Bitops.  When your own books only mention built-in functions like @(see logand)
and @(see ash), this is no problem.  But you may often write theorems or
functions that use new functions like @(see loghead), @(see logcdr), etc., and
in this case you need to non-locally include the definitions of these
functions.</p>

<p>Because of this, you will usually want to use something like this:</p>

@({
    (include-book \"ihs/basic-definitions\" :dir :system)
    (local (include-book \"centaur/bitops/ihsext-basics\" :dir :system))
    (local (include-book \"centaur/bitops/signed-byte-p\" :dir :system))
    (local (include-book ... other bitops books ...))
})

<p>Although there is a @('top') book, we generally recommend <b>against</b>
using it.  Instead, it's generally best to load the individual @(see
bitops-books) that address your particular needs.</p>")



(defxdoc bitops-books
  :parents (bitops)
  :short "Guide to the books in the Bitops library."

  :long "<p>Here is a summary of some of the books in the library.</p>

<h3>Major Lemma Books</h3>

<h5>@(see bitops/ihsext-basics)</h5>

<p>This is a key book in the library and is generally a good starting point.
It is intended to be a (still lightweight) replacement for books such as
@('ihs/logops-lemmas.lisp').</p>

<p>For instance, it has rules such as @('logand**'), which is a recursive
definition of @(see logand) that is well-suited for doing inductive proofs,
etc.  This rule is much like IHS's @('logand*') but is improved since there
are no hypotheses.</p>

<p>A lot of the rules in @('ihsext-basics') are improved versions of @('ihs')
rules, but some others are not included at all in @('ihs').</p>


<h5>@(see bitops/ihs-extensions)</h5>

<p>This book is sort of a continuation of @('ihsext-basics').  Oftentimes you
will not need it.  It adds some bounding theorems that relate various bit-vector
operations to @('(expt 2 n)') and may be useful when combining the Bitops
library with books like @('arithmetic-3') and @('arithmetic-5').  The rules here
tend to be more expensive than those in @('ihsext-basics'), so this may not be
well-suited for machine-code models.</p>


<h5>@(see bitops/integer-length)</h5>

<p>This is included in @('ihs-extensions.lisp').  It has some basic lemmas
about @(see integer-length) and its relationship to @('(expt 2 n)').  It may be
useful when combining Bitops with libraries such as @('arithmetic-3') and
@('arithmetic-5').</p>


<h5>@(see bitops/signed-byte-p)</h5>

<p>This is a nice, light-weight book that adds a number of \"obvious\" lemmas
about @('signed-byte-p') and @('unsigned-byte-p'), e.g., that when you add two
@('n')-bit signed numbers, you get an @('n+1')-bit signed number.</p>

<p>These rules can be very helpful when you are trying to write optimized
functions using Common Lisp @(see acl2::type-spec)s and need to satisfy the
guard obligations that come from terms such as @('(the (unsigned-byte 16)
x)').</p>

<p>You can use this book independently of the rest of the library.  It
currently has some support for reasoning about +, -, *, lognot, ash, logcdr,
loghead, and logtail, and will likely be extended as we find it lacking.  You
may often wish to at least also load @('ihsext-basics'), since that has bounds
for many bit-vector operations.</p>


<h5>@(see bitops/equal-by-logbitp)</h5>

<p>This is a very cool book that allows you to carry out pick-a-point proofs:
to show that integers @('x') and @('y') are the same, you can show that their
@('n')th bit is always the same.  This can be a very effective strategy for
working with sequences of bit-manipulation operations, e.g., updates to a flags
register on a processor model.  Some computed hints like
@('equal-by-logbitp-hammer') are also provided, which can automate this
strategy.</p>



<h3>Other Lemma Books</h3>

<h5>congruences.lisp</h5>

<p>This is an advanced book that implements an <i>n</i>-ary like mechanism for
rewriting terms in an @('n')-bit context.</p>


<h5>@(see bitops/ash-bounds)</h5>

<p>This book adds some basic bounding and monotonicity lemmas for @(see ash)
and @(see logtail).</p>

<h5>@(see bitops/logbitp-bounds)</h5>

<p>This book adds some basic lemmas about @(see logbitp) and @(see
expt).</p>

<h5>@(see bitops/defaults)</h5>

<p>This book just has basic theorems about the \"default\" behavior of
bit-vector operations when their inputs are ill-formed (e.g., not integers, not
naturals).  You probably shouldn't load it; most of this should be subsumed by
more recent congruence reasoning for @(see nat-equiv) and @(see int-equiv).</p>


<h3>Books with Extra Definitions</h3>

<h5>@(see bitops/extra-defs)</h5>

<p>This book is a random assortment of functions for slicing integers,
manipulating individual bits, and bit scanning.  It will likely be split up and
organized into separate books in the future.</p>

<h5>@(see bitops/merge)</h5>

<p>This book provides several optimized functions for merging together, e.g.,
four bytes into a 32-bit value, or four 16-bit unsigned values into a 64-bit
result, etc.</p>

<h5>@(see bitops/fast-logrev)</h5>

<p>This book provides optimized implementations of @(see logrev) at various
widths; these definitions are logically just the ordinary, nice, logical
definition of @('logrev'), thanks to @(see mbe).</p>

<h5>@(see bitops/parity)</h5>

<p>This book provides a simple recursive definition of a parity (i.e.,
reduction xor) function, and also a faster version for execution.</p>

<h5>@(see bitops/part-select)</h5>

<p>This book provides a readable nice macro for extracting a portion of an
integer, e.g., bits 15-8.</p>

<h5>@(see bitops/part-install)</h5>

<p>This book provides a function and a macro to set a portion of an
integer to some value. It also includes some theorems about the
interaction of @('part-install') with @(see bitops/part-select).</p>

<h5>@(see bitops/rotate)</h5>

<p>This book defines @(see rotate-left) and @(see rotate-right) operations.  It
provides lemmas explaining how @(see logbitp) interacts with these operations,
and it makes use of the @('equal-by-logbitp') strategy to provide equivalent,
recursive definitions.</p>

<h5>@(see bitops/fast-rotate)</h5>

<p>This book defines @(see fast-rotate) operations that are proved equivalent
to @(see rotate-left) and @(see rotate-right).</p>

<h5>@(see bitops/saturate)</h5>

<p>This book defines some optimized signed and unsigned saturation functions.</p>

<h5>@(see bitops/fast-logext)</h5>

<p>This book provides an optimized sign-extension functions, and proves them
equivalent to @(see logext).  These optimizations don't impact reasoning
because we carry them out with @(see mbe).</p>")


(defsection bitops-compatibility
  :parents (bitops)
  :short "Notes about using Bitops with other arithmetic libraries."

  :long "<p>Bitops can work well with many other arithmetic libraries.  Here we
briefly sketch some tips about using various libraries with Bitops.</p>


<h3>ihs/</h3>

<p>Bitops started as an extension to the ihs library.  Because of this
heritage, the relationship between @('ihs/') and @('bitops/') is somewhat
complex.  Some parts of @('ihs') can still be used with Bitops, others are best
avoided.</p>

<h5>IHS Definition Books</h5>

<p>The @('ihs/basic-definitions') book is included directly in Bitops.  You may
often want to non-locally include this book (to get definitions such as
@('loghead') and @('logtail')), then locally include Bitops books such as
@('ihsext-basics') (to get the lemmas).</p>

<p>The @('basic-definitions') book wasn't always part of ihs.  We created it by
extracting \"the good parts\" of the richer @('ihs/logops-definitions') book.
We typically do <b>not</b> load the additional definitions and macros that
remain in @('ihs/logops-definitions'), or the @('@logops') book which defines
various four-valued operations.  But if you have some particular reason to want
these definitions, it would probably be fine to load them alongside Bitops.</p>

<h5>IHS Lemma Books</h5>

<p>The @('ihs/quotient-remainder-lemmas') book has lemmas about integer
division operations like @(see floor), @(see mod), @(see truncate), @(see rem),
etc.  This book generally works well with Bitops and may be a fine choice.
Other options include @('arithmetic-3') and @('arithmetic-5'); see below.</p>

<p>The @('ihs/math-lemmas') book is an extremely minimal math library.  You
should probably use a library like @('arithmetic/top') instead; see below.</p>

<p>The @('ihs/logops-lemmas') book is a key book for bit-vector reasoning in
ihs.  But you should generally <b>not</b> use it when you are using Bitops,
because the Bitops book @('ihsext-basics') supersedes it&mdash;it imports the
good rules and then introduces improved replacements for many of the
@('ihsext-basics') rules.</p>


<p>The @('ihs-lemmas') book is a wrapper that includes the other @('-lemmas')
books; it probably is best to just load @('quotient-remainder-lemmas') instead,
since you generally wouldn't want to use the other books with Bitops.</p>


<h3>@('arithmetic/')</h3>

<p>This is a very lightweight library that loads quickly and generally works
well with Bitops.  It provides modest support for reasoning about how basic
operations like @('<'), @('+'), @('-'), @('*'), @('/') and @('expt') relate to
one another over integers and rationals.</p>

<p><b>1.</b> The book @('arithmetic/top') is generally a good starting point.
It can effectively deal with simple terms like @('(+ 1 -1 a)') and apply other
obvious reductions.  This is a good book to use when your use of arithmetic is
mostly incidental, e.g., you have a function that recurs by calling @('(- n
1)') or similar.</p>

<p><b>2.</b> The book @('arithmetic/top-with-meta') is only slightly stronger;
it adds some @(see acl2::meta) rules that can more effectively cancel out
summands and factors that can arise in various equalities and inequalities.
It's a fine choice that is about on par with @('arithmetic/top'), but which is
superior in some cases.</p>


<h3>@('arithmetic-3/')</h3>

<p><b>1.</b> The basic @('arithmetic-3/bind-free/top') book is essentially
similar to the @('arithmetic') library, but features a much more sophisticated
use of meta rules for reducing sums and products, and recognizing when
arithmetic expressions return integers.  It also features a much stronger
integration with @(see acl2::non-linear-arithmetic) reasoning, which may be
especially useful when working with @('*') and @('/').</p>

<p>This book is also very compatible with Bitops and may be a good choice for
cases where @('arithmetic/top-with-meta') is not doing a good enough job with
respect to the basic arithmetic operations.  Just about the only issue is that
it has some special support for @('(expt 2 ...)') which overlaps a bit with
Bitops rules about @('ash').  But this is really pretty unlikely to cause you
any problems.</p>

<p>If your proofs involving large terms (e.g., you are doing proofs about
machine models), you might want to start with @('arithmetic/top-with-meta')
instead of @('arithmetic-3'), but only because @('arithmetic-3')'s more
powerful rules are perhaps somewhat slower&mdash;it has a lot of @(see
acl2::type-prescription) rules, for instance, and these can sometimes get
slow.</p>

<p><b>2.</b> The @('arithmetic-3/floor-mod/floor-mod') book extends
@('bind-free/top') with rules about @(see floor) and @(see mod).  It also gets
rid of @(see rem), @(see truncate), @(see round), and @(see ceiling) by
rewriting them into @('floor') and @('mod') terms.</p>

<p>Bitops has very little support for working with @('floor') and @('mod'), so
all of this is generally compatible with Bitops <b>except for powers of 2</b>.
In Bitops, we generally prefer to deal with @('(loghead n x)') and @('(logtail
n x)') instead of @('(mod x (expt 2 n))') and @('(floor x (expt 2 n))').  We
also generally prefer @('(ash 1 n)') over @('(expt 2 n)'), but this is more
minor.</p>

<p>At any rate, if you are dealing with something like @('(floor x 3)'), or
more generally with @('floor') or @('mod') by arbitrary moduli, then writing
your goals in terms of @('floor') and @('mod') and using the @('floor-mod')
book may be a fine choice.  But if you are dealing with powers of 2, it is
probably generally best to avoid @('floor') and @('mod'), and phrase your goal
using the bit-vector operations instead.</p>

<p><b>3.</b> The @('arithmetic-3/extra/top-ext') book extends the
@('floor-mod') book with additional lemmas about both the basic operators and
about @('floor') and @('mod'). </p>

<p>This is a bit heavier weight.  It adds build dependencies on
@('arithmetic-2') and a (small) portion of the @('rtl') library, and may
generally be a bit slower since, e.g., some of the rules it adds introduce
additional case splits.  But while you may not want to try this book when
dealing with very large terms, it is generally a good book to try when you need
to prove a hard lemma involving lots of arithmetic.</p>


<h3>arithmetic-5/</h3>

<p>The @('arithmetic-5/top') book is a popular, quite heavy-weight book that
is somewhat compatible with Bitops.</p>

<p>We usually prefer not to use @('arithmetic-5').  The library can sometimes
be quite slow; many rules case split and there are, for instance, a great
number of @(see acl2::type-prescription) rules that can become very expensive
in some cases.  For instance, an extreme case was @('lemma-4-1-30') from
@('rtl/rel9/seed.lisp')&mdash;we were able to speed this proof up from 651
seconds to 1 second by mostly just disabling these type-prescription rules; see
SVN revision 2160 for details.</p>

<p>On the other hand, @('arithmetic-5') is a very sophisticated library that
can deal with hard arithmetic problems, and now and again it can be useful to
use it instead of other libraries.</p>

<p>Combining @('arithmetic-5') with Bitops may sometimes be tricky.</p>

<p>As with @('arithmetic-3/floor-mod'), you will want to watch out for powers
of 2.  In Bitops we generally prefer to work with bit-vector functions like
@(see loghead), @(see logtail), @(see ash), etc., instead of writing terms
involving @(see floor) and @(see mod) terms by @('(expt 2 n)').</p>

<p>But unlike @('arithmetic-3'), @('arithmetic-5') has many rules about
bit-vector functions such as @(see logand), @(see logior), etc., and these
rules may sometimes work against you.  For instance, rules like these are likely
not what you want:</p>

@(def acl2::|(logand 1 x)|)

<p>And generally @('arithmetic-5') likes to reason about @('(integerp (* 1/2
x))') instead of @('(logcar x)'), which is messy because it introduces rational
arithmetic into your problem.</p>

<p>It's possible to overcome and work around these problems, but you may want
to be looking out for these sorts of issues and making sure that you aren't
being pulled toward competing normal forms.</p>")
