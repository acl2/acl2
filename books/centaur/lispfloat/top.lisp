; Lispfloat - Interface to the Common Lisp Floating Point Operations
; Copyright (C) 2016 Centaur Technology
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

(in-package "LISPFLOAT")
(include-book "ops-logic")
(include-book "ops-exec")

(defxdoc lispfloat
  :parents (arithmetic)
  :short "A library for computing with (but not reasoning about) Common Lisp
floats from within ACL2."

  :long "<h3>Introduction</h3>

<p>ACL2 doesn't provide a floating point number representation or any
operations for floating point arithmetic.  So if you want to use floating point
numbers in ACL2, what are your options?</p>

<p>One approach is to model floating-point numbers using some machine-like
representation (e.g., as triples with a sign bit, some exponent bits, and some
mantissa bits) and write ACL2 functions that carry out the desired FP
operations on top of this representation.  This is done in, for instance, the
@(see rtl::rtl) library.  This approach is well-principled and has many
advantages, e.g., it provides real logical definitions that can be reasoned
about.  But it is also a lot of work and, for instance, RTL is a relatively
heavyweight library.</p>

<p>The <b>lispfloat</b> library takes a much less-principled but lighter-weight
approach.  Our goal is not to try to specify how FP operations work, but merely
to try to provide a pragmatic way to compute with floats by connecting ACL2 to
the existing FP implementation provided by the Lisp environment.  The main
issues here are how to represent floats in a convenient way for the ACL2
program (since real floats aren't valid ACL2 objects), and how to provide a
sound connection to the Lisp runtime.</p>

<h5>Representation</h5>

<p>To represent floats as ACL2 objects we just use rationals.  This is quite
imperfect.  There are weird floats (infinities, nans) that don't even represent
rationals, and positive/negative versions of zero that will both map to 0.
There are also (of course) rationals that cannot be represented as floats
without being rounded.</p>

<p>But in practice this is still pretty good.  Any ``sensible'' float (e.g.,
normal, denormal, or the zeroes) can be turned into a rational and back without
loss of precision.  And any FP operation that doesn't do cause an exception
will result in a sensible number.  In short, if we start with sensible numbers
and then only carry out reasonable FP operations on them, we should always stay
in the realm of sensible numbers where using rationals works fine.</p>

<h5>Operations</h5>

<p>The floating point functions that we implement each take rationals as inputs
and produce rationals as their results.  These functions might be called on bad
inputs such as (1) rational numbers that we cannot correctly turn into floats
because they are too big or would require rounding, or (2) arguments that cause
the underlying FP operation to encounter some exception like an overflow,
divide by zero, or similar.</p>

<p>To identify these cases, each FP operation also returns a potential error
message, which is either a string that describes the problem or is @('nil')
when everything is OK.  The functions also have names like @(see er-float+) to
remind you that they may encounter into errors.</p>

<h5>Logical Story</h5>

<p>We do not provide logical definitions for our floating-point operations, but
instead introduce them with @(see encapsulate) and constrain them so that they
are known to produce sensible results (error messages are strings or @('nil'),
answers are rationals) and to satisfy basic @(see acl2::congruence) rules for
rationals for compatibility with the @(see acl2::fty-discipline).</p>

<p>By themselves, these logical definitions are just an ordinary @(see
encapsulate) and hence don't require any trust tags.  You can load just these
logical definitions by doing:</p>

@({
    (include-book \"centaur/lispfloat/ops-logic\" :dir :system)
})

<p>However, note that these operations can't be executed until you load the
executable versions, typically by including @('lispfloat/top').</p>

<h5>Executable Versions</h5>

<p>We define executable versions of the operations as ``untouchable''
program-mode functions, which we then (using a trust-tag) redefine in raw
Common Lisp and attach to the logical definitions.</p>

<p>Once this has been done, you can run these functions to carry out floating
point computations.  For example:</p>

@({
    ACL2 !>(include-book \"centaur/lispfloat/top\" :dir :system)

    ACL2 !>(lispfloat::er-float+ 1/2 1/2)
    (nil 1)  ;; no error, answer is 1
})

<p>Note however that you will still not be able to prove anything about the
actual evaluations of these floating-point operations.  For instance, trying to
prove a theorem like this will <b>fail</b>:</p>

@({
    (thm (equal (mv-nth 1 (lispfloat::er-float+ 1/2 1/2)) 1))
})

<h5>Supported Operations</h5>

<p>We currently support single- and double-precision versions of the basic
arithmetic operations (+, -, *, /), exponentiation of @('a^b') and @('e^x'),
square root, sine, cosine, and tangent.</p>

<p>We don't yet implement many operations that are available in Common Lisp
such as arcsine, log, etc., because they can return complex numbers for some
inputs and we haven't decided how to handle that yet.</p>

<p>Other functions that are currently missing but would probably be mostly
straightforward to add: basic inequality comparisons, round a float/double to
the nearest integer, parse a string as a float/double (doesn't seem to be built
into Common Lisp but there are Quicklisp libraries like parse-number), convert
a float/double into a string, etc.</p>")

