; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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

(in-package "BITSETS")
(include-book "bitsets")
(include-book "sbitsets")

(defxdoc std/bitsets
  :parents (std)
  :short "Optimized libraries for representing finite sets of natural numbers
using bit masks, featuring a strong connection to the @(see std/osets) library."

  :long "<h3>Introduction</h3>

<p>The @('std/bitsets') library offers two ways to represent sets of natural
numbers.</p>

<ul>

<li>@(see bitsets)&mdash;<i>plain bitsets</i>&mdash;each set is encoded as a
single bit-mask, i.e., using a single natural number.  This representation is
particularly efficient for sets of very small numbers but cannot cope well with
large elements.</li>

<li>@(see sbitsets)&mdash;<i>sparse bitsets</i>&mdash;each set is encoded as an
ordered list of offset/block pairs, each block being a bit-mask for
@(`*sbitset-block-size*`) elements.  This representation is more forgiving; it
can handle larger sets, perhaps with very large elements, and still achieves
bitset-like efficiencies in many cases.</li>

</ul>

<p>Either representation provides a nice set-level abstraction that should
shield you from reasoning about the underlying bitwise arithmetic operations;
see @(see reasoning).</p>

<h3>Loading the Library</h3>

<p>To load everything (except for optimizations that require trust tags):</p>

@({
    (include-book \"std/bitsets/top\" :dir :system)
})

<p>Alternately, for just the plain bitset library:</p>

@({
    (include-book \"std/bitsets/bitsets\" :dir :system)
})

<p>Or for just the sparse bitsets library:</p>

@({
    (include-book \"std/bitsets/sbitsets\" :dir :system)
})

<h5>Optional Optimizations</h5>

<p>You may be able to substantially speed up the @(see bitset-members)
operation for large sets, perhaps especially on CCL, by loading an optimized,
raw Lisp definition:</p>

@({
    (include-book \"std/bitsets/bitsets-opt\" :dir :system)
})

<p>See @(see ttag-bitset-members) and @(see bignum-extract) for details.</p>")


(defxdoc utilities
  :parents (bitsets)
  :short "Utility functions.")


(defsection reasoning
  :parents (std/bitsets)
  :short "How to reason about bitsets."

  :long "<box><p>Note: for now this discussion is only about plain @(see
bitsets).  In the future, we intend this discussion to apply equally well to
@(see sbitsets).</p></box>

<p>A general goal of the bitsets library is to let you take advantage of
efficient operations like @('logand') and @('logior') without having to do any
arithmetic reasoning.  Instead, ideally, you should be able to carry out all of
your reasoning on the level of sets.</p>

<h4>Basic Approach</h4>

<p>To achieve this, we try to cast everything in terms of @(see
bitset-members).  If you want to reason about some bitset-producing function
@('foo'), then you should typically try to write your theorems about:</p>

@({
 (bitset-members (foo ...))
})

<p>instead of directly proving something about:</p>

@({
 (foo ...)
})

<p>For example, to reason about @(see bitset-union) we prove:</p>

@(thm bitset-members-of-bitset-union)

<p>In most cases, this theorem is sufficient for reasoning about the behavior
of @('bitset-union').</p>

<h4>Equivalence Proofs</h4>

<p>The @('bitset-members') approach is good most of the time, but in some cases
you may wish to show that two bitset-producing functions literally create the
same bitset.  That is, instead of showing:</p>

@({
 (bitset-members (foo ...)) = (bitset-members (bar ...))
})

<p>it is perhaps better to prove:</p>

@({
 (foo ...) = (bar ...)
})

<p>It should be automatic to prove this stronger form (after first proving the
weaker form) by using the theorem:</p>

@(def equal-bitsets-by-membership)")
