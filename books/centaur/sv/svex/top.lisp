; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "4vec")
(include-book "4vmask")
(include-book "aig-arith")
;; Not bits -- it's just lemmas about b-and/b-not/etc., should be local
(include-book "assigns-compose")
(include-book "env-ops")
(include-book "eval")
(include-book "lattice")
;; not rsh-concat, it should be local
;; (include-book "rsh-concat")
(include-book "argmasks")
;; Note svex-equivs, it's apparently not included anywhere?
;; (include-book "svex-equivs")
(include-book "svex")
(include-book "rewrite-base")
(include-book "rewrite")
(include-book "rewrite-rules")
(include-book "rewrite-trace")
(include-book "symbolic")
(include-book "vars")
(include-book "xeval")

;; ttag book needed for efficient rewriting (trailing 0 count).
(include-book "std/bitsets/bignum-extract-opt" :dir :system)



(defxdoc why-infinite-width
  :parents (expressions)
  :short "Notes about our use of infinite-width vectors as the basis for our
expression language."

  :long "<p>It probably seems very odd to base the core of a hardware
description language on infinite width vectors.  After all, in real hardware
every wire and register will, of course, be of some particular, finite
size.</p>

<p>In HDLs like Verilog, every variable is always declared to have some
particular width, and every operator like @('a + b') ultimately ends up being
interpreted as having some fixed size&mdash;well, at least after
``elaboration'' is over.  As a concrete example to discuss, consider a Verilog
fragment like the following:</p>

@({
     wire signed [3:0] a = ...;
     wire [15:8] b = ...;
     wire c = ...;
     wire [7:0] ans = {8{c}} & (a % b);
})

<p>We can imagine developing vector-level expression languages that include
size information.  This might be done, for instance, by having a kind of
<b>context</b> that records the sizes and ranges of the various expressions,
and then interpreting vector-level expressions in some way that is relative to
this context.  For instance, our context might be some kind of structure that
binds names to ranges/types, say:</p>

@({
      ((a   (signed 3 0))
       (b   (unsigned 15 8))
       (c   (unsigned nil nil))
       (ans (unsigned 7 0)))
})

<p>And given such a context, we could write functions to infer the widths of
operators.  We might, for instance, represent the expression for @('ans') as
something like this:</p>

@({
     (bitand (replicate 8 c) (mod (cast-to-unsigned a) b))
})

<p>And then, using the context, we would be able to see that this occurrence of
@('mod') is an 8-bit operation, and its first argument @('a') needs to be
zero-extended from 4 bits to 8 bits, and so on.  We might be able to use the
context to type-check expressions and determine that certain expressions, like
@('(bitsel 5 a)'), are invalid since @('5') is not a valid index into a wire
from @('3') to @('0').</p>

<p>All of this might be a fine approach, but we have not pursued it.</p>

<p>Instead, in our expression language, we adopt the convention that every
variable represents an infinitely long, signed value.  The main consequence of
this is that we do not need a context.  Instead, all size/signedness coercions
become explicit in the expressions themselves.</p>

<p>This seems like a strong advantage.  It means, for instance, that every
expression can be understood, exactly, all by itself, without having to
consider or look up any other information.</p>")

