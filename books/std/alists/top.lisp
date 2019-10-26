; Standard Association Lists Library
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; This is Jared's preferred way to load the alist library and get a decent
; theory.  If you want to keep functions like ALISTP and STRIP-CARS enabled,
; you can include the individual books, which mostly try to leave the default
; theory alone.

(include-book "alistp")
(include-book "alist-keys")
(include-book "alist-vals")
(include-book "alist-fix")
(include-book "append-alist-keys")
(include-book "append-alist-vals")
(include-book "alist-equiv")
(include-book "alists-compatible")
(include-book "fal-all-boundp")
(include-book "fal-find-any")
(include-book "fal-extract")
(include-book "fal-extract-vals")
(include-book "fast-alist-clean")
(include-book "hons-assoc-equal")
(include-book "hons-rassoc-equal")
(include-book "hons-remove-assoc")
(include-book "strip-cars")
(include-book "strip-cdrs")
(include-book "pairlis")
(include-book "remove-assocs")
(include-book "remove-assoc-equal")
(include-book "alist-map-keys")
(include-book "alist-map-vals")
(include-book "assoc")

(include-book "alist-defuns")

(in-theory (disable alistp
                    hons-assoc-equal
                    strip-cars
                    strip-cdrs
                    pairlis$
                    ))


(defsection std/alists
  :parents (std alists)
  :short "A library for reasoning about association list (alist) operations
like @(see alist-keys), @(see alist-vals), @(see hons-get), etc."

  :long "<h3>Introduction</h3>

<p>An association list is a fundamental data structure that
associates (\"binds\") some @('keys') to @('value')s.  In other programming
languages, alists may go by names like <i>dictionaries</i>, <i>maps</i>,
<i>hashes</i>, <i>associative arrays</i>, and the like.</p>

<p>The @('std/alists') library provides functions and lemmas about:</p>

<ul>

<li><b>\"traditional\" alist operations</b> like @(see alistp), @(see assoc),
and @(see strip-cars), which have long been built into ACL2.</li>

<li><b>\"modern\" alist operations</b> like @(see hons-assoc-equal), @(see
alist-keys), @(see make-fal), etc., which have better compatibility with
@(see fast-alists).</li>

</ul>

<p>In the \"traditional\" view, an alist is something recognized by @(see
alistp)&mdash;a @(see true-listp) of conses.  This @('alistp') recognizer
serves as a @(see guard) for functions like @(see assoc), @(see rassoc), @(see
strip-cars), and so forth.</p>

<p>In contrast, in the \"modern\" view, the @(see final-cdr) of an alist is not
expected to be @('nil'); instead it may be any atom.  (This can be used, e.g.,
to name @(see fast-alists) and to govern the sizes of their initial hash
tables; see @(see hons-acons) for details.)  Any traditional @(see alistp) is
still perfectly valid under this modern view, but these new kinds of alists,
with their weird final cdrs, are incompatible with traditional alist functions
like @(see assoc).</p>


<h3>The Non-Alist Convention</h3>

<p>Going further, in the modern view, we do not even expect that the elements
of an alist must necessarily be conses.  Instead, a modern alist function
simply skips past any atoms in its input.  We call this the <b>non-alist
convention</b>.</p>

<p>Following the non-alist convention means that functions like @(see
alist-keys) and @(see hons-assoc-equal) avoid needing any guard, which is
occasionally convenient.  More importantly, it means that when reasoning about
modern alist functions, we typically do not need any @(see alistp) style
hypotheses.  For instance, here is a typical, beautiful, hypothesis-free
theorem about @(see hons-assoc-equal):</p>

@({
    (equal (hons-assoc-equal key (append x y))
           (or (hons-assoc-equal key x)
               (hons-assoc-equal key y)))
})

<p>By comparison, the analogous theorem for the traditional @(see assoc)
function requires a hypothesis like @('(alistp a)') or @('(not (equal key
nil))').  Without such a hypothesis, we run into \"degenerate\" cases due to
taking the @(see car)s of arbitrary @(see atom)s.  For instance,</p>

@({
    let key = nil
    let x = (nil 1 2)
    let y = (a b c)

    then (assoc key x) --> nil
         (assoc key y) --> a

    (assoc nil (append x y))              --> nil   }
                                                    } different!
    (or (assoc key x)   -->  (or nil a)   --> a     }
        (assoc key y))
})

<p>This weird behavior for @('(assoc nil x)') leads to complications for many
theorems about traditional alist operations.  Following the non-alist
convention allows modern alist operations to avoid this problem.</p>


<h3>Loading the Library</h3>

<p>The recommended way to load the library, especially for beginning to
intermediate ACL2 users, is to simply include the top book, e.g.,</p>

@({ (include-book \"std/alists/top\" :dir :system) })

<p>This book loads quickly (typically in under a second), gives you everything
we have to offer, and sets up a \"recommended\" theory.</p>

<box><p>Note: Loading the @('std/alists/top') book will also result in loading
the @(see std/lists) library.  See the documentation for @('std/lists') for
important notes about its @(see equivalence) relations, the functions it will
@(see disable), etc.</p></box>


<h3>Things to Note</h3>

<p>When you include the @('top') book, several basic, built-in ACL2 alist
functions like @(see alistp), @(see strip-cars), @(see assoc), and so forth
will be @(see disable)d.  As a result, ACL2 will sometimes not automatically
try to induct as it did before.  You may find that you need to give explicit
@(':induct') @(see hints), or explicitly re-@(see enable) these basic functions
during certain theorems. (On the flip side, you may also find that you are
spending less time trying to prove theorems using incorrect induction
schemes.)</p>

<p>A very useful @(see equivalence) relation when working with association
lists is <b>@(see alist-equiv)</b>, which says whether alists agree on the
value of every key.  Many alist operations respect this equivalence relation.
It is generally a good idea to define appropriate @('alist-equiv') @(see
congruence) rules for new alist-processing functions.</p>")
