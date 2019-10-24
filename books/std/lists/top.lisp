; ACL2 Standard Library
; Portions are Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")

; This is Jared's preferred way to load the list library and get a decent
; theory.  If you don't want to keep functions like APPEND and LEN disabled,
; you can include the individual books, which mostly try to leave the default
; theory alone.

(include-book "append")
(include-book "all-equalp")
(include-book "bits-equiv")
(include-book "duplicity")
(include-book "equiv")
(include-book "final-cdr")
(include-book "flatten")
(include-book "intersection")
(include-book "index-of")
(include-book "intersection")
(include-book "intersectp")
(include-book "last")
(include-book "len")
(include-book "list-fix")
(include-book "mfc-utils")
(include-book "nats-equiv")
(include-book "no-duplicatesp")
(include-book "nth")
(include-book "nthcdr")
(include-book "prefixp")
(include-book "remove")
(include-book "remove-duplicates")
(include-book "remove1-equal")
(include-book "repeat")
(include-book "resize-list")
(include-book "revappend")
(include-book "reverse")
(include-book "rev")
(include-book "sets")
(include-book "set-difference")
(include-book "sublistp")
(include-book "subseq")
(include-book "suffixp")
(include-book "take")
(include-book "true-listp")
(include-book "update-nth")
(include-book "list-defuns")
(include-book "union")

; BOZO it might be best to move these disables into the corresponding
; books, to make things more consistent when you load the individual
; books versus the whole library.

(in-theory (disable ;; I often use len as a way to induct, so I only disable
                    ;; its definition.
                    (:definition len)
                    ;; The other functions can just be turned off.
                    append
                    revappend
                    no-duplicatesp-equal
                    make-character-list
                    take
                    nthcdr
                    subseq-list
                    resize-list
                    last
                    butlast
                    remove
                    ;; It seems like disabling these is hard to do in general, so
                    ;; I'll leave nth and update-nth enabled.
                    ;; nth
                    ;; update-nth
                    member
                    subsetp
                    intersectp
                    union-equal
                    set-difference-equal
                    intersection-equal
                    ))


(defsection std/lists
  :parents (std)
  :short "A library for reasoning about basic list operations like @(see
append), @(see len), @(see member), @(see take), etc."

  :long "<h3>Introduction</h3>

<p>The @('std/lists') library provides lemmas that are useful when reasoning
about the basic list functions that are built into ACL2, and also defines some
additional functions like @(see list-fix), @(see rev), @(see set-equiv), and so
on.</p>

<p>The @('std/lists') library is based largely on books that were previously
part of the @('unicode') library, but also incorporates ideas from earlier
books such as @('data-structures/list-defthms') and
@('data-structures/number-list-defthms') and also from @('coi/lists').</p>


<h3>Loading the Library</h3>

<p>The recommended way to load the library, especially for beginning to
intermediate ACL2 users, is to simply include the @('top') book, e.g.,</p>

@({ (include-book \"std/lists/top\" :dir :system) })

<p>This book loads quickly (typically in under a second), gives you everything
we have to offer, and sets up a \"recommended\" theory.  See below for some
general comments about this theory.</p>

<p>For advanced users, we recommend using the @('top') book if possible.
However, in case you find this book to be too heavy or too incompatible with
your existing developments, the library is mostly arranged in a \"buffet\"
style that is meant to allow you to load as little or as much as you like.  A
particularly useful book is</p>

@({ (include-book \"std/lists/list-defuns\" :dir :system) })

<p>which adds the new @('std/lists') functions like @(see list-fix), but
has (almost) no theorems.  Typically, you would then want to (perhaps locally)
include individual books for the particular list functions you are dealing
with.  The books have sensible names, e.g., you might write:</p>

@({
 (include-book \"std/lists/list-defuns\" :dir :system)
 (local (include-book \"std/lists/append\" :dir :system))
 (local (include-book \"std/lists/rev\" :dir :system))
 (local (include-book \"std/lists/repeat\" :dir :system))
})

<p>The best way to see what books are available is to just run @('ls') in the
@('std/lists') directory.  Unlike the top book, most individual books are meant
to be reasonably unobtrusive, e.g., loading the @('append') book will not
disable @(see append).</p>


<h3>Things to Note</h3>

<p>When you include the @('top') book, note that many basic, built-in ACL2 list
functions like @('append') and @('len') will be @(see disable)d.  As a result,
ACL2 will sometimes not automatically try to induct as it did before.  You may
find that you need to give explicit @(':induct') @(see hints), or explicitly
re-@(see enable) these basic functions during certain theorems.  (On the flip
side, you may also find that you are spending less time trying to prove
theorems using incorrect induction schemes.)</p>

<p>The library introduces a couple of useful @(see equivalence) relations,
namely:</p>

<dl>
<dt>@(see list-equiv)</dt>
<dd>Equivalences of lists based on @(see list-fix).</dd>
<dd>Respected in some way by most list-processing functions.</dd>
</dl>

<dl>
<dt>@(see set-equiv)</dt>
<dd>Equivalence of lists up to @(see member)ship, but ignoring order and @(see
duplicity).</dd>
<dd>@('list-equiv') is a @(see refinement) of @('set-equiv').</dd>
<dd>Respected in a strong way by most \"lists as sets\" functions, e.g., @(see
subsetp), @(see union$), etc.</dd>
<dd>Preserved by many other ordinary list functions like @(see append), @(see
rev), etc.</dd>
</dl>

<p>These rules allow for some very powerful equivalence-based reasoning.  When
introducing new list-processing functions, it is generally a good idea to
define the appropriate @(see congruence) rules for these relations.</p>")
