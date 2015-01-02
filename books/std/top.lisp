; ACL2 Standard Library
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "basic/top")
(include-book "bitsets/top")
(include-book "lists/top")
(include-book "alists/top")
(include-book "typed-lists/top")
(include-book "io/top")
(include-book "strings/top")
(include-book "misc/top")
(include-book "osets/top")
(include-book "util/top")

(defsection std
  :parents (top)
  :short "Standard libraries for ACL2."

  :long "<p>The <b>std</b> library is meant to become <i>ACL2, Batteries
Included</i>.  Its features a wide variety of books that work well together to
provide a well-thought-out, documented, coherent reasoning strategy.</p>

<p>@('Std') is currently under active development.  You are welcome to use it,
but please be aware that things may change out from under you.</p>

<p>So far, @('std') itself includes libraries about
   <see topic='@(url std/basic)'>basic</see> concepts,
   <see topic='@(url std/lists)'>lists</see>,
   <see topic='@(url std/osets)'>sets</see>,
   <see topic='@(url std/alists)'>alists</see>,
   <see topic='@(url std/typed-lists)'>typed-lists</see>, and
   <see topic='@(url std/io)'>input/output</see>.
Each of these libraries provides many lemmas for reasoning about built-in
ACL2 functions, and also many additional functions.  There is also a very
convenient @(see std/util) macro library, with macros that automate many
otherwise-tedious tasks.</p>")

(defxdoc where-do-i-place-my-book
  :parents (std projects books best-practices)
  :short "How to decide where in the books directory structure to place your book"
  :long "<p>Here is our loose view of the books organization:</p>

  <ol>
    <li>project-specific stuff</li>
    <li>useful libraries not yet vetted by the 'std' maintainers</li>
    <li>libraries 'approved' for the standard approach</li>
  </ol>

  <p>Books in category (1) easily belong in @('books/projects').</p>

  <p>Books in category (2) can go in the top-level @('books') directory or in
  projects.  There's so much stuff in the top-level directory, that we suggest
  @('books/projects') -- especially for people that are new to the ACL2
  community.</p>

  <p>Once general-use books are vetted by the ACL2 book Czars, they go in the
  @('std') directory.  Some of the criteria the book czars use to decide
  whether a book should be in @('std') follow below:</p>

  <ul>
    <li>Design is consistent with other @('std') books</li>
    <li>Has some general purpose use -- e.g., data structure books are very
    much something that you would expect to see in a general framework for a
    language like Java</li>
    <li>Has good documentation that explains how to use it</li>
  </ul>")
