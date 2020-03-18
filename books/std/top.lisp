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
(include-book "stobjs/top")
(include-book "osets/top")
(include-book "util/top")
(include-book "typed-alists/top")
(include-book "testing/top")
(include-book "system/top")

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
   <see topic='@(url std/typed-lists)'>typed-lists</see>,
   <see topic='@(url acl2::std/stobjs)'>stobjs</see>,
   <see topic='@(url std/io)'>input/output</see>.
Each of these libraries provides many lemmas for reasoning about built-in
ACL2 functions, and also many additional functions.  There is also a very
convenient @(see std/util) macro library, with macros that automate many
otherwise-tedious tasks.  There is also a @(see std/testing) library with
utilities to create tests.</p>")
