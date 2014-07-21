; Standard Typed Lists Library
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "acl2-number-listp")
(include-book "atom-listp")
(include-book "boolean-listp")
(include-book "character-listp")
(include-book "eqlable-listp")
(include-book "integer-listp")
(include-book "nat-listp")
(include-book "pseudo-term-listp")
(include-book "rational-listp")
(include-book "string-listp")
(include-book "symbol-listp")
(include-book "signed-byte-listp")
(include-book "unsigned-byte-listp")

(defsection std/typed-lists
  :parents (std)
  :short "A library about the built-in typed lists, like @(see
character-listp), @(see nat-listp), @(see string-listp), etc."

  :long "<p>The @('std/typed-lists') library provides basic lemmas about
built-in ACL2 functions.</p>

<p>If you want to load everything in the library, you can just include the
@('top') book, e.g.,</p>

@({ (include-book \"std/typed-lists/top\" :dir :system) })

<p>Alternately, it is perfectly reasonable to just include the individual books
that deal with the typed lists you are interested in.  For instance,</p>

@({
    (include-book \"std/typed-lists/character-listp\" :dir :system)
    (include-book \"std/typed-lists/symbol-listp\" :dir :system)
    ;; and so on.
})

<p>Most of the typed-lists library is generated automatically by @(see
std::deflist).  You may find this macro useful for introducing your own, custom
typed lists.</p>")

