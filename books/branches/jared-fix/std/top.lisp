; Standard Library
; Portions are Copyright (C) 2008-2013 Centaur Technology
; Portions are Copyright (C) 2004-2013 Jared Davis
; Portions are Copyright (C) 2013 Kookamara LLC
; See individual books for details.
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "lists/top")
(include-book "alists/top")
(include-book "typed-lists/top")
(include-book "io/top")
(include-book "strings/top")
(include-book "misc/top")
(include-book "osets/top")

(defsection std
  :short "Standard libraries for ACL2."

  :long "<p>The @('std') library is meant to become <i>ACL2, Batteries
Included</i>.  Its features a wide variety of books that work well together to
provide a well-thought-out, documented, coherent reasoning strategy.</p>

<p>@('Std') is currently under active development.  You are welcome to use it,
but please be aware that things may change out from under you.</p>

<p>So far, @('std') itself includes libraries about
   <see topic='@(url std/lists)'>lists</see>,
   <see topic='@(url std/alists)'>alists</see>,
   <see topic='@(url std/typed-lists)'>typed-lists</see>, and
   <see topic='@(url std/io)'>input/output</see>.
Each of these libraries provides many lemmas for reasoning about built-in
ACL2 functions, and also many additional functions.</p>

<p>The @('Std') books already play well with libraries such as @(see osets),
@(see str), and @(see cutil).  We are working to further integrate these
libraries, and may soon incorporate some of them into @(see std), itself.</p>")


