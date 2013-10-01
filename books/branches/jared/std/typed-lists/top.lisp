; Standard Typed Lists Library
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "atom-listp")
(include-book "character-listp")
(include-book "nat-listp")
(include-book "string-listp")
(include-book "symbol-listp")
(include-book "signed-byte-listp")
(include-book "unsigned-byte-listp")

(defsection std/typed-lists
  :parents (std)
  :short "A library about the built-in typed lists, like @(see
character-listp), @(see nat-listp), string-listp), etc."

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
cutil::deflist).  You may find this macro useful for introducing your own,
custom typed lists.</p>

<p>BOZO this library is not very complete.  We should probably add books
about the other kinds of typed-list recognizers.</p>")

