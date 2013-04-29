; Standard Lists Library
; Portions are Copyright (C) 2008-2013 Centaur Technology
; Portions are Copyright (C) 2004-2006 by Jared Davis
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

; This is Jared's preferred way to load the list library and get a decent
; theory.  If you don't want to keep functions like APPEND and LEN disabled,
; you can include the individual books, which mostly try to leave the default
; theory alone.

(include-book "append")
(include-book "coerce")
(include-book "duplicity")
(include-book "equiv")
(include-book "final-cdr")
(include-book "flatten")
(include-book "len")
(include-book "list-fix")
(include-book "make-character-list")
(include-book "mfc-utils")
(include-book "no-duplicatesp")
(include-book "nthcdr")
(include-book "prefixp")
(include-book "repeat")
(include-book "revappend")
(include-book "reverse")
(include-book "rev")
(include-book "sets")
(include-book "sublistp")
(include-book "subseq")
(include-book "take")
(include-book "list-defuns")

(in-theory (disable ;; I often use len as a way to induct, so I only disable
                    ;; its definition.
                    (:definition len)
                    ;; The other functions can just be turned off.
                    append
                    revappend
                    no-duplicatesp-equal
                    make-character-list
                    take-redefinition
                    nthcdr
                    subseq-list
                    subsetp
                    intersectp
                    ;; BOZO eventually disable member and other functions
                    ))


(defsection std/lists
  :parents (std)
  :short "A library for reasoning about basic list operations like @('append'),
@('len'), @('member'), @('take'), etc."

  :long "<p>The @('std/lists') library provides lemmas that are useful when
reasoning about the basic list functions that are built into ACL2, and also
defines many additional functions like @(see list-fix), @(see rev), @(see
set-equiv), and so on.</p>

<p>The recommended way to load the library, especially for beginning to
intermediate users, is to simply include the @('top') book, e.g.,</p>

@({ (include-book \"std/lists/top\" :dir :system) })

<p>The top book loads quickly (typically under a second), gives you everything
we have to offer, and sets up a \"recommended\" theory.  This theory differs
from the default ACL2 theory in some notable ways, e.g., it @(see disable)s
some basic, built-in ACL2 list functions like @('append') and @('len').</p>

<p>Even for advanced users, we recommend using the @('top') book if possible.
However, in case you find this book to be too heavy or too incompatible with
your existing developments, the library is arranged in a \"buffet\" style that
is meant to allow you to load as little or as much as you like.  A useful
starting point is</p>

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
@('std/lists') directory.  In most cases, these individual books are meant to
be reasonably unobtrusive, e.g., loading the @('append') book will not disable
@(see append).</p>")


(defsection std
  :short "Some \"standard\" libraries for ACL2.")


