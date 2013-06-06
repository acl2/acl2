; Centaur Miscellaneous Books
; Copyright (C) 2012 Centaur Technology
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
; fast cons memoization utility -- acl2 book wrapper
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(defttag fast-cons-memo)

;; Warning!  Not compatible with parallelism.

;; Credit/blame to Bob Boyer for showing me this type of optimization.

;; This book provides some utilities to make it slightly less error-prone to do
;; a horrible trick: Say you want to do some computation on a cons tree, and
;; memoize intermediate results for some internal nodes.  You can do this using
;; a hash table, which is relatively safe, or you can use the following trick:
;; Whenever you're ready to store a result, push a record containing the
;; current cons node and its car and cdr onto a recovery stack.  Then, clobber
;; the car and cdr of the node: set the cdr to a particular value recognized as
;; meaning "i'm done here", and the car to the result.  Whenever you descend to
;; a cons node with the special cdr value, just return the car value, since
;; that's its memoized result.  When you finish the computation, restore all
;; the conses by going through the recovery stack and undoing all your
;; destructive operations.

;; Care must be taken to recover correctly if such a function is interrupted.
;; The with-fast-cons-memo macro takes care of this using unwind-protect.

;; Of course, if you have some other thread looking at the same conses that
;; this thread is destructively updating, you'll get into a lot of trouble. :-)

;; (depends-on "fast-cons-memo-raw.lsp")
(include-raw "fast-cons-memo-raw.lsp")
