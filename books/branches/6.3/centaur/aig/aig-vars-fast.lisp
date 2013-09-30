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
; fast AIG variable collection cheat using destructive consing
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

;; Warning!! Don't include this book if you're doing anything involving
;; parallelism.  Uses destructive operations on conses to do fast memoization.
;; See ../misc/fast-cons-memo.lisp.

(include-book "tools/include-raw" :dir :system)
(include-book "aig-vars-ext")
(include-book "../misc/fast-cons-memo")

(defttag aig-vars)

; (depends-on "aig-vars-fast-raw.lsp")
(include-raw "aig-vars-fast-raw.lsp")

