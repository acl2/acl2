; Standard Lists Library
;
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
(include-book "list-defuns")
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
(include-book "take")

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
                    ))

; For now we don't disable set functions like member-equal.  But I intend
; to do so eventually, after adding the appropriate theorems from vl, etc.

