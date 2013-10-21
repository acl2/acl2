; GL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "generic-geval")
(include-book "symbolic-arithmetic-fns")
;; (include-book "defapply")


(def-eval-g eval-g-base
  (BINARY-*
   cons if
   BINARY-+
   PKG-WITNESS
;   UNARY-/
   UNARY--
   COMPLEX-RATIONALP
;   BAD-ATOM<=
   ACL2-NUMBERP
   SYMBOL-PACKAGE-NAME
   INTERN-IN-PACKAGE-OF-SYMBOL
   CODE-CHAR
;   DENOMINATOR
   CDR
;   COMPLEX
   CAR
   CONSP
   SYMBOL-NAME
   CHAR-CODE
   IMAGPART
   SYMBOLP
   REALPART
;   NUMERATOR
   EQUAL
   STRINGP
   RATIONALP
   CONS
   INTEGERP
   CHARACTERP
   <
   COERCE
   booleanp
   logbitp
   binary-logand
   binary-logior
   acl2::binary-logxor
   acl2::binary-logeqv
   lognot
   ash
   integer-length
   floor
   mod
   truncate
   rem
   acl2::boolfix
   hons-assoc-equal

   ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
   NOT IMPLIES
   EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
   PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
   ;; FORCE CASE-SPLIT
   ;; DOUBLE-REWRITE

   logapp int-set-sign maybe-integer
   binary--))


(in-theory (disable eval-g-base))

