; GL - A Symbolic Simulation Framework for ACL2
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "generic-geval")
(include-book "symbolic-arithmetic")
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
   DENOMINATOR
   CDR
;   COMPLEX
   CAR
   CONSP
   SYMBOL-NAME
   CHAR-CODE
   IMAGPART
   SYMBOLP
   REALPART
   NUMERATOR
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
   acl2::bool-fix$inline
   acl2::bool->bit$inline
   bool->sign
   hons-assoc-equal

   ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
   NOT IMPLIES
   EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
   PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
   ;; FORCE CASE-SPLIT
   ;; DOUBLE-REWRITE

   logapp int-set-sign maybe-integer
   binary-minus-for-gl))


(in-theory (disable eval-g-base))

