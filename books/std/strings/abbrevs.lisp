; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "top")

(defmacro cat (&rest args) `(STR::cat . ,args))

(defmacro append-chars (x y) `(STR::append-chars ,x ,y))
(add-macro-alias append-chars STR::append-chars)

(defmacro append-firstn-chars (n x y) `(STR::append-firstn-chars ,n ,x ,y))
(add-macro-alias append-firstn-chars STR::append-firstn-chars)

(defmacro revappend-chars (x y) `(STR::revappend-chars ,x ,y))
(add-macro-alias revappend-chars STR::revappend-chars)



(defmacro charlisteqv (x y) `(STR::charlisteqv ,x ,y))
(add-macro-alias charlisteqv STR::charlisteqv)


(defmacro collect-strs-with-isubstr (a x) `(STR::collect-strs-with-isubstr ,a ,x))
(add-macro-alias collect-strs-with-isubstr STR::collect-strs-with-isubstr)

(defmacro collect-syms-with-isubstr (a x) `(STR::collect-syms-with-isubstr ,a ,x))
(add-macro-alias collect-syms-with-isubstr STR::collect-syms-with-isubstr)


(defmacro dec-digit-char-p (x) `(STR::dec-digit-char-p ,x))
(add-macro-alias dec-digit-char-p STR::dec-digit-char-p)

(defmacro dec-digit-char-value (x) `(STR::dec-digit-char-value ,x))
(add-macro-alias dec-digit-char-value STR::dec-digit-char-value)

(defmacro dec-digit-char-listp (x) `(STR::dec-digit-char-listp ,x))
(add-macro-alias dec-digit-char-listp STR::dec-digit-char-listp)

(defmacro dec-digit-char-list-value (x) `(STR::dec-digit-char-list-value ,x))
(add-macro-alias dec-digit-char-list-value STR::dec-digit-char-list-value)

(defmacro charlistnat< (x y) `(STR::charlistnat< ,x ,y))
(add-macro-alias charlistnat< STR::charlistnat<)


(defmacro firstn-chars (x y) `(STR::firstn-chars ,x ,y))
(add-macro-alias firstn-chars STR::firstn-chars)


(defmacro html-encode-string (x tabsize) `(STR::html-encode-string ,x ,tabsize))
(add-macro-alias html-encode-string STR::html-encode-string)

(defmacro ichareqv (x) `(STR::ichareqv ,x))
(add-macro-alias ichareqv STR::ichareqv)

(defmacro ichar< (x y) `(STR::ichar< ,x ,y))
(add-macro-alias ichar< STR::ichar<)

(defmacro icharlisteqv (x) `(STR::icharlisteqv ,x))
(add-macro-alias icharlisteqv STR::icharlisteqv)

(defmacro icharlist< (x y) `(STR::icharlist< ,x ,y))
(add-macro-alias icharlist< STR::icharlist<)

(defmacro iprefixp (x) `(STR::iprefixp ,x))
(add-macro-alias iprefixp STR::iprefixp)

(defmacro istreqv (x) `(STR::istreqv ,x))
(add-macro-alias istreqv STR::istreqv)

(defmacro istr< (x y) `(STR::istr< ,x ,y))
(add-macro-alias istr< STR::istr<)

(defmacro istrsort (x) `(STR::istr-sort ,x))
(add-macro-alias istrsort STR::istr-sort)

(defmacro istrpos (x y) `(STR::istrpos ,x ,y))
(add-macro-alias istrpos STR::istrpos)

(defmacro istrprefixp (x y) `(STR::istrprefixp ,x ,y))
(add-macro-alias istrprefixp STR::istrprefixp)

(defmacro isubstrp (x y) `(STR::isubstrp ,x ,y))
(add-macro-alias isubstrp STR::isubstrp)


(defmacro prefix-lines (x prefix) `(STR::prefix-lines ,x ,prefix))
(add-macro-alias prefix-lines STR::prefix-lines)

(defmacro rpadchars (x len) `(STR::rpadchars ,x ,len))
(add-macro-alias rpadchars STR::rpadchars)

(defmacro rpadstr (x len) `(STR::rpadstr ,x ,len))
(add-macro-alias rpadstr STR::rpadstr)

(defmacro lpadchars (x len) `(STR::lpadchars ,x ,len))
(add-macro-alias lpadchars STR::lpadchars)

(defmacro lpadstr (x len) `(STR::lpadstr ,x ,len))
(add-macro-alias lpadstr STR::lpadstr)


(defmacro strsplit (x del) `(STR::strsplit ,x ,del))
(add-macro-alias strsplit STR::strsplit)

(defmacro strpos (x y) `(STR::strpos ,x ,y))
(add-macro-alias strpos STR::strpos)

(defmacro strrpos (x y) `(STR::strrpos ,x ,y))
(add-macro-alias strrpos STR::strrpos)

(defmacro strsubst (x y z) `(STR::strsubst ,x ,y ,z))
(add-macro-alias strsubst STR::strsubst)

(defmacro strprefixp (x y) `(STR::strprefixp ,x ,y))
(add-macro-alias strprefixp STR::strprefixp)

(defmacro strsuffixp (x y) `(STR::strsuffixp ,x ,y))
(add-macro-alias strsuffixp STR::strsuffixp)

(defmacro substrp (x y) `(STR::substrp ,x ,y))
(add-macro-alias substrp STR::substrp)

(defmacro strnat< (x y) `(STR::strnat< ,x ,y))
(add-macro-alias strnat< STR::strnat<)

(defmacro strtok (x y) `(STR::strtok ,x ,y))
(add-macro-alias strtok STR::strtok)

(defmacro strval (x) `(STR::strval ,x))
(add-macro-alias strval STR::strval)

(defmacro strval8 (x) `(STR::strval8 ,x))
(add-macro-alias strval8 STR::strval8)

(defmacro strval16 (x) `(STR::strval16 ,x))
(add-macro-alias strval16 STR::strval16)
