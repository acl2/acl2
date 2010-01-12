; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "top")

(defmacro cat (&rest args) `(STR::cat . ,args))

(defmacro append-chars (x y) `(STR::append-chars ,x ,y))
(add-macro-alias append-chars STR::append-chars)

(defmacro append-firstn-chars (n x y) `(STR::append-firstn-chars ,n ,x ,y))
(add-macro-alias append-firstn-chars STR::append-firstn-chars)

(defmacro revappend-chars (x y) `(STR::revappend-chars ,x ,y))
(add-macro-alias revappend-chars STR::revappend-chars)


(defmacro char-fix (x) `(STR::char-fix ,x))
(add-macro-alias char-fix STR::char-fix)

(defmacro chareqv (x y) `(STR::chareqv ,x ,y))
(add-macro-alias chareqv STR::chareqv)

(defmacro charlisteqv (x y) `(STR::charlisteqv ,x ,y))
(add-macro-alias charlisteqv STR::charlisteqv)


(defmacro digitp (x) `(STR::digitp ,x))
(add-macro-alias digitp STR::digitp)

(defmacro digit-val (x) `(STR::digit-val ,x))
(add-macro-alias digit-val STR::digit-val)

(defmacro digit-listp (x) `(STR::digit-listp ,x))
(add-macro-alias digit-listp STR::digit-listp)

(defmacro digit-list-value (x) `(STR::digit-list-value ,x))
(add-macro-alias digit-list-value STR::digit-list-value)

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

(defmacro strprefixp (x y) `(STR::strprefixp ,x ,y))
(add-macro-alias strprefixp STR::strprefixp)

(defmacro substrp (x y) `(STR::substrp ,x ,y))
(add-macro-alias substrp STR::substrp)

(defmacro strnat< (x y) `(STR::strnat< ,x ,y))
(add-macro-alias strnat< STR::strnat<)

