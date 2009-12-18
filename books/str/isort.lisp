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

(in-package "STR")
(include-book "iless")
(include-book "defsort/defsort" :dir :system)
(include-book "unicode/list-fix" :dir :system)

(ACL2::defsort
 :comparablep stringp
 :compare< istr<
 :prefix istr)

(defthm istr-list-p-removal
  (equal (istr-list-p x)
         (string-listp (list-fix x)))
  :hints(("Goal" :in-theory (enable istr-list-p))))

(defthm string-listp-of-list-fix
  (implies (string-listp x)
           (string-listp (list-fix x))))

(defthm string-listp-of-istr-sort
  (implies (force (string-listp x))
           (string-listp (istr-sort x)))
  :hints(("Goal"
          :in-theory (disable istr-sort-creates-comparable-listp)
          :use ((:instance istr-sort-creates-comparable-listp)))))

(defmacro istrsort (x)

  ":Doc-Section Str
  Case-insensitively sort a string list~/

  This is an efficient, stable mergesort for string lists based on ~il[istr<]
  and implemented with the \"defsort/defsort\" book.~/

  ~l[istr<]"

  `(istr-sort ,x))

(add-macro-alias istrsort istr-sort)