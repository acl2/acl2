; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "STR")
(include-book "ieqv")
(include-book "unicode/prefixp" :dir :system)
(local (include-book "arithmetic"))

(defund iprefixp (x y)

  ":Doc-Section Str
  Case-insensitive character-list prefix test~/

  ~c[(iprefixp x y)] determines whether one character list is a prefix of another,
  where each character is tested using ~il[str::ichareqv].~/

  ~l[str::istrprefixp]"

  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))))

  (if (consp x)
      (and (consp y)
           (ichareqv (car x) (car y))
           (iprefixp (cdr x) (cdr y)))
    t))

(defthm iprefixp-when-not-consp-left
  (implies (not (consp x))
           (iprefixp x y))
  :hints(("Goal" :in-theory (enable iprefixp))))

(defthm iprefixp-of-cons-left
  (equal (iprefixp (cons a x) y)
         (and (consp y)
              (ichareqv a (car y))
              (iprefixp x (cdr y))))
  :hints(("Goal" :in-theory (enable iprefixp))))

(defthm iprefixp-when-not-consp-right
  (implies (not (consp y))
           (equal (iprefixp x y)
                  (not (consp x))))
  :hints(("Goal" :induct (len x))))

(defthm iprefixp-of-cons-right
  (equal (iprefixp x (cons a y))
         (if (consp x)
             (and (ichareqv (car x) a)
                  (iprefixp (cdr x) y))
           t)))

(defthm iprefixp-of-list-fix-left
  (equal (iprefixp (list-fix x) y)
         (iprefixp x y))
  :hints(("Goal" :in-theory (enable iprefixp))))

(defthm iprefixp-of-list-fix-right
  (equal (iprefixp x (list-fix y))
         (iprefixp x y))
  :hints(("Goal" :in-theory (enable iprefixp))))

(defcong icharlisteqv equal (iprefixp x y) 1
  :hints(("Goal" :in-theory (enable iprefixp))))

(defcong icharlisteqv equal (iprefixp x y) 2
  :hints(("Goal" :in-theory (enable iprefixp))))

(defthm iprefixp-when-prefixp
  (implies (prefixp x y) (iprefixp x y))
  :hints(("Goal" :in-theory (enable iprefixp))))
