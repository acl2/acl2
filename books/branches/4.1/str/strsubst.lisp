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
(include-book "cat")
(include-book "strprefixp")
(local (include-book "arithmetic"))

(defund strsubst-aux (old new x n xl oldl acc)
  (declare (type string old)
           (type string new)
           (type string x)
           (type integer n)
           (type integer xl)
           (type integer oldl)
           (xargs :guard (and (stringp old)
                              (stringp new)
                              (stringp x)
                              (natp n)
                              (natp xl)
                              (posp oldl)
                              (= oldl (length old))
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (cond ((mbe :logic (zp oldl)
              :exec nil)
         acc)

        ((mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (>= n xl))
         acc)

        ((strprefixp-impl old x 0 n oldl xl)
         (let ((acc (revappend-chars new acc)))
           (strsubst-aux old new x
                           (mbe :logic (+ oldl (nfix n))
                                :exec (+ oldl n))
                           xl oldl acc)))

        (t
         (let ((acc (cons (char x n) acc)))
           (strsubst-aux old new x
                           (mbe :logic (+ 1 (nfix n))
                                :exec (+ 1 n))
                           xl oldl acc)))))

(defthm character-listp-of-strsubst-aux
  (implies (and (stringp old)
                (stringp new)
                (stringp x)
                (natp n)
                (natp xl)
                (posp oldl)
                (= oldl (length old))
                (= xl (length x))
                (character-listp acc))
           (character-listp (strsubst-aux old new x n xl oldl acc)))
  :hints(("Goal" :in-theory (enable strsubst-aux))))

(defund strsubst (old new x)

  ":Doc-Section Str
Repalce substrings throughout a string~/

~c[(strsubst old new x)] replaces each occurrence of ~c[old] with ~c[new]
throughout ~c[x].  Each argument is a string.  A string is returned.  The
replacement is done globally and non-recursively.

Examples:
~bv[]
 (strsubst \"World\" \"Star\" \"Hello, World!\") --> \"Hello, Star!\"

 (strsubst \"oo\" \"aa\" \"xoooyoo\") --> \"xaaoyaa\"
~ev[]~/~/"

  (declare (xargs :guard (and (stringp old)
                              (stringp new)
                              (stringp x))))
  (let ((xl   (length x))
        (oldl (length old)))
    (if (= oldl 0)
        (mbe :logic (if (stringp x)
                        x
                      "")
             :exec x)
      (reverse (coerce (strsubst-aux old new x 0 xl oldl nil) 'string)))))

(defthm stringp-of-strsubst
  (stringp (strsubst old new x))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strsubst))))


(local
 (encapsulate
   ()

   (defthm test1 (equal (strsubst "World" "Star" "Hello, World!")
                        "Hello, Star!"))

   (defthm test2 (equal (strsubst "oo" "aa" "xoooyoo")
                        "xaaoyaa"))))



