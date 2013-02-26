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
(include-book "tools/bstar" :dir :system)
(local (include-book "std/ks/explode-atom" :dir :system))
(local (include-book "arithmetic"))

(defund insert-underscores (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         x)
        ((equal (mod (len x) 4) 0)
         (list* #\_ (car x) (insert-underscores (cdr x))))
        (t
         (list* (car x) (insert-underscores (cdr x))))))

(local (in-theory (enable insert-underscores)))

(defthm character-listp-of-insert-underscores
  (implies (force (character-listp x))
           (character-listp (insert-underscores x))))

(local (in-theory (disable explode-atom)))

(local (defthm character-listp-of-cdr
         (implies (character-listp x)
                  (character-listp (cdr x)))))

(defun hexify (x)
  ;; Dumb printing utility.  X should be a natural, string, or symbol;
  ;; otherwise we'll just cause an error.
  ;;
  ;; Normally X is a natural.  We turn it into a hexadecimal string that has an
  ;; underscore inserted every four characters, which makes it easier to read
  ;; long hex values.
  ;;
  ;; As a special convenience, if X is a string we just return it unchanged, and
  ;; if X is a symbol we just return its name.
  ;;
  ;; Typical usage is (cw "foo: ~x0~%" (str::hexify foo))
  (declare (xargs :guard t))
  (cond ((natp x)
         (b* ((chars (explode-atom x 16)) ;; looks like BEEF...
              (nice-chars (list* #\# #\u #\x (first chars)
                                 (insert-underscores (nthcdr 1 chars)))))
           (coerce nice-chars 'string)))
        ((symbolp x)
         (symbol-name x))
        ((stringp x)
         x)
        (t
         (prog2$ (er hard? 'hexify "Unexpected argument ~x0.~%" x)
                 ""))))
