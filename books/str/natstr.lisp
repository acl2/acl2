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
(include-book "doc")
(include-book "digitp")
(local (include-book "char-support"))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defund natchars-aux (n acc)
  (declare (type integer n)
           (xargs :guard (and (natp n)
                              (character-listp acc))
                  :verify-guards nil))
  (if (mbe :logic (zp n)
           :exec (= (the integer n) 0))
      acc
    (natchars-aux (the integer (truncate (the integer n) 10))
                  (cons (the character (code-char
                                        (the (unsigned-byte 8)
                                          (+ (the (unsigned-byte 8) 48)
                                             (the (unsigned-byte 8)
                                               (rem (the integer n) 10))))))
                        acc))))

(defthm true-listp-of-natchars-aux
  (implies (true-listp acc)
           (true-listp (natchars-aux n acc)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable natchars-aux))))

(defthm character-listp-of-natchars-aux
  (implies (character-listp acc)
           (character-listp (natchars-aux n acc)))
  :hints(("Goal" :in-theory (enable natchars-aux))))

(verify-guards natchars-aux)

(defthm digit-listp-of-natchars-aux
  (implies (digit-listp acc)
           (digit-listp (natchars-aux n acc)))
  :hints(("Goal" :in-theory (enable natchars-aux digitp))))



(defund natchars (n)
  (declare (type integer n)
           (xargs :guard (natp n)))
  (or (natchars-aux (mbe :logic (nfix n)
                         :exec (the integer n))
                    nil)
      '(#\0)))

(defthm true-listp-of-natchars
  (true-listp (natchars n))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable natchars))))

(defthm character-listp-of-natchars
  (character-listp (natchars n))
  :hints(("Goal" :in-theory (enable natchars))))

(defthm digit-listp-of-natchars
  (digit-listp (natchars n))
  :hints(("Goal" :in-theory (enable natchars))))



(defund natstr (n)
  (declare (type integer n)
           (xargs :guard (natp n)))
  (coerce (natchars n) 'string))

(defthm stringp-of-natstr
  (stringp (natstr n))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable natstr))))

(defthm digit-listp-of-natstr
  (digit-listp (coerce (natstr n) 'list))
  :hints(("Goal" :in-theory (enable natstr))))


#|

;; Use a machine with lots of memory, or lower the indices below.  Ideally the
;; test should not do any garbage collection.

(ccl::set-lisp-heap-gc-threshold (expt 2 33))

;; 8.5 seconds, 1.1 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 10000000
                   do (explode-nonnegative-integer i 10 nil))))

;; 5.8 seconds, 1.1 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 10000000
                   do (STR::natchars-aux i nil))))

;; 5.9 seconds, 1.1 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 10000000
                   do (STR::natchars i))))

;; Was 44 seconds.  Now 6.1 seconds with CCL patch.  1.5 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 10000000
                   do (STR::natstr i))))

|#