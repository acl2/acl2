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
(local (include-book "unicode/revappend" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "unicode/rev" :dir :system))
(local (include-book "unicode/coerce" :dir :system))


(local (defthm digit-listp-of-rev
         (implies (digit-listp x)
                  (digit-listp (acl2::rev x)))
         :hints(("Goal" :in-theory (enable acl2::rev)))))


(defund basic-natchars (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons (digit-to-char (mod n 10))
          (basic-natchars (floor n 10)))))

(defthm basic-natchars-when-zp
  (implies (zp n)
           (equal (basic-natchars n)
                  nil))
  :hints(("Goal" :in-theory (enable basic-natchars))))

(defthm true-listp-of-basic-natchars
  (true-listp (basic-natchars n))
  :rule-classes :type-prescription)

(defthm character-listp-of-basic-natchars
  (character-listp (basic-natchars n))
  :hints(("Goal" :in-theory (enable basic-natchars))))

(defthm digit-listp-of-basic-natchars
  (digit-listp (basic-natchars n))
  :hints(("Goal" :in-theory (enable basic-natchars))))

(defthm basic-natchars-under-iff
  (iff (basic-natchars n)
       (not (zp n)))
  :hints(("Goal" :in-theory (enable basic-natchars))))

(defthm consp-of-basic-natchars
  (equal (consp (basic-natchars n))
         (if (basic-natchars n)
             t
           nil))
  :hints(("Goal" :in-theory (enable basic-natchars))))

(encapsulate
 ()
 (local (defun my-induction (n m)
          (if (or (zp n)
                  (zp m))
              nil
            (my-induction (floor n 10) (floor m 10)))))

 (defthm basic-natchars-one-to-one
   (equal (equal (basic-natchars n)
                 (basic-natchars m))
          (equal (nfix n)
                 (nfix m)))
   :hints(("Goal"
           :in-theory (enable basic-natchars)
           :induct (my-induction n m)))))

(local (defthm digit-list-value-of-rev-of-basic-natchars
         (equal (digit-list-value (acl2::rev (basic-natchars n)))
                (nfix n))
         :hints(("Goal"
                 :induct (basic-natchars n)
                 :in-theory (e/d (basic-natchars)
                                 (digit-to-char))))))




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

(defthm natchars-aux-redefinition
  (equal (natchars-aux n acc)
         (revappend (basic-natchars n) acc))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable natchars-aux basic-natchars))))

(verify-guards natchars-aux)



(defund natchars (n)
  (declare (type integer n)
           (xargs :guard (natp n)))
  (or (natchars-aux n nil) '(#\0)))

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

(encapsulate
 ()
 (local (defthm lemma1
          (equal (equal (acl2::rev x) (list y))
                 (and (consp x)
                      (not (consp (cdr x)))
                      (equal (car x) y)))
          :hints(("Goal" :in-theory (enable acl2::rev)))))

 (local (defthmd lemma2
          (not (equal (basic-natchars n) '(#\0)))
          :hints(("Goal" :in-theory (enable basic-natchars)))))

 (defthm natchars-one-to-one
   (equal (equal (natchars n)
                 (natchars m))
          (equal (nfix n) (nfix m)))
   :hints(("Goal"
           :in-theory (e/d (natchars) (basic-natchars-one-to-one))
           :use ((:instance basic-natchars-one-to-one)
                 (:instance lemma2)
                 (:instance lemma2 (n m)))))))

(defthm digit-list-value-of-natchars
  (equal (digit-list-value (natchars n))
         (nfix n))
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

(defthm natstr-one-to-one
  (equal (equal (natstr n) (natstr m))
         (equal (nfix n) (nfix m)))
  :hints(("Goal" :in-theory (enable natstr))))

(defthm digit-list-value-of-natstr
  (equal (digit-list-value (coerce (natstr n) 'list))
         (nfix n))
  :hints(("Goal" :in-theory (enable natstr))))

(defthm natstr-nonempty
  (not (equal (natstr n) ""))
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