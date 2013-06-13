; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
(include-book "digitp")
(local (include-book "arithmetic"))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defsection basic-natchars
  :parents (natchars)
  :short "Logically simple definition that is mostly similar to @(see natchars)."

  :long "<p>@(call basic-natchars) almost computes @('(natchars n)'), but when
@('n') is zero it returns @('nil') instead of @('(#\\0)').</p>"

  (defund basic-natchars (n)
    (declare (xargs :guard (natp n)))
    (if (zp n)
        nil
      (cons (digit-to-char (mod n 10))
            (basic-natchars (floor n 10)))))

  (local (in-theory (enable basic-natchars)))

  (defthm basic-natchars-when-zp
    (implies (zp n)
             (equal (basic-natchars n)
                    nil)))

  (defthm true-listp-of-basic-natchars
    (true-listp (basic-natchars n))
    :rule-classes :type-prescription)

  (defthm character-listp-of-basic-natchars
    (character-listp (basic-natchars n)))

  (defthm digit-listp-of-basic-natchars
    (digit-listp (basic-natchars n)))

  (defthm basic-natchars-under-iff
    (iff (basic-natchars n)
         (not (zp n))))

  (defthm consp-of-basic-natchars
    (equal (consp (basic-natchars n))
           (if (basic-natchars n)
               t
             nil)))

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
              :induct (my-induction n m))))))



(defsection natchars
  :parents (numbers)
  :short "Convert a natural number into a list of characters."
  :long "<p>For instance, @('(natchars 123)') is @('(#\\1 #\\2 #\\3)').</p>"

  (local (defthm digit-list-value-of-rev-of-basic-natchars
           (equal (digit-list-value (rev (basic-natchars n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-natchars n)
                   :in-theory (e/d (basic-natchars)
                                   (digit-to-char))))))

  (defund natchars-aux (n acc)
    (declare (type integer n)
             (xargs :guard (natp n)
                    :verify-guards nil))
    (if (zp n)
        acc
      (natchars-aux (the integer (truncate (the integer n) 10))
                    (cons (the character (code-char
                                          (the (unsigned-byte 8)
                                            (+ (the (unsigned-byte 8) 48)
                                               (the (unsigned-byte 8)
                                                 (rem (the integer n) 10))))))
                          acc))))

  (definlined natchars (n)
    (declare (type integer n)
             (xargs :guard (natp n)
                    :verify-guards nil))
    (or (natchars-aux n nil) '(#\0)))

  (defthm natchars-aux-redefinition
    (equal (natchars-aux n acc)
           (revappend (basic-natchars n) acc))
    :rule-classes :definition
    :hints(("Goal" :in-theory (enable natchars-aux basic-natchars))))

  (verify-guards natchars-aux)
  (verify-guards natchars$inline)

  (local (in-theory (enable natchars)))

  (defthm true-listp-of-natchars
    (true-listp (natchars n))
    :rule-classes :type-prescription)

  (defthm character-listp-of-natchars
    (character-listp (natchars n)))

  (defthm digit-listp-of-natchars
    (digit-listp (natchars n)))

  (encapsulate
    ()
    (local (defthm lemma1
             (equal (equal (rev x) (list y))
                    (and (consp x)
                         (not (consp (cdr x)))
                         (equal (car x) y)))
             :hints(("Goal" :in-theory (enable rev)))))

    (local (defthmd lemma2
             (not (equal (basic-natchars n) '(#\0)))
             :hints(("Goal" :in-theory (enable basic-natchars)))))

    (defthm natchars-one-to-one
      (equal (equal (natchars n)
                    (natchars m))
             (equal (nfix n) (nfix m)))
      :hints(("Goal"
              :in-theory (disable basic-natchars-one-to-one)
              :use ((:instance basic-natchars-one-to-one)
                    (:instance lemma2)
                    (:instance lemma2 (n m)))))))

  (defthm digit-list-value-of-natchars
    (equal (digit-list-value (natchars n))
           (nfix n))))



(defsection natstr
  :parents (numbers)
  :short "Convert a natural number into a string."
  :long "<p>For instance, @('(natstr 123)') is @('\"123\"').</p>"

  (definlined natstr (n)
    (declare (type integer n)
             (xargs :guard (natp n)))
    (implode (natchars n)))

  (local (in-theory (enable natstr)))

  (defthm stringp-of-natstr
    (stringp (natstr n))
    :rule-classes :type-prescription)

  (defthm digit-listp-of-natstr
    (digit-listp (explode (natstr n))))

  (defthm natstr-one-to-one
    (equal (equal (natstr n) (natstr m))
           (equal (nfix n) (nfix m))))

  (defthm digit-list-value-of-natstr
    (equal (digit-list-value (explode (natstr n)))
           (nfix n)))

  (defthm natstr-nonempty
    (not (equal (natstr n) ""))))



(defsection natstr-list
  :parents (numbers)
  :short "Convert a list of natural numbers into a list of strings."

  (defund natstr-list (x)
    (declare (xargs :guard (nat-listp x)))
    (if (atom x)
        nil
      (cons (natstr (car x))
            (natstr-list (cdr x)))))

  (local (in-theory (enable natstr-list)))

  (defthm natstr-list-when-atom
    (implies (atom x)
             (equal (natstr-list x)
                    nil)))

  (defthm natstr-list-of-cons
    (equal (natstr-list (cons a x))
           (cons (natstr a)
                 (natstr-list x))))

  (defthm string-listp-of-natstr-list
    (string-listp (natstr-list x))))



(defsection revappend-natchars
  :parents (numbers)
  :short "More efficient version of @('(revappend (natchars n) acc).')"

  :long "<p>This can be useful when building strings by consing together
characters in reverse order.</p>"

  (defund revappend-natchars-aux (n acc)
    (declare (type integer n)
             (xargs :guard (and (natp n))))
    (if (zp n)
        acc
      (cons (the character (code-char
                            (the (unsigned-byte 8)
                              (+ (the (unsigned-byte 8) 48)
                                 (the (unsigned-byte 8)
                                   (rem (the integer n) 10))))))
            (revappend-natchars-aux
             (the integer (truncate (the integer n) 10))
             acc))))

  (defthm revappend-natchars-aux-redef
    (equal (revappend-natchars-aux n acc)
           (append (basic-natchars n) acc))
    :hints(("Goal" :in-theory (enable revappend-natchars-aux basic-natchars))))

  (definline revappend-natchars (n acc)
    (declare (type integer n)
             (xargs :guard (natp n)
                    :guard-hints(("Goal" :in-theory (enable natchars)))))
    (mbe :logic (revappend (natchars n) acc)
         :exec (if (zp n)
                   (cons #\0 acc)
                 (revappend-natchars-aux n acc)))))


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
