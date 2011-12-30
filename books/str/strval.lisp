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
(include-book "strnatless")
(local (include-book "arithmetic"))
(local (include-book "misc/assert" :dir :system))


;; BOZO maybe use cutil::deflist for these list recognizers

(defsection octal-digitp
  :parents (numbers)
  :short "Recognizer for characters #\0 through #\7."
  :long "<p>@(call octal-digitp) is the octal alternative to @(see digitp).</p>"

  (defund octal-digitp (x)
    (declare (type character x))
    (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
      (and (<= (char-code #\0) code)
           (<= code (char-code #\7)))))

  (defthm digitp-when-octal-digitp
    (implies (octal-digitp x)
             (digitp x))
    :hints(("Goal" :in-theory (enable octal-digitp digitp)))))

(defsection octal-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see octal-digitp) characters."

  (defund octal-digit-listp (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        t
      (and (octal-digitp (car x))
           (octal-digit-listp (cdr x)))))

  (defthm digit-listp-when-octal-digit-listp
    (implies (octal-digit-listp x)
             (digit-listp x))
    :hints(("Goal" :in-theory (enable digit-listp octal-digit-listp)))))

(defsection parse-octal-from-charlist
  :parents (numbers)
  :short "Parse an octal number from the beginning of a character list."
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with octal
digits and returns their octal value.</p>"

  (defund parse-octal-from-charlist (x val len)
    (declare (type integer val)
             (type integer len)
             (xargs :guard (and (character-listp x)
                                (natp val)
                                (natp len))))
    (cond ((atom x)
           (mv (mbe :logic (nfix val) :exec val)
               (mbe :logic (nfix len) :exec len)
               nil))
          ((octal-digitp (car x))
           (let ((digit-val (digit-val (car x))))
             (parse-octal-from-charlist (cdr x)
                                        (+ digit-val (* 8 (mbe :logic (nfix val) :exec val)))
                                        (+ 1 (mbe :logic (nfix len) :exec len)))))
          (t
           (mv (mbe :logic (nfix val) :exec val)
               (mbe :logic (nfix len) :exec len)
               x))))

  (defthm natp-of-parse-octal-from-charlist
    (implies (natp val)
             (natp (mv-nth 0 (parse-octal-from-charlist x val len))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable parse-octal-from-charlist)))))

(defsection octal-digit-list-value
  :parents (numbers)
  :short "Coerces a list of octal digits into a natural number."
  :long "<p>@(call octal-digit-list-value) is like @(see digit-list-value) but
for octal numbers.</p>

<p>See also @(see parse-octal-from-charlist) for a more flexible function that
can tolerate non-octal digits after the number.</p>"

  (defund octal-digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (octal-digit-listp x))))
    (b* (((mv val ?len ?rest)
          (parse-octal-from-charlist x 0 0)))
      val))

  (defthm natp-of-octal-digit-list-value
    (natp (octal-digit-list-value x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable octal-digit-list-value))))

  (local (assert! (and (equal (octal-digit-list-value (coerce "0" 'list)) #o0)
                       (equal (octal-digit-list-value (coerce "6" 'list)) #o6)
                       (equal (octal-digit-list-value (coerce "12" 'list)) #o12)
                       (equal (octal-digit-list-value (coerce "1234" 'list)) #o1234)))))




(defsection hex-digitp
  :parents (numbers)
  :short "Recognizer for characters 0-9, A-F, and a-f."
  :long "<p>@(call hex-digitp) is the hexadecimal alternative to @(see digitp).</p>"

  (defund hex-digitp (x)
    (declare (type character x))
    (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
      (or (and (<= (char-code #\0) code)
               (<= code (char-code #\9)))
          (and (<= (char-code #\a) code)
               (<= code (char-code #\f)))
          (and (<= (char-code #\A) code)
               (<= code (char-code #\F)))))))

(defsection hex-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see hex-digitp) characters."

  (defund hex-digit-listp (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        t
      (and (hex-digitp (car x))
           (hex-digit-listp (cdr x))))))

(defsection hex-digit-val
  :parents (numbers)
  :short "Coerces a @(see hex-digitp) character into an integer."
  :long "<p>@(call hex-digit-val) is the hexadecimal version of @(see
digit-val).</p>"

  (defund hex-digit-val (x)
    (declare (xargs :guard (and (characterp x)
                                (hex-digitp x))))
    (if (mbe :logic (not (hex-digitp x))
             :exec nil)
        0
      (let ((code (char-code (mbe :logic (char-fix x)
                                  :exec x))))
        (cond ((<= (char-code #\a) code) (- code (- (char-code #\a) 10)))
              ((<= (char-code #\A) code) (- code (- (char-code #\A) 10)))
              (t                         (- code (char-code #\0)))))))

  (defthm natp-of-hex-digit-val
    (natp (hex-digit-val x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable hex-digitp hex-digit-val))))

  (local (assert! (and (equal (hex-digit-val #\A) #xA)
                       (equal (hex-digit-val #\B) #xB)
                       (equal (hex-digit-val #\C) #xC)
                       (equal (hex-digit-val #\D) #xD)
                       (equal (hex-digit-val #\E) #xE)
                       (equal (hex-digit-val #\F) #xF)
                       (equal (hex-digit-val #\a) #xa)
                       (equal (hex-digit-val #\b) #xb)
                       (equal (hex-digit-val #\c) #xc)
                       (equal (hex-digit-val #\d) #xd)
                       (equal (hex-digit-val #\e) #xe)
                       (equal (hex-digit-val #\f) #xf)
                       (equal (hex-digit-val #\0) #x0)
                       (equal (hex-digit-val #\1) #x1)
                       (equal (hex-digit-val #\2) #x2)
                       (equal (hex-digit-val #\3) #x3)
                       (equal (hex-digit-val #\4) #x4)
                       (equal (hex-digit-val #\5) #x5)
                       (equal (hex-digit-val #\6) #x6)
                       (equal (hex-digit-val #\7) #x7)
                       (equal (hex-digit-val #\8) #x8)
                       (equal (hex-digit-val #\9) #x9)))))

(defsection parse-hex-from-charlist
  :parents (numbers)
  :short "Parse a hexadecimal number from the beginning of a character list."
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with
hex digits and returns their hexadecimal value.</p>"

  (defund parse-hex-from-charlist (x val len)
    (declare (type integer val)
             (type integer len)
             (xargs :guard (and (character-listp x)
                                (natp val)
                                (natp len))))
    (cond ((atom x)
           (mv (mbe :logic (nfix val) :exec val)
               (mbe :logic (nfix len) :exec len)
               nil))
          ((hex-digitp (car x))
           (let ((digit-val (hex-digit-val (car x))))
             (parse-hex-from-charlist (cdr x)
                                      (+ digit-val (* 16 (mbe :logic (nfix val) :exec val)))
                                      (+ 1 (mbe :logic (nfix len) :exec len)))))
          (t
           (mv (mbe :logic (nfix val) :exec val)
               (mbe :logic (nfix len) :exec len)
               x))))

  (defthm natp-of-parse-hex-from-charlist
    (implies (natp val)
             (natp (mv-nth 0 (parse-hex-from-charlist x val len))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable parse-hex-from-charlist)))))

(defsection hex-digit-list-value
  :parents (numbers)
  :short "Coerces a list of hex digits into a natural number."
  :long "<p>@(call hex-digit-list-value) is like @(see digit-list-value) but
for hex numbers.</p>

<p>See also @(see parse-hex-from-charlist) for a more flexible function that
can tolerate non-hex digits after the number.</p>"

  (defund hex-digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (hex-digit-listp x))))
    (b* (((mv val ?len ?rest)
          (parse-hex-from-charlist x 0 0)))
      val))

  (defthm natp-of-hex-digit-list-value
    (natp (hex-digit-list-value x))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable hex-digit-list-value))))

  (local (assert! (and (equal (hex-digit-list-value (coerce "0" 'list)) #x0)
                       (equal (hex-digit-list-value (coerce "6" 'list)) #x6)
                       (equal (hex-digit-list-value (coerce "12" 'list)) #x12)
                       (equal (hex-digit-list-value (coerce "1234" 'list)) #x1234)))))


(defsection bit-digitp
  :parents (numbers)
  :short "Recognizer for characters #\0 and #\1."
  :long "<p>@(call bit-digitp) is the binary alternative to @(see digitp).</p>"

  (defund bit-digitp (x)
    (declare (xargs :guard t))
    (or (eql x #\0)
        (eql x #\1))))

(defsection bit-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see bit-digitp) characters."

  (defund bit-digit-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (bit-digitp (car x))
           (bit-digit-listp (cdr x))))))

(defsection bitstring-p
  :parents (numbers)
  :short "Recognizes strings with only @(see bit-digitp) characters."

  (defund bitstring-p (x)
    (declare (xargs :guard t))
    ;; BOZO make a faster version of this
    (and (stringp x)
         (bit-digit-listp (coerce x 'list)))))




; BOZO we could do some work to make these nicer, i.e., we should have fast
; versions of strval8, etc., and ordinary strval should have a nicer logical
; definition.

(defsection strval
  :parents (numbers)
  :short "Interpret a string as a decimal number."
  :long "<p>@(call strval) tries to interpret a string as a base-10 natural
number.  For example, <tt>(strval \"35\")</tt> is 35.  If the string has any
non-decimal digit characters, we return <tt>nil</tt>.</p>"

  (defund strval (x)
    (declare (type string x))
    (b* ((xl (length x))
         ((mv val len)
          (str::parse-nat-from-string x 0 0 0 xl)))
      (and (= len xl)
           val)))

  (defthm type-of-strval
    (or (natp (strval x))
        (not (strval x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable strval)))))

(defsection strval8
  :parents (numbers)
  :short "Interpret a string as an octal number."
  :long "<p>@(call strval8) is like @(see strval) but for octal instead of
decimal numbers.  For example, <tt>(strval8 \"10\")</tt> is 8.  If the string
has any non-octal digit characters, we return <tt>nil</tt>.</p>"

  (defund strval8 (x)
    (declare (type string x))
    (let ((chars (coerce x 'list)))
      (and (octal-digit-listp chars)
           (octal-digit-list-value chars))))

  (defthm type-of-strval8
    (or (natp (strval8 x))
        (not (strval8 x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable strval8)))))

(defsection strval16
  :parents (numbers)
  :short "Interpret a string as a hexadecimal number."
  :long "<p>@(call strval16) is like @(see strval) but for hexadecimal instead
of decimal numbers.  For example, <tt>(strval16 \"10\")</tt> is 16.  If the
string has any non-hex digit characters, we return <tt>nil</tt>.</p>"

  (defund strval16 (x)
    (declare (type string x))
    (let ((chars (coerce x 'list)))
      (and (hex-digit-listp chars)
           (hex-digit-list-value chars))))

  (defthm type-of-strval16
    (or (natp (strval16 x))
        (not (strval16 x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable strval16)))))


