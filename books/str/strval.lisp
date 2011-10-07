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
(local (include-book "char-support"))
(local (include-book "make-event/assert" :dir :system))



(defund octal-digitp (x)

  ":Doc-Section Str
  Recognizer for characters #\0 through #\7.~/

  See ~ilc[digitp].  This is just the octal version.~/~/"

  (declare (type character x))
  (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
    (and (<= (char-code #\0) code)
         (<= code (char-code #\7)))))


(defund octal-digit-listp (x)

  ":Doc-Section Str
  Recognizes lists of ~il[str::octal-digitp] characters.~/~/~/"

  (declare (xargs :guard (character-listp x)))
  (if (atom x)
      t
    (and (octal-digitp (car x))
         (octal-digit-listp (cdr x)))))

(defthm digitp-when-octal-digitp
  (implies (octal-digitp x)
           (digitp x))
  :hints(("Goal" :in-theory (enable octal-digitp digitp))))

(defthm digit-listp-when-octal-digit-listp
  (implies (octal-digit-listp x)
           (digit-listp x))
  :hints(("Goal" :in-theory (enable digit-listp octal-digit-listp))))




(defund parse-octal-from-charlist (x val len)

  ":Doc-Section Str
  Parse an octal number from the beginning of a character list.~/

  This is like ~ilc[str::parse-nat-from-charlist], but deals with octal digits
  and returns their octal value.~/~/"

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
  :hints(("Goal" :in-theory (enable parse-octal-from-charlist))))



(defund octal-digit-list-value (x)

  ":Doc-Section Str
  Coerces a list of octal digits into a natural number.~/

  This is like ~ilc[str::digit-list-value] but for octal numbers.  See also
  ~ilc[str::parse-octal-from-charlist] for a more flexible function that can
  tolerate non-octal digits after the number.~/~/"

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
                     (equal (octal-digit-list-value (coerce "1234" 'list)) #o1234))))





(defund hex-digitp (x)

  ":Doc-Section Str
  Recognizer for [0-9], [A-F], and [a-f].~/

  See ~ilc[digitp].  This is just the hexadecimal version.~/~/"

  (declare (type character x))
  (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
    (or (and (<= (char-code #\0) code)
             (<= code (char-code #\9)))
        (and (<= (char-code #\a) code)
             (<= code (char-code #\f)))
        (and (<= (char-code #\A) code)
             (<= code (char-code #\F))))))

(defund hex-digit-listp (x)

  ":Doc-Section Str
  Recognizes lists of ~il[str::hex-digitp] characters.~/~/~/"

  (declare (xargs :guard (character-listp x)))
  (if (atom x)
      t
    (and (hex-digitp (car x))
         (hex-digit-listp (cdr x)))))

(defund hex-digit-val (x)

  ":Doc-Section Str
  Coerces a ~il[str::hex-digitp] character into an integer. ~/

  This is like ~ilc[str::digit-val] but for ilc[str::hex-digitp]'s.~/~/"

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
                     (equal (hex-digit-val #\9) #x9))))

(defund parse-hex-from-charlist (x val len)

  ":Doc-Section Str
  Parse a hexadecimal number from the beginning of a character list.~/

  This is like ~ilc[str::parse-nat-from-charlist], but deals with hex digits
  and returns their hexadecimal value.~/~/"

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
  :hints(("Goal" :in-theory (enable parse-hex-from-charlist))))

(defund hex-digit-list-value (x)

  ":Doc-Section Str
  Coerces a list of hexadecimal digits into a natural number.~/

  This is like ~ilc[str::digit-list-value] but for hexadecimal numbers.  See also
  ~ilc[str::parse-hex-from-charlist] for a more flexible function that can
  tolerate non-hexadecimal digits after the number.~/~/"

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
                     (equal (hex-digit-list-value (coerce "1234" 'list)) #x1234))))




(defund bit-digitp (x)

  ":Doc-Section Str
  Recognizer for characters #\0 and #\1.~/

  See ~ilc[digitp].  This is just the binary version.~/~/"

  (declare (xargs :guard t))
  (or (eql x #\0)
      (eql x #\1)))

(defund bit-digit-listp (x)

  ":Doc-Section Str
  Recognizes lists of ~il[str::bit-digitp] characters.~/~/~/"

  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (bit-digitp (car x))
         (bit-digit-listp (cdr x)))))

(defund bitstring-p (x)

  ":Doc-Section Str
  Recognizes strings with only ~il[str::bit-digitp] characters.~/~/~/"

  (declare (xargs :guard t))
  ;; BOZO make a faster version of this
  (and (stringp x)
       (bit-digit-listp (coerce x 'list))))




; BOZO we could do some work to make these nicer, i.e., we should have fast
; versions of strval8, etc., and ordinary strval should have a nicer logical
; definition.

(defund strval (x)

  ":Doc-Section Str
  ~c[(strval x)] coerces a string of decimal digits into its value.~/

  For example, ~c[(strval \"35\")] is 35.  If the string doesn't contain
  only decimal digit characters, we return NIL.~/~/"

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
  :hints(("Goal" :in-theory (enable strval))))


(defund strval8 (x)

  ":Doc-Section Str
  ~c[(strval8 x)] coerces a string of octal digits into its value.~/

  This is like ~ilc[str::strval] but for octal digits.  For example,
  ~c[(strval8 \"10\")] is 8.  We return NIL if the string contains
  any non-octal digits.~/~/"

  (declare (type string x))
  (let ((chars (coerce x 'list)))
    (and (octal-digit-listp chars)
         (octal-digit-list-value chars))))

(defthm type-of-strval8
  (or (natp (strval8 x))
      (not (strval8 x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strval8))))


(defund strval16 (x)

  ":Doc-Section Str
  ~c[(strval16 x)] coerces a string of hex digits into its value.~/

  This is like ~ilc[str::strval] but for hex digits.  For example,
  ~c[(strval16 \"10\")] is 16.  We return NIL if the string contains
  any non-octal digits.~/~/"

  (declare (type string x))
  (let ((chars (coerce x 'list)))
    (and (hex-digit-listp chars)
         (hex-digit-list-value chars))))

(defthm type-of-strval16
  (or (natp (strval16 x))
      (not (strval16 x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strval16))))


