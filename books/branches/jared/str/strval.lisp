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
(include-book "strnatless")
(local (include-book "arithmetic"))
(local (include-book "misc/assert" :dir :system))


;; BOZO maybe use cutil::deflist for these list recognizers

(defsection octal-digitp
  :parents (numbers)
  :short "Recognizer for characters #\\0 through #\\7."
  :long "<p>@(call octal-digitp) is the octal alternative to @(see digitp).</p>"

  (definlined octal-digitp (x)
    (declare (type character x))
    (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
      (declare (type (unsigned-byte 8) code))
      (and (<= (char-code #\0) code)
           (<= code (char-code #\7)))))

  (local (in-theory (enable octal-digitp)))

  (defcong ichareqv equal (octal-digitp x) 1
    :hints(("Goal" :in-theory (enable octal-digitp
                                      ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm digitp-when-octal-digitp
    (implies (octal-digitp x)
             (digitp x))
    :hints(("Goal" :in-theory (enable digitp)))))


(defsection octal-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see octal-digitp) characters."

  (defund octal-digit-listp (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        t
      (and (octal-digitp (car x))
           (octal-digit-listp (cdr x)))))

  (local (in-theory (enable octal-digit-listp)))

  (defthm digit-listp-when-octal-digit-listp
    (implies (octal-digit-listp x)
             (digit-listp x))
    :hints(("Goal" :in-theory (enable digit-listp))))

  (defcong icharlisteqv equal (octal-digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv)))))



(defsection parse-octal-from-charlist
  :parents (numbers)
  :short "Parse an octal number from the beginning of a character list."
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with octal
digits and returns their octal value.</p>"

  (defund parse-octal-from-charlist (x val len)
    (declare (type (integer 0 *) val len)
             (xargs :guard (and (character-listp x)
                                (natp val)
                                (natp len))))
    (cond ((atom x)
           (mv (lnfix val) (lnfix len) nil))
          ((octal-digitp (car x))
           (let ((digit-val (digit-val (car x))))
             (parse-octal-from-charlist (cdr x)
                                        (+ digit-val (* 8 (lnfix val)))
                                        (+ 1 (lnfix len)))))
          (t
           (mv (lnfix val) (lnfix len) x))))

  (local (in-theory (enable parse-octal-from-charlist)))

  (defthm natp-of-parse-octal-from-charlist
    (implies (natp val)
             (natp (mv-nth 0 (parse-octal-from-charlist x val len))))
    :rule-classes :type-prescription))


(defsection octal-digit-list-value
  :parents (numbers)
  :short "Coerces a list of octal digits into a natural number."
  :long "<p>@(call octal-digit-list-value) is like @(see digit-list-value) but
for octal numbers.</p>

<p>See also @(see parse-octal-from-charlist) for a more flexible function that
can tolerate non-octal digits after the number.</p>"

  (definlined octal-digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (octal-digit-listp x))))
    (b* (((mv val ?len ?rest)
          (parse-octal-from-charlist x 0 0)))
      val))

  (local (in-theory (enable octal-digit-list-value)))

  (defthm natp-of-octal-digit-list-value
    (natp (octal-digit-list-value x))
    :rule-classes :type-prescription)

  (local (defthmd l0
           (implies (icharlisteqv x x-equiv)
                    (equal (mv-nth 0 (parse-octal-from-charlist x val len))
                           (mv-nth 0 (parse-octal-from-charlist x-equiv val len))))
           :hints(("Goal" :in-theory (enable parse-octal-from-charlist
                                             icharlisteqv)))))

  (defcong icharlisteqv equal (octal-digit-list-value x) 1
    :hints(("Goal" :use ((:instance l0 (val 0) (len 0))))))

  (local (assert! (and (equal (octal-digit-list-value (coerce "0" 'list)) #o0)
                       (equal (octal-digit-list-value (coerce "6" 'list)) #o6)
                       (equal (octal-digit-list-value (coerce "12" 'list)) #o12)
                       (equal (octal-digit-list-value (coerce "1234" 'list)) #o1234)))))




(defsection hex-digitp
  :parents (numbers)
  :short "Recognizer for characters 0-9, A-F, and a-f."
  :long "<p>@(call hex-digitp) is the hexadecimal alternative to @(see digitp).</p>"

  (definlined hex-digitp (x)
    (declare (type character x))
    (let ((code (char-code (mbe :logic (char-fix x) :exec x))))
      (declare (type (unsigned-byte 8) code))
      (or (and (<= (char-code #\0) code)
               (<= code (char-code #\9)))
          (and (<= (char-code #\a) code)
               (<= code (char-code #\f)))
          (and (<= (char-code #\A) code)
               (<= code (char-code #\F))))))

  (local (in-theory (enable hex-digitp)))

  (defcong ichareqv equal (hex-digitp x) 1
    :hints(("Goal" :in-theory (enable hex-digitp
                                      ichareqv
                                      downcase-char
                                      char-fix)))))


(defsection hex-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see hex-digitp) characters."

  (defund hex-digit-listp (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        t
      (and (hex-digitp (car x))
           (hex-digit-listp (cdr x)))))

  (local (in-theory (enable hex-digit-listp)))

  (defcong icharlisteqv equal (hex-digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv)))))


(defsection hex-digit-val
  :parents (numbers)
  :short "Coerces a @(see hex-digitp) character into an integer."
  :long "<p>@(call hex-digit-val) is the hexadecimal version of @(see
digit-val).</p>"

  (definlined hex-digit-val (x)
    (declare (xargs :guard (and (characterp x)
                                (hex-digitp x))))
    (if (mbe :logic (not (hex-digitp x))
             :exec nil)
        0
      (let ((code (char-code (mbe :logic (char-fix x)
                                  :exec x))))
        (declare (type (unsigned-byte 8) code))
        (cond ((<= (char-code #\a) code) (- code (- (char-code #\a) 10)))
              ((<= (char-code #\A) code) (- code (- (char-code #\A) 10)))
              (t                         (- code (char-code #\0)))))))

  (local (in-theory (enable hex-digit-val hex-digitp)))

  (defthm natp-of-hex-digit-val
    (natp (hex-digit-val x))
    :rule-classes :type-prescription)

  (defcong ichareqv equal (hex-digit-val x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))

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
    (declare (type (integer 0 *) val len)
             (xargs :guard (and (character-listp x)
                                (natp val)
                                (natp len))))
    (cond ((atom x)
           (mv (lnfix val) (lnfix len) nil))
          ((hex-digitp (car x))
           (let ((digit-val (hex-digit-val (car x))))
             (parse-hex-from-charlist
              (cdr x)
              (the (integer 0 *) (+ (the (integer 0 *) digit-val)
                                    (the (integer 0 *)
                                      (* 16 (the (integer 0 *) (lnfix val))))))
              (the (integer 0 *) (+ 1 (the (integer 0 *) (lnfix len)))))))
          (t
           (mv (lnfix val) (lnfix len) x))))

  (local (in-theory (enable parse-hex-from-charlist)))

  (defthm natp-of-parse-hex-from-charlist
    (implies (natp val)
             (natp (mv-nth 0 (parse-hex-from-charlist x val len))))
    :rule-classes :type-prescription))


(defsection hex-digit-list-value
  :parents (numbers)
  :short "Coerces a list of hex digits into a natural number."
  :long "<p>@(call hex-digit-list-value) is like @(see digit-list-value) but
for hex numbers.</p>

<p>See also @(see parse-hex-from-charlist) for a more flexible function that
can tolerate non-hex digits after the number.</p>"

  (definlined hex-digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (hex-digit-listp x))))
    (b* (((mv val ?len ?rest)
          (parse-hex-from-charlist x 0 0)))
      val))

  (local (in-theory (enable hex-digit-list-value)))

  (defthm natp-of-hex-digit-list-value
    (natp (hex-digit-list-value x))
    :rule-classes :type-prescription)

  (local (defthmd l0
           (implies (icharlisteqv x x-equiv)
                    (equal (mv-nth 0 (parse-hex-from-charlist x val len))
                           (mv-nth 0 (parse-hex-from-charlist x-equiv val len))))
           :hints(("Goal" :in-theory (enable parse-hex-from-charlist
                                             icharlisteqv)))))

  (defcong icharlisteqv equal (hex-digit-list-value x) 1
    :hints(("Goal" :use ((:instance l0 (val 0) (len 0))))))

  (local (assert! (and (equal (hex-digit-list-value (coerce "0" 'list)) #x0)
                       (equal (hex-digit-list-value (coerce "6" 'list)) #x6)
                       (equal (hex-digit-list-value (coerce "12" 'list)) #x12)
                       (equal (hex-digit-list-value (coerce "1234" 'list)) #x1234)))))


(defsection bit-digitp
  :parents (numbers)
  :short "Recognizer for characters #\\0 and #\\1."
  :long "<p>@(call bit-digitp) is the binary alternative to @(see digitp).</p>"

  (definlined bit-digitp (x)
    (declare (xargs :guard t))
    (or (eql x #\0)
        (eql x #\1)))

  (local (in-theory (enable bit-digitp)))

  (defcong ichareqv equal (bit-digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix)))))


(defsection bit-digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see bit-digitp) characters."

  (defund bit-digit-listp (x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (bit-digitp (car x))
           (bit-digit-listp (cdr x)))))

  (local (in-theory (enable bit-digit-listp)))

  (defcong icharlisteqv equal (bit-digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv)))))



(defsection bitstring-p
  :parents (numbers)
  :short "Recognizes strings with only @(see bit-digitp) characters."

  (defund bitstring-p (x)
    (declare (xargs :guard t))
    ;; BOZO make a faster version of this
    ;; BOZO requiring stringp is bad for congruences
    (and (stringp x)
         (bit-digit-listp (explode x))))

  (local (in-theory (enable bitstring-p))))


(defsection parse-bits-from-charlist
  :parents (numbers)
  :short "Parse a binary number from the beginning of a character list."
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with binary
digits (#\\0 and #\\1) and returns their binary value.</p>"

  (defund parse-bits-from-charlist (x val len)
    (declare (type (integer 0 *) val len)
             (xargs :guard (and (character-listp x)
                                (natp val)
                                (natp len))))
    (cond ((atom x)
           (mv (lnfix val) (lnfix len) nil))
          ((eql (car x) #\0)
           (parse-bits-from-charlist
            (cdr x)
            (mbe :logic (* 2 (nfix val))
                 :exec (the (integer 0 *) (ash val 1)))
            (the (integer 0 *) (+ 1 (the (integer 0 *) (lnfix len))))))
          ((eql (car x) #\1)
           (parse-bits-from-charlist
            (cdr x)
            (the (integer 0 *)
              (+ 1
                 (mbe :logic (* 2 (nfix val))
                      :exec (the (integer 0 *) (ash val 1)))))
            (the (integer 0 *) (+ 1 (the (integer 0 *) (lnfix len))))))
          (t
           (mv (lnfix val) (lnfix len) x))))

  (local (in-theory (enable parse-bits-from-charlist)))

  (defthm natp-of-parse-bits-from-charlist
    (implies (natp val)
             (natp (mv-nth 0 (parse-bits-from-charlist x val len))))
    :rule-classes :type-prescription))


(defsection bit-digit-list-value
  :parents (numbers)
  :short "Coerces a list of bit digits into a natural number."
  :long "<p>@(call bit-digit-list-value) is like @(see digit-list-value) but
for bit numbers.</p>

<p>See also @(see parse-bits-from-charlist) for a more flexible function that
can tolerate non-bit digits after the number.</p>"

  (definlined bit-digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (bit-digit-listp x))))
    (b* (((mv val ?len ?rest)
          (parse-bits-from-charlist x 0 0)))
      val))

  (local (in-theory (enable bit-digit-list-value)))

  (defthm natp-of-bit-digit-list-value
    (natp (bit-digit-list-value x))
    :rule-classes :type-prescription)

  (local (defthmd l0
           (implies (icharlisteqv x x-equiv)
                    (equal (mv-nth 0 (parse-bits-from-charlist x val len))
                           (mv-nth 0 (parse-bits-from-charlist x-equiv val len))))
           :hints(("Goal" :in-theory (enable parse-bits-from-charlist
                                             icharlisteqv
                                             ichareqv
                                             downcase-char
                                             char-fix)))))

  (defcong icharlisteqv equal (bit-digit-list-value x) 1
    :hints(("Goal" :use ((:instance l0 (val 0) (len 0))))))

  (local (assert! (and (equal (bit-digit-list-value (coerce "0" 'list)) #b0)
                       (equal (bit-digit-list-value (coerce "1" 'list)) #b1)
                       (equal (bit-digit-list-value (coerce "01" 'list)) #b01)
                       (equal (bit-digit-list-value (coerce "0101011101" 'list))
                              #b0101011101)))))




; BOZO we could do some work to make these nicer, i.e., we should have fast
; versions of strval8, etc., and ordinary strval should have a nicer logical
; definition.

(defsection strval
  :parents (numbers)
  :short "Interpret a string as a decimal number."
  :long "<p>@(call strval) tries to interpret a string as a base-10 natural
number.  For example, @('(strval \"35\")') is 35.  If the string has any
non-decimal digit characters or is empty, we return @('nil').</p>"

  (defund strval (x)
    (declare (type string x))
    (b* (((the (integer 0 *) xl)
          (mbe :logic (len (explode x))
               :exec (length x)))
         ((mv (the (integer 0 *) val)
              (the (integer 0 *) len))
          (str::parse-nat-from-string x 0 0 0 xl)))
      (and (< 0 len)
           (int= len xl)
           val)))

  (local (in-theory (enable strval)))

  (defthm type-of-strval
    (or (natp (strval x))
        (not (strval x)))
    :rule-classes :type-prescription)

  (defcong istreqv equal (strval x) 1))


(defsection strval8
  :parents (numbers)
  :short "Interpret a string as an octal number."
  :long "<p>@(call strval8) is like @(see strval) but for octal instead of
decimal numbers.  For example, @('(strval8 \"10\")') is 8.  If the string is
empty or has any non-octal digit characters, we return @('nil').</p>"

  (defund strval8 (x)
    (declare (type string x))
    (let ((chars (explode x)))
      (and (consp chars)
           (octal-digit-listp chars)
           (octal-digit-list-value chars))))

  (local (in-theory (enable strval8)))

  (defthm type-of-strval8
    (or (natp (strval8 x))
        (not (strval8 x)))
    :rule-classes :type-prescription)

  (defcong istreqv equal (strval8 x) 1))


(defsection strval16
  :parents (numbers)
  :short "Interpret a string as a hexadecimal number."
  :long "<p>@(call strval16) is like @(see strval) but for hexadecimal instead
of decimal numbers.  For example, @('(strval16 \"10\")') is 16.  If the string
is empty or has any non-hex digit characters, we return @('nil').</p>"

  (defund strval16 (x)
    (declare (type string x))
    (let ((chars (explode x)))
      (and (consp chars)
           (hex-digit-listp chars)
           (hex-digit-list-value chars))))

  (local (in-theory (enable strval16)))

  (defthm type-of-strval16
    (or (natp (strval16 x))
        (not (strval16 x)))
    :rule-classes :type-prescription)

  (defcong istreqv equal (strval16 x) 1))


(defsection strval2
  :parents (numbers)
  :short "Interpret a string as a binary number."
  :long "<p>@(call strval2) is like @(see strval) but for binary instead of
decimal numbers.  For example, @('(strval16 \"10\")') is 2.  If the string is
empty or has any non-binary digit characters, we return @('nil').</p>"

  (defund strval2 (x)
    (declare (type string x))
    (let ((chars (explode x)))
      (and (consp chars)
           (bit-digit-listp chars)
           (bit-digit-list-value chars))))

  (local (in-theory (enable strval2)))

  (defthm type-of-strval2
    (or (natp (strval2 x))
        (not (strval2 x)))
    :rule-classes :type-prescription)

  (defcong istreqv equal (strval2 x) 1))



(local (assert! (equal (strval "") nil)))
(local (assert! (equal (strval2 "") nil)))
(local (assert! (equal (strval8 "") nil)))
(local (assert! (equal (strval16 "") nil)))

(local (assert! (equal (strval "0") 0)))
(local (assert! (equal (strval2 "0") 0)))
(local (assert! (equal (strval8 "0") 0)))
(local (assert! (equal (strval16 "0") 0)))

(local (assert! (equal (strval "1234") 1234)))
(local (assert! (equal (strval2 "0101") #b0101)))
(local (assert! (equal (strval8 "1234") #o1234)))
(local (assert! (equal (strval16 "1234") #x1234)))
