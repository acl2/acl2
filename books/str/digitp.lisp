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
(include-book "eqv")
(include-book "misc/list-fix" :dir :system)
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "arithmetic"))



(defsection digitp
  :parents (numbers)
  :short "Recognizer for numeric characters (0-9)."

  :long "<p>ACL2 provides @(see digit-char-p) which is more flexible and can
recognize numeric characters in other bases.  @(call digitp) only recognizes
base-10 digits, but is roughly twice as fast as @('digit-char-p'), at least on
CCL.  Here is an experiment you can run in raw lisp, with times reported in CCL
on the machine Lisp2.</p>

@({
  (defconstant *chars*
    (loop for i from 0 to 256 collect (code-char i)))

  ;; 21.876 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digit-char-p c))))

  ;; 10.819 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digitp c))))
})"

  (definlined digitp (x)
    (declare (type character x))
    (mbe :logic (let ((code (char-code (char-fix x))))
                  (and (<= (char-code #\0) code)
                       (<= code (char-code #\9))))
         :exec (let ((code (the (unsigned-byte 8) (char-code (the character x)))))
                 (declare (type (unsigned-byte 8) code))
                 (and (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))
                      (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57))))))

  (local (in-theory (enable digitp)))

  (defcong chareqv equal (digitp x) 1))



(defsection nonzero-digitp
  :parents (numbers)
  :short "Recognizer for non-zero numeric characters (1-9)."

  (definlined nonzero-digitp (x)
    (declare (type character x))
    (mbe :logic (let ((code (char-code (char-fix x))))
                  (and (<= (char-code #\1) code)
                       (<= code (char-code #\9))))
         :exec (let ((code (the (unsigned-byte 8) (char-code (the character x)))))
                 (declare (type (unsigned-byte 8) code))
                 (and (<= (the (unsigned-byte 8) 49) (the (unsigned-byte 8) code))
                      (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57))))))

  (local (in-theory (enable nonzero-digitp)))

  (defcong chareqv equal (nonzero-digitp x) 1)

  (defthm digitp-when-nonzero-digitp
    (implies (nonzero-digitp x)
             (digitp x))
    :hints(("Goal" :in-theory (enable digitp)))))



(defsection digit-val
  :parents (numbers)
  :short "Coerces a @(see digitp) character into an integer."

  :long "<p>For instance, @('(digit-val #\\3)') is 3.  For any non-@('digitp'),
0 is returned.</p>"

  (definlined digit-val (x)
    (declare (type character x)
             (xargs :guard (digitp x)
                    :guard-hints (("Goal" :in-theory (enable digitp)))))
    (mbe :logic
         (if (digitp x)
             (- (char-code (char-fix x))
                (char-code #\0))
           0)
         :exec
         (the (unsigned-byte 8)
           (- (the (unsigned-byte 8) (char-code (the character x)))
              (the (unsigned-byte 8) 48)))))

  (local (in-theory (enable digitp digit-val char-fix)))

  (defcong chareqv equal (digit-val x) 1)

  (defthm natp-of-digit-val
    (and (integerp (digit-val x))
         (<= 0 (digit-val x)))
    :rule-classes :type-prescription)

  (defthm digit-val-upper-bound
    (< (digit-val x) 10)
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-digit-val-and-digit-val
    (implies (and (digitp x)
                  (digitp y))
             (equal (equal (digit-val x)
                           (digit-val y))
                    (equal x y))))

  (defthm digit-val-of-digit-to-char
    (implies (and (natp n)
                  (< n 10))
             (equal (digit-val (digit-to-char n))
                    n))))



(defsection digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see digitp) characters."

; BOZO consider using cutil::deflist

  (defund digit-listp (x)
    (declare (xargs :guard (character-listp x)))
    (if (consp x)
        (and (digitp (car x))
             (digit-listp (cdr x)))
      t))

  (local (in-theory (enable digit-listp)))

  (defthm digit-listp-when-not-consp
    (implies (not (consp x))
             (digit-listp x)))

  (defthm digit-listp-of-cons
    (equal (digit-listp (cons a x))
           (and (digitp a)
                (digit-listp x))))

  (defcong charlisteqv equal (digit-listp x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

  (defthm digit-listp-of-list-fix
    (equal (digit-listp (list-fix x))
           (digit-listp x)))

  (defthm digit-listp-of-append
    (equal (digit-listp (append x y))
           (and (digit-listp x)
                (digit-listp y))))

  (defthm digit-listp-of-revappend
    (equal (digit-listp (revappend x y))
           (and (digit-listp x)
                (digit-listp y))))

  (defthm digit-listp-of-nthcdr
    (implies (digit-listp x)
             (digit-listp (nthcdr n x)))))



(defsection digit-list-value
  :parents (numbers)
  :short "Coerces a @(see digit-listp) into a natural number."

  :long "<p>For instance, @('(digit-list-value '(#\1 #\0 #\3))') is 103.</p>

<p>See also @(see parse-nat-from-charlist) for a more flexible function that
can tolerate non-numeric characters after the number.</p>"

  (defund digit-list-value1 (x val)
    (declare (type integer val)
             (xargs :guard (and (character-listp x)
                                (digit-listp x)
                                (natp val))
                    :guard-hints (("Goal" :in-theory (enable digit-val digitp)))))
    (mbe :logic (if (consp x)
                    (digit-list-value1 (cdr x)
                                       (+ (digit-val (car x))
                                          (* 10 (nfix val))))
                  (nfix val))
         :exec (if (consp x)
                   (digit-list-value1 (cdr x)
                                      (the integer
                                        (+ (the (unsigned-byte 8)
                                             (- (the (unsigned-byte 8) (char-code (the character (car x))))
                                                (the (unsigned-byte 8) 48)))
                                           (* (the integer 10)
                                              (the integer val)))))
                 (the integer val))))

  (definlined digit-list-value (x)
    (declare (xargs :guard (and (character-listp x)
                                (digit-listp x))
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (+ (* (expt 10 (1- (len x)))
                          (digit-val (car x)))
                       (digit-list-value (cdr x)))
                  0)
         :exec (digit-list-value1 x (the integer 0))))

  (local (in-theory (enable digit-list-value)))

  (defcong charlisteqv equal (digit-list-value x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

  (defthm natp-of-digit-list-value
    (natp (digit-list-value x))
    :rule-classes :type-prescription)

  (encapsulate
    ()
    (set-non-linearp t) ;; implicitly local
    (defthm digit-list-value-upper-bound
      (< (digit-list-value x)
         (expt 10 (len x)))))

  (defthm digit-list-value-upper-bound-free
    (implies (equal n (len x))
             (< (digit-list-value x) (expt 10 n))))

  (defthm digit-list-value1-removal
    (equal (digit-list-value1 x val)
           (+ (digit-list-value x)
              (* (nfix val) (expt 10 (len x)))))
    :hints(("Goal"
            :in-theory (enable digit-list-value1)
            :induct (digit-list-value1 x val))))

  (verify-guards digit-list-value$inline)

  (defthm digit-list-value-of-append
    (equal (digit-list-value (append x (list a)))
           (+ (* 10 (digit-list-value x))
              (digit-val a)))))



(defsection skip-leading-digits

  (defund skip-leading-digits (x)
    (declare (xargs :guard (character-listp x)))
    (if (consp x)
        (if (digitp (car x))
            (skip-leading-digits (cdr x))
          x)
      nil))

  (local (in-theory (enable skip-leading-digits)))

  (defcong charlisteqv charlisteqv (skip-leading-digits x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

  (defthm len-of-skip-leading-digits
    (implies (digitp (car x))
             (< (len (skip-leading-digits x))
                (len x))))

  (defthm character-listp-of-skip-leading-digits
    (implies (character-listp x)
             (character-listp (skip-leading-digits x)))))



(defsection take-leading-digits

  (defund take-leading-digits (x)
    (declare (xargs :guard (character-listp x)))
    (if (consp x)
        (if (digitp (car x))
            (cons (car x) (take-leading-digits (cdr x)))
          nil)
      nil))

  (local (in-theory (enable take-leading-digits)))

  (defcong charlisteqv equal (take-leading-digits x) 1
    :hints(("Goal" :in-theory (enable charlisteqv
                                      ;; Gross, but gets us equal.
                                      digitp
                                      chareqv
                                      char-fix))))

  (defthm character-listp-of-take-leading-digits
    (character-listp (take-leading-digits x))
    :hints(("Goal" :in-theory (enable digitp))))

  (defthm digit-listp-of-take-leading-digits
    (digit-listp (take-leading-digits x)))

  (defthm bound-of-len-of-take-leading-digits
    (<= (len (take-leading-digits x)) (len x))
    :rule-classes :linear)

  (defthm take-leading-digits-when-digit-listp
    (implies (digit-listp x)
             (equal (take-leading-digits x)
                    (list-fix x)))))



(defsection digit-string-p

  (defund digit-string-p-aux (x n xl)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        t
      (and (digitp (char x n))
           (digit-string-p-aux x (+ 1 (lnfix n)) xl))))

  (defthm digit-string-p-aux-removal
    (implies (and (stringp x)
                  (natp n)
                  (equal xl (length x)))
             (equal (digit-string-p-aux x n xl)
                    (digit-listp (nthcdr n (coerce x 'list)))))
    :hints(("Goal" :in-theory (enable digit-string-p-aux
                                      digit-listp))))

  (definline digit-string-p (x)
    (declare (type string x))

; 0.5485 seconds, no garbage
;
; (let ((x "1234"))
;   (time$ (loop for i fixnum from 1 to 10000000 do
;                (str::digit-string-p x))))
;
; 1.3762 seconds, 640 MB allocated
;
; (let ((x "1234"))
;   (time$ (loop for i fixnum from 1 to 10000000 do
;                (str::digit-listp (coerce x 'list)))))

    (mbe :logic (digit-listp (coerce x 'list))
         :exec (digit-string-p-aux x 0 (length x)))))


