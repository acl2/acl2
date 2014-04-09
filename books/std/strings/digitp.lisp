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
(include-book "ieqv")
(include-book "std/lists/list-fix" :dir :system)
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "arithmetic"))

(define digitp
  :parents (numbers)
  :short "Recognizer for numeric characters (0-9)."
  ((x :type character))
  :returns bool
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
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\0) code)
                     (<= code (char-code #\9))))
       :exec (let ((code (the (unsigned-byte 8)
                           (char-code (the character x)))))
               (declare (type (unsigned-byte 8) code))
               (and (<= (the (unsigned-byte 8) 48)
                        (the (unsigned-byte 8) code))
                    (<= (the (unsigned-byte 8) code)
                        (the (unsigned-byte 8) 57)))))
  ///
  (defcong ichareqv equal (digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm characterp-when-digitp
    (implies (str::digitp char)
             (characterp char))
    :rule-classes :compound-recognizer))


(define nonzero-digitp
  :parents (numbers)
  :short "Recognizer for non-zero numeric characters (1-9)."
  ((x :type character))
  :returns bool
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\1) code)
                     (<= code (char-code #\9))))
       :exec (let ((code (the (unsigned-byte 8)
                           (char-code (the character x)))))
               (declare (type (unsigned-byte 8) code))
               (and (<= (the (unsigned-byte 8) 49)
                        (the (unsigned-byte 8) code))
                    (<= (the (unsigned-byte 8) code)
                        (the (unsigned-byte 8) 57)))))
  ///
  (defcong ichareqv equal (nonzero-digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm digitp-when-nonzero-digitp
    (implies (nonzero-digitp x)
             (digitp x))
    :hints(("Goal" :in-theory (enable digitp)))))


(define digit-val
  :parents (numbers)
  :short "Coerces a @(see digitp) character into an integer."
  ((x digitp :type character))
  :returns (val natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(digit-val #\\3)') is 3.  For any non-@('digitp'),
0 is returned.</p>"
  :inline t
  (mbe :logic
       (if (digitp x)
           (- (char-code (char-fix x))
              (char-code #\0))
         0)
       :exec
       (the (unsigned-byte 8)
         (- (the (unsigned-byte 8) (char-code (the character x)))
            (the (unsigned-byte 8) 48))))
  :prepwork
  ((local (in-theory (enable digitp char-fix))))
  ///
  (defcong ichareqv equal (digit-val x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char))))

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


(define digit-listp
  :parents (numbers)
  :short "Recognizes lists of @(see digitp) characters."
  ((x character-listp))
  (if (consp x)
      (and (digitp (car x))
           (digit-listp (cdr x)))
    t)
  ///
  ;; BOZO consider using std::deflist instead
  (defthm digit-listp-when-not-consp
    (implies (not (consp x))
             (digit-listp x)))

  (defthm digit-listp-of-cons
    (equal (digit-listp (cons a x))
           (and (digitp a)
                (digit-listp x))))

  (defcong icharlisteqv equal (digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))

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

  (defthm digit-listp-of-rev
    (equal (digit-listp (rev x))
           (digit-listp x)))

  (defthm digit-listp-of-nthcdr
    (implies (digit-listp x)
             (digit-listp (nthcdr n x)))))


(define digit-list-value1
  :parents (digit-list-value)
  ((x   (and (character-listp x)
             (digit-listp x)))
   (val :type (integer 0 *)))
  :guard-hints (("Goal" :in-theory (enable digit-val digitp)))
  (mbe :logic (if (consp x)
                  (digit-list-value1 (cdr x)
                                     (+ (digit-val (car x))
                                        (* 10 (nfix val))))
                (nfix val))
       :exec (if (consp x)
                 (digit-list-value1
                  (cdr x)
                  (the (integer 0 *)
                    (+ (the (unsigned-byte 8)
                         (- (the (unsigned-byte 8)
                              (char-code (the character (car x))))
                            (the (unsigned-byte 8) 48)))
                       (* (the (integer 0 *) 10)
                          (the (integer 0 *) val)))))
               (the (integer 0 *) val))))

(define digit-list-value
  :parents (numbers)
  :short "Coerces a @(see digit-listp) into a natural number."
  ((x (and (character-listp x)
           (digit-listp x))))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(digit-list-value '(#\1 #\0 #\3))') is 103.</p>

<p>See also @(see parse-nat-from-charlist) for a more flexible function that
can tolerate non-numeric characters after the number.</p>"
  :inline t

  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (* (expt 10 (1- (len x)))
                        (digit-val (car x)))
                     (digit-list-value (cdr x)))
                0)
       :exec (digit-list-value1 x 0))
  ///
  (defcong icharlisteqv equal (digit-list-value x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))

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


(define skip-leading-digits ((x character-listp))
  :returns (tail character-listp :hyp :guard)
  (cond ((atom x)
         nil)
        ((digitp (car x))
         (skip-leading-digits (cdr x)))
        (t
         x))
  ///
  (defcong charlisteqv charlisteqv (skip-leading-digits x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

  (defcong icharlisteqv icharlisteqv (skip-leading-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))

  (defthm len-of-skip-leading-digits
    (implies (digitp (car x))
             (< (len (skip-leading-digits x))
                (len x)))))


(define take-leading-digits ((x character-listp))
  :returns (head character-listp)
  (cond ((atom x)
         nil)
        ((digitp (car x))
         (cons (car x) (take-leading-digits (cdr x))))
        (t
         nil))
  ///
  (defcong icharlisteqv equal (take-leading-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv
                                      ;; Gross, but gets us equal.
                                      ichareqv
                                      downcase-char
                                      digitp
                                      char-fix))))

  (defthm digit-listp-of-take-leading-digits
    (digit-listp (take-leading-digits x)))

  (defthm bound-of-len-of-take-leading-digits
    (<= (len (take-leading-digits x)) (len x))
    :rule-classes :linear)

  (defthm take-leading-digits-when-digit-listp
    (implies (digit-listp x)
             (equal (take-leading-digits x)
                    (list-fix x)))))



(define digit-string-p-aux
  :parents (digit-string-p)
  ((x  stringp             :type string)
   (n  natp                :type (integer 0 *))
   (xl (eql xl (length x)) :type (integer 0 *)))
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
  :split-types t
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (eql n xl))
      t
    (and (digitp (char x n))
         (digit-string-p-aux x
                             (mbe :logic (+ 1 (nfix n))
                                  :exec
                                  (the (integer 0 *) (+ 1 n)))
                             xl)))
  ///
  (defthm digit-string-p-aux-removal
    (implies (and (stringp x)
                  (natp n)
                  (equal xl (length x)))
             (equal (digit-string-p-aux x n xl)
                    (digit-listp (nthcdr n (explode x)))))
    :hints(("Goal" :in-theory (enable digit-listp)))))

(define digit-string-p
  :parents (numbers)
  :short "Recognizes strings of @(see digitp) characters."
  ((x :type string))
  :returns bool

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

  :inline t
  :enabled t

  (mbe :logic (digit-listp (explode x))
       :exec (digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (digit-string-p x) 1))

