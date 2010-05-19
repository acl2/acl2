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
(include-book "ieqv")
(local (include-book "unicode/nthcdr" :dir :system))
(local (include-book "arithmetic"))
(local (include-book "char-support"))


(defund ichar< (x y)

  ":Doc-Section Str
  Case-insensitive character less-than test~/

  Our approach is basically to downcase upper-case letters.  Something subtle
  about this is that, in the ASCII character ordering, the upper-case
  characters do not immediately preceede the lower-case ones.  That is,
  upper-case Z is at 90, but lower-case a does not start until 97.  So, in our
  approach, the 6 intervening characters (the square brackets, backslash, hat,
  underscore, and backtick) are considered \"smaller\" than letters, even though
  in regular ASCII ordering they are \"larger\" than the upper-case letters.
  ~/

  ~l[istr<] and ~pl[icharlist<]"

  (declare (type character x)
           (type character y))

  (mbe :logic
       (let* ((xc (if (characterp x)
                      (char-code x)
                    0))
              (yc (if (characterp y)
                      (char-code y)
                    0))
              (xc-fix (if (and (<= (char-code #\A) xc) (<= xc (char-code #\Z)))
                          (+ xc 32)
                        xc))
              (yc-fix (if (and (<= (char-code #\A) yc) (<= yc (char-code #\Z)))
                          (+ yc 32)
                        yc)))
         (< xc-fix yc-fix))

       :exec
       (let* ((xc     (the (unsigned-byte 8) (char-code (the character x))))
              (yc     (the (unsigned-byte 8) (char-code (the character y))))
              (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                               (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                          (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                        (the (unsigned-byte 8) xc)))
              (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                               (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                          (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                        (the (unsigned-byte 8) yc))))
         (< (the (unsigned-byte 8) xc-fix)
            (the (unsigned-byte 8) yc-fix)))))

(defthm ichar<-irreflexive
  (not (ichar< x x))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-antisymmetric
  (implies (ichar< x y)
           (not (ichar< y x)))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-transitive
  (implies (and (ichar< x y)
                (ichar< y z))
           (ichar< x z))
  :hints(("Goal" :in-theory (enable ichar<))))

(defthm ichar<-transitive-two
  (implies (and (ichar< y z)
                (ichar< x y))
           (ichar< x z))
  :hints(("Goal" :in-theory (enable ichar<))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (<= 65 (char-code x))
                        (<= (char-code x) 90)
                        (equal (char-code y) (+ 32 (char-code x))))
                   (standard-char-p y))
          :hints(("Goal"
                  :in-theory (disable standard-char-p-of-char-downcase)
                  :use ((:instance standard-char-p-of-char-downcase))))))

 (defthm ichar<-trichotomy-weak
   (implies (and (not (ichar< x y))
                 (not (ichar< y x)))
            (equal (ichareqv x y)
                   t))
   :hints(("Goal" :in-theory (enable ichar< ichareqv)))))

(defcong ichareqv equal (ichar< x y) 1
  :hints(("Goal" :in-theory (enable ichar<
                                    ichareqv
                                    char-downcase-redefinition
                                    standard-char-p-of-char-downcase))))

(defcong ichareqv equal (ichar< x y) 2
  :hints(("Goal" :in-theory (enable ichar<
                                    ichareqv
                                    char-downcase-redefinition
                                    standard-char-p-of-char-downcase))))

(defthm ichar<-trichotomy-strong
  (equal (ichar< x y)
         (and (not (ichareqv x y))
              (not (ichar< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))





(defund icharlist< (x y)

  ":Doc-Section Str
  Case-insensitive character-list less-than test~/

  We determine whether one character list alphabetically preceeds another, where
  each character is tested with ~il[char<] and shorter strings are said to come
  before longer strings. ~/

  ~l[ichar<] and ~pl[istr<]"

  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))
                  :verify-guards nil))

  (mbe :logic (cond ((atom y)
                     nil)
                    ((atom x)
                     t)
                    ((ichar< (car x) (car y))
                     t)
                    ((ichar< (car y) (car x))
                     nil)
                    (t
                     (icharlist< (cdr x) (cdr y))))
       :exec
       (cond ((atom y)
              nil)
             ((atom x)
              t)
             (t
              (let* ((xc     (the (unsigned-byte 8) (char-code (the character (car x)))))
                     (yc     (the (unsigned-byte 8) (char-code (the character (car y)))))
                     (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                                      (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                               (the (unsigned-byte 8) xc)))
                     (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                                      (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                               (the (unsigned-byte 8) yc))))
                (cond ((< (the (unsigned-byte 8) xc-fix) (the (unsigned-byte 8) yc-fix))
                       t)
                      ((< (the (unsigned-byte 8) yc-fix) (the (unsigned-byte 8) xc-fix))
                       nil)
                      (t
                       (icharlist< (cdr x) (cdr y)))))))))

(verify-guards icharlist<
               :hints(("Goal" :in-theory (e/d (ichar<)
                                              (ichar<-trichotomy-strong)))))

(defthm icharlist<-irreflexive
  (equal (icharlist< x x)
         nil)
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-antisymmetric
  (implies (icharlist< x y)
           (not (icharlist< y x)))
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-transitive
  (implies (and (icharlist< x y)
                (icharlist< y z))
           (icharlist< x z))
  :hints(("Goal" :in-theory (enable icharlist<))))

(defthm icharlist<-trichotomy-weak
   (implies (and (not (icharlist< x y))
                 (not (icharlist< y x)))
            (equal (icharlisteqv x y)
                   t))
   :hints(("Goal" :in-theory (enable icharlist<))))

(defcong icharlisteqv equal (icharlist< x y) 1
  :hints(("Goal" :in-theory (enable icharlist<))))

(defcong icharlisteqv equal (icharlist< x y) 2
  :hints(("Goal" :in-theory (enable icharlist< icharlisteqv))))

(defthm icharlist<-trichotomy-strong
  (equal (icharlist< x y)
         (and (not (icharlisteqv x y))
              (not (icharlist< y x))))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))




(defund istr<-aux (x y n xl yl)
  (declare (type string x)
           (type string y)
           (type integer n)
           (type integer xl)
           (type integer yl)
           (xargs :guard (and (stringp x)
                              (stringp y)
                              (natp n)
                              (<= n (length x))
                              (<= n (length y))
                              (equal xl (length x))
                              (equal yl (length y)))
                  :verify-guards nil
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (mbe :logic
       (cond ((zp (- (nfix yl) (nfix n)))
              nil)
             ((zp (- (nfix xl) (nfix n)))
              t)
             ((ichar< (char x n) (char y n))
              t)
             ((ichar< (char y n) (char x n))
              nil)
             (t
              (istr<-aux x y (+ (nfix n) 1) xl yl)))
       :exec
       (cond ((= (the integer n) (the integer yl))
              nil)
             ((= (the integer n) (the integer xl))
              t)
             (t
              (let* ((xc     (the (unsigned-byte 8)
                               (char-code (the character
                                            (char (the string x) (the integer n))))))
                     (yc     (the (unsigned-byte 8)
                               (char-code (the character
                                            (char (the string y) (the integer n))))))
                     (xc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) xc))
                                      (<= (the (unsigned-byte 8) xc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                               (the (unsigned-byte 8) xc)))
                     (yc-fix (if (and (<= (the (unsigned-byte 8) 65) (the (unsigned-byte 8) yc))
                                      (<= (the (unsigned-byte 8) yc) (the (unsigned-byte 8) 90)))
                                 (the (unsigned-byte 8) (+ (the (unsigned-byte 8) yc) 32))
                               (the (unsigned-byte 8) yc))))
                (cond ((< (the (unsigned-byte 8) xc-fix) (the (unsigned-byte 8) yc-fix))
                       t)
                      ((< (the (unsigned-byte 8) yc-fix) (the (unsigned-byte 8) xc-fix))
                       nil)
                      (t
                       (istr<-aux (the string x)
                                  (the string y)
                                  (the integer (+ (the integer n) 1))
                                  (the integer xl)
                                  (the integer yl)))))))))

(verify-guards istr<-aux
               :hints(("Goal" :in-theory (e/d (ichar<)
                                              (ichar<-trichotomy-strong)))))

(defthm istr<-aux-correct
  (implies (and (stringp x)
                (stringp y)
                (natp n)
                (<= n (length x))
                (<= n (length y))
                (equal xl (length x))
                (equal yl (length y)))
           (equal (istr<-aux x y n xl yl)
                  (icharlist< (nthcdr n (coerce x 'list))
                              (nthcdr n (coerce y 'list)))))
  :hints(("Goal" :in-theory (enable istr<-aux icharlist<))))



(defun istr< (x y)

  ":Doc-Section Str
  Case-insensitive string less-than test~/

  We determine whether one string alphabetically preceeds another, where each
  character is tested with ~il[char<] and shorter strings are said to come
  before longer strings.

  Logically, ~c[(istr< x y)] is ~c[(icharlist< (coerce x 'list) (coerce y 'list)],
  but we use a more efficient implementation which avoids coercing the strings.~/

  ~l[ichar<] and ~pl[icharlist<]"

  (declare (type string x)
           (type string y))

  (mbe :logic
       (icharlist< (coerce x 'list) (coerce y 'list))

       :exec
       (istr<-aux (the string x)
                  (the string y)
                  (the integer 0)
                  (the integer (length (the string x)))
                  (the integer (length (the string y))))))





