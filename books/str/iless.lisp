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
(include-book "ieqv")
(include-book "char-case")
(local (include-book "unicode/nthcdr" :dir :system))
(local (include-book "arithmetic"))


(local
 (encapsulate
   ()
   (local (defund exhaustive-test (n)
            (and (let ((x (code-char n)))
                   (implies (and (<= 65 (char-code x))
                                 (<= (char-code x) 90))
                            (and (standard-char-p x)
                                 (standard-char-p (code-char (+ (char-code x) 32))))))
                 (or (zp n)
                     (exhaustive-test (- n 1))))))

   (local (defthm lemma
            (implies (and (natp n)
                          (natp m)
                          (exhaustive-test n)
                          (= x (code-char m))
                          (<= m n)
                          (<= n 255))
                     (implies (and (<= 65 (char-code x))
                                   (<= (char-code x) 90))
                              (and (standard-char-p x)
                                   (standard-char-p (code-char (+ (char-code x) 32))))))
            :hints(("goal"
                    :induct (exhaustive-test n)
                    :in-theory (enable exhaustive-test)))))

   (defthm standard-char-p-when-upper-case
     (implies (and (<= 65 (char-code x))
                   (<= (char-code x) 90))
              (standard-char-p x))
     :hints(("Goal"
             :in-theory (disable lemma)
             :use ((:instance lemma
                              (n 255)
                              (m (char-code x)))))))

   (defthm standard-char-p-of-char-downcase
     (implies (and (<= 65 (char-code x))
                   (<= (char-code x) 90))
              (standard-char-p (code-char (+ 32 (char-code x)))))
     :hints(("goal"
             :in-theory (disable lemma)
             :use ((:instance lemma
                              (n 255)
                              (m (char-code x)))))))))


(defsection ichar<
  :parents (ordering)
  :short "Case-insensitive character less-than test."

  :long "<p>@(call ichar<) determines if <tt>x</tt> is \"smaller\" than
<tt>y</tt>, but ignoring case.  Our approach is basically to downcase
upper-case letters and then compare the resulting character codes.</p>

<p>Something subtle about this is that, in the ASCII character ordering, the
upper-case characters do not immediately preceede the lower-case ones.  That
is, upper-case Z is at 90, but lower-case a does not start until 97.  So, in
our approach, the 6 intervening characters (the square brackets, backslash,
hat, underscore, and backtick) are considered \"smaller\" than letters, even
though in regular ASCII ordering they are \"larger\" than the upper-case
letters.</p>"

  (defund ichar< (x y)
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

  (local (in-theory (enable ichar<)))

  (defthm ichar<-irreflexive
    (not (ichar< x x)))

  (defthm ichar<-antisymmetric
    (implies (ichar< x y)
             (not (ichar< y x))))

  (defthm ichar<-transitive
    (implies (and (ichar< x y)
                  (ichar< y z))
             (ichar< x z)))

  (defthm ichar<-transitive-two
    (implies (and (ichar< y z)
                  (ichar< x y))
             (ichar< x z)))

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
      :hints(("Goal" :in-theory (enable ichar<
                                        ichareqv
                                        downcase-char)))))

  (defcong ichareqv equal (ichar< x y) 1
    :hints(("Goal" :in-theory (enable ichar<
                                      ichareqv
                                      downcase-char
                                      standard-char-p-of-char-downcase))))

  (defcong ichareqv equal (ichar< x y) 2
    :hints(("Goal" :in-theory (enable ichar<
                                      ichareqv
                                      downcase-char
                                      standard-char-p-of-char-downcase))))

  (defthm ichar<-trichotomy-strong
    (equal (ichar< x y)
           (and (not (ichareqv x y))
                (not (ichar< y x))))
    :hints(("Goal"
            :in-theory (e/d (ichareqv downcase-char)
                            (ichar<-trichotomy-weak))
            :use ((:instance ichar<-trichotomy-weak))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))



(defsection icharlist<
  :parents (ordering)
  :short "Case-insensitive character-list less-than test."

  :long "<p>@(call icharlist<) determines whether the character list <tt>x</tt>
preceeds <tt>y</tt> in alphabetical order without regards to case.  The
characters are compared with @(see ichar<) and shorter strings are considered
smaller than longer strings.</p>"

  (defund icharlist< (x y)
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

  (local (in-theory (enable icharlist<)))

  (verify-guards icharlist<
    :hints(("Goal" :in-theory (e/d (ichar<)
                                   (ichar<-trichotomy-strong)))))

  (defthm icharlist<-irreflexive
    (equal (icharlist< x x)
           nil))

  (defthm icharlist<-antisymmetric
    (implies (icharlist< x y)
             (not (icharlist< y x))))

  (defthm icharlist<-transitive
    (implies (and (icharlist< x y)
                  (icharlist< y z))
             (icharlist< x z)))

  (defthm icharlist<-trichotomy-weak
    (implies (and (not (icharlist< x y))
                  (not (icharlist< y x)))
             (equal (icharlisteqv x y)
                    t)))

  (defcong icharlisteqv equal (icharlist< x y) 1)
  (defcong icharlisteqv equal (icharlist< x y) 2)

  (defthm icharlist<-trichotomy-strong
    (equal (icharlist< x y)
           (and (not (icharlisteqv x y))
                (not (icharlist< y x))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))



(defsection istr<
  :parents (ordering)
  :short "Case-insensitive string less-than test."

  :long "<p>@(call icharlist<) determines whether the string <tt>x</tt>
preceeds <tt>y</tt> in alphabetical order without regards to case.  The
characters are compared with @(see ichar<) and shorter strings are considered
smaller than longer strings.</p>

<p>Logically, this is identical to:</p>

<code>
  (icharlist&lt; (coerce x 'list) (coerce y 'list))
</code>

<p>But we use a more efficient implementation which avoids coercing the strings
into lists.</p>

<p>NOTE: for reasoning, we leave this function enabled and prefer to work with
@(see icharlist<) of the coerces as our normal form.</p>"

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

  (defun istr< (x y)
    (declare (type string x)
             (type string y)
             (xargs :verify-guards nil))
    (mbe :logic
         (icharlist< (coerce x 'list) (coerce y 'list))

         :exec
         (istr<-aux (the string x)
                    (the string y)
                    (the integer 0)
                    (the integer (length (the string x)))
                    (the integer (length (the string y))))))

  (local (in-theory (enable istr<-aux
                            istr<)))

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

  (verify-guards istr<))

