; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "ieqv")
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(defsection ichar<
  :parents (ordering)
  :short "Case-insensitive character less-than test."

  :long "<p>@(call ichar<) determines if @('x') is \"smaller\" than @('y'), but
ignoring case.  Our approach is basically to downcase upper-case letters and
then compare the resulting character codes.</p>

<p>Something subtle about this is that, in the ASCII character ordering, the
upper-case characters do not immediately preceede the lower-case ones.  That
is, upper-case Z is at 90, but lower-case a does not start until 97.  So, in
our approach, the 6 intervening characters (the square brackets, backslash,
hat, underscore, and backtick) are considered \"smaller\" than letters, even
though in regular ASCII ordering they are \"larger\" than the upper-case
letters.</p>"

  (definlined ichar< (x y)
    (declare (type character x)
             (type character y)
             (xargs :guard-hints(("Goal" :in-theory (enable downcase-char)))))
    (mbe :logic
         (< (char-code (downcase-char x))
            (char-code (downcase-char y)))
         :exec
         (let* ((xc (the (unsigned-byte 8) (char-code (the character x))))
                (yc (the (unsigned-byte 8) (char-code (the character y))))
                (xc-fix (if (and (<= (big-a) (the (unsigned-byte 8) xc))
                                 (<= (the (unsigned-byte 8) xc) (big-z)))
                            (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                          (the (unsigned-byte 8) xc)))
                (yc-fix (if (and (<= (big-a) (the (unsigned-byte 8) yc))
                                 (<= (the (unsigned-byte 8) yc) (big-z)))
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

  (defthm ichar<-trichotomy-weak
    (implies (and (not (ichar< x y))
                  (not (ichar< y x)))
             (equal (ichareqv x y)
                    t))
    :hints(("Goal" :in-theory (enable ichar<
                                      ichareqv
                                      downcase-char
                                      char-fix))))

  (defcong ichareqv equal (ichar< x y) 1
    :hints(("Goal" :in-theory (enable ichar<
                                      ichareqv
                                      downcase-char
                                      char-fix))))

  (defcong ichareqv equal (ichar< x y) 2
    :hints(("Goal" :in-theory (enable ichar<
                                      ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm ichar<-trichotomy-strong
    (equal (ichar< x y)
           (and (not (ichareqv x y))
                (not (ichar< y x))))
    :hints(("Goal"
            :in-theory (e/d (ichareqv downcase-char char-fix)
                            (ichar<-trichotomy-weak))
            :use ((:instance ichar<-trichotomy-weak))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))



(defsection icharlist<
  :parents (ordering)
  :short "Case-insensitive character-list less-than test."

  :long "<p>@(call icharlist<) determines whether the character list @('x')
preceeds @('y') in alphabetical order without regards to case.  The characters
are compared with @(see ichar<) and shorter strings are considered smaller than
longer strings.</p>"

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
                       (xc-fix (if (and (<= (big-a) (the (unsigned-byte 8) xc))
                                        (<= (the (unsigned-byte 8) xc) (big-z)))
                                   (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                                 (the (unsigned-byte 8) xc)))
                       (yc-fix (if (and (<= (big-a) (the (unsigned-byte 8) yc))
                                        (<= (the (unsigned-byte 8) yc) (big-z)))
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
    :hints(("Goal" :in-theory (e/d (ichar< downcase-char)
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

  :long "<p>@(call icharlist<) determines whether the string @('x') preceeds
@('y') in alphabetical order without regards to case.  The characters are
compared with @(see ichar<) and shorter strings are considered smaller than
longer strings.</p>

<p>Logically, this is identical to:</p>

@({
  (icharlist< (explode x) (explode y))
})

<p>But we use a more efficient implementation which avoids coercing the strings
into lists.</p>

<p>NOTE: for reasoning, we leave this function enabled and prefer to work with
@(see icharlist<) of the explodes as our normal form.</p>"

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
                       (xc-fix (if (and (<= (big-a) (the (unsigned-byte 8) xc))
                                        (<= (the (unsigned-byte 8) xc) (big-z)))
                                   (the (unsigned-byte 8) (+ (the (unsigned-byte 8) xc) 32))
                                 (the (unsigned-byte 8) xc)))
                       (yc-fix (if (and (<= (big-a) (the (unsigned-byte 8) yc))
                                        (<= (the (unsigned-byte 8) yc) (big-z)))
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

  (definline istr< (x y)
    (declare (type string x)
             (type string y)
             (xargs :verify-guards nil))
    (mbe :logic
         (icharlist< (explode x) (explode y))

         :exec
         (istr<-aux (the string x)
                    (the string y)
                    (the integer 0)
                    (the integer (length (the string x)))
                    (the integer (length (the string y))))))

  (local (defthm crock
           (equal (< a a)
                  nil)))

  (local (defthm crock2
           (implies (< a b)
                    (equal (< b a)
                           nil))))

  (verify-guards istr<-aux
    :hints(("Goal" :in-theory (e/d (ichar< downcase-char)))))

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

  (verify-guards istr<$inline)

  (defcong istreqv equal (istr< x y) 1)
  (defcong istreqv equal (istr< x y) 2))

