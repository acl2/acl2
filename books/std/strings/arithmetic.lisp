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

(in-package "ACL2")
(include-book "coerce")
(include-book "arithmetic/top" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/len" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/append" :dir :system)
(include-book "std/lists/repeat" :dir :system)


;; BOZO fundamental lemmas that should probably be part of other libraries.

(defthm negative-when-natp
  (implies (natp x) (equal (< x 0) nil)))

(defthm eqlablep-when-characterp
  (implies (characterp x) (eqlablep x)))

(defthm nth-of-len
  (equal (nth (len x) x)
         nil))

(defthm nth-when-bigger
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil))
  :hints(("Goal" :in-theory (enable nth))))


(defthm car-of-repeat
  (equal (car (repeat n x))
         (if (zp n)
             nil
           x))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm len-of-nonempty-string-is-positive
  (implies (and (stringp x)
                (not (equal x "")))
           (< 0 (len (explode x))))
  :rule-classes ((:rewrite) (:linear)))

(defthm length-zero-when-stringp
  (implies (stringp x)
           (equal (equal 0 (length x))
                  (equal x ""))))

(defthm length-zero-when-stringp-alt
  (implies (stringp x)
           (equal (equal 0 (len (explode x)))
                  (equal x ""))))



(defthm subsetp-equal-of-cons-right
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons b y))))

(defthm subsetp-equal-reflexive
  (subsetp-equal x x))


(encapsulate
  ()
  (local (defthm l1
           (implies (or (not (natp x))
                        (<= 256 x))
                    (equal (code-char x)
                           (code-char 0)))
           :hints(("Goal" :use ((:instance acl2::completion-of-code-char))))))

  (local (defthm l2
           (implies (natp k)
                    (equal (char-code (code-char (+ k (char-code a))))
                           (if (and (integerp k)
                                    (<= 0 (+ k (char-code a)))
                                    (< (+ k (char-code a)) 256))
                               (+ k (char-code a))
                             0)))
           :hints(("Goal"
                   :cases ((< (+ k (char-code a)) 256))))))

  (local (defthm l0
           (implies (and (integerp a)
                         (not (integerp b)))
                    (equal (integerp (+ a b))
                           (not (acl2-numberp b))))))

  (defthm char-code-of-code-char-of-sum-with-char-code
    (equal (char-code (code-char (+ k (char-code a))))
           (cond ((integerp k)
                  (if (and (<= 0 (+ k (char-code a)))
                           (< (+ k (char-code a)) 256))
                      (+ k (char-code a))
                    0))
                 ((acl2-numberp k)
                  0)
                 (t
                  (char-code a))))
    :hints(("Goal" :in-theory (e/d ()
                                   (code-char-char-code-is-identity
                                    str::equal-of-char-codes))))))


(defthm characterp-of-car-when-character-listp
  (implies (character-listp x)
           (equal (characterp (car x))
                  (consp x))))

(defthm character-listp-of-cdr-when-character-listp
  (implies (character-listp x)
           (character-listp (cdr x))))

(defthm character-listp-of-repeat
  (implies (characterp x)
           (character-listp (repeat n x)))
  :hints(("Goal" :in-theory (enable repeat))))

(defthm character-listp-of-take
  (implies (character-listp x)
           (equal (character-listp (take n x))
                  (<= (nfix n) (len x))))
  :hints(("Goal" :in-theory (enable take))))

(defthm character-listp-of-rev
  (equal (character-listp (rev x))
         (character-listp (list-fix x)))
  :hints(("Goal" :induct (len x))))
