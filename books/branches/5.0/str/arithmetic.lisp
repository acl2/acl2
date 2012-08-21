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

(in-package "ACL2")
(include-book "arithmetic/top" :dir :system)
(include-book "unicode/nthcdr" :dir :system)
(include-book "unicode/append" :dir :system)
(include-book "unicode/repeat" :dir :system)
(in-theory (enable acl2::make-list-ac->repeat))


;; BOZO fundamental lemmas that should probably be part of other libraries.

(defthm negative-when-natp
  (implies (natp x) (equal (< x 0) nil)))

(defthm eqlablep-when-characterp
  (implies (characterp x) (eqlablep x)))

(defthm len-zero
  (equal (equal 0 (len x))
         (not (consp x))))

(defthm nth-of-len
  (equal (nth (len x) x)
         nil))

(defthm nth-when-bigger
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil))
  :hints(("Goal" :in-theory (enable nth))))

(defthm character-listp-of-repeat
  (implies (characterp x)
           (character-listp (acl2::repeat x n)))
  :hints(("Goal" :in-theory (enable acl2::repeat))))

(defthm len-of-append
  (equal (len (append x y))
         (+ (len x)
            (len y))))

(defthm consp-of-repeat
  (equal (consp (acl2::repeat x n))
         (not (zp n)))
  :hints(("Goal" :in-theory (enable acl2::repeat))))

(defthm car-of-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthm car-of-repeat
  (equal (car (acl2::repeat x n))
         (if (zp n)
             nil
           x))
  :hints(("Goal" :in-theory (enable acl2::repeat))))

(defthm append-of-repeat-to-cons-of-same
  (equal (append (acl2::repeat a n) (cons a x))
         (cons a (append (acl2::repeat a n) x)))
  :hints(("Goal" :in-theory (enable acl2::repeat))))


(defthm len-of-nonempty-string-is-positive
  (implies (and (stringp x)
                (not (equal x "")))
           (< 0 (len (coerce x 'list))))
  :hints(("Goal"
          :in-theory (disable coerce-inverse-2)
          :use ((:instance coerce-inverse-2)))))

(defthm simpler-take-of-len
  (equal (simpler-take (len x) x)
         (list-fix x))
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm simpler-take-of-zero
  (equal (simpler-take 0 x)
         nil)
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm character-listp-of-simpler-take
  (implies (character-listp x)
           (equal (character-listp (simpler-take n x))
                  (<= (nfix n) (len x))))
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm subsetp-equal-of-cons-right
  (implies (subsetp-equal x y)
           (subsetp-equal x (cons b y))))

(defthm subsetp-equal-reflexive
  (subsetp-equal x x))


;; Lemmas for working with character codes.

(defthm equal-of-char-code-and-char-code
  (implies (and (characterp x)
                (characterp y))
           (equal (equal (char-code x) (char-code y))
                  (equal x y)))
  :hints(("Goal" :use acl2::equal-char-code)))

(defthm equal-of-char-code-and-constant
  (implies (syntaxp (quotep c))
           (equal (equal (char-code x) c)
                  (if (characterp x)
                      (and (natp c)
                           (<= c 255)
                           (equal x (code-char c)))
                    (equal c 0)))))

(defthm code-char-when-not-natp
  (implies (not (natp x))
           (equal (code-char x)
                  (code-char 0)))
  :hints(("Goal" :use ((:instance acl2::completion-of-code-char)))))

(defthm equal-of-char-code-of-plus
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep const))
                (characterp a)
                (natp y)
                (natp const)
                (<= (+ const y) 255))
           (equal (equal a (code-char (+ const y)))
                  (equal y (- (char-code a) const)))))

(encapsulate
 ()
 (local (defund exhaustive-test1 (x y)
          (and (equal (equal (code-char x) (code-char y))
                      (equal x y))
               (or (zp y)
                   (exhaustive-test1 x (- y 1))))))

 (local (defund exhaustive-test2 (x y)
          (and (exhaustive-test1 x y)
               (or (zp x)
                   (exhaustive-test2 (- x 1) y)))))

 (local (defthm lemma1
          (implies (and (exhaustive-test1 x y)
                        (natp x)
                        (natp y)
                        (natp m)
                        (<= m y)
                        (<= x 255)
                        (<= y 255))
                   (equal (equal (code-char x) (code-char m))
                          (equal x m)))
          :hints(("Goal" :in-theory (enable exhaustive-test1)))))

 (local (defthm lemma2
          (implies (and (exhaustive-test2 x y)
                        (natp x)
                        (natp y)
                        (<= x 255)
                        (<= y 255)
                        (natp n)
                        (natp m)
                        (<= n x)
                        (<= m y))
                   (equal (equal (code-char n) (code-char m))
                          (equal n m)))
          :hints(("Goal"
                  :in-theory (enable exhaustive-test2)
                  :induct (exhaustive-test2 x y))
                 ("Subgoal *1/1"
                  :in-theory (disable lemma1)
                  :use ((:instance lemma1
                                   (x 0)
                                   (m m)
                                   (y y)))))))

 (defthm equal-of-code-chars
   (implies (and (natp n)
                 (natp m)
                 (<= n 255)
                 (<= m 255))
            (equal (equal (code-char n) (code-char m))
                   (equal n m)))
   :hints(("Goal"
           :in-theory (disable lemma2)
           :use ((:instance lemma2
                            (x 255)
                            (y 255)
                            (n n)
                            (m m)))))))