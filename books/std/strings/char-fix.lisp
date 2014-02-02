; ACL2 String Library
; Copyright (C) 2009-2014 Centaur Technology
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
(include-book "std/util/define" :dir :system)

(defsection code-char-lemmas
  :parents (code-char)
  :short "Lemmas about @(see code-char) from the @(see str) library."

  (defthm default-code-char
    (implies (or (zp x)
                 (not (< x 256)))
             (equal (code-char x)
                    (code-char 0)))
    :hints(("Goal" :use ((:instance completion-of-code-char)))))

  (local (defthm l0
           (implies (not (or (zp x)
                             (not (< x 256))))
                    (not (equal (code-char x)
                                (code-char 0))))
           :hints(("Goal" :use ((:instance char-code-code-char-is-identity (n x)))))))

  (local (defthm l1
           (equal (equal (code-char x)
                         (code-char 0))
                  (or (zp x)
                      (not (< x 256))))))

  (local (defthm l2
           (implies (and (natp n)
                         (natp m)
                         (< n 256)
                         (< m 256))
                    (equal (equal (code-char n) (code-char m))
                           (equal n m)))
           :hints(("Goal"
                   :in-theory (disable char-code-code-char-is-identity)
                   :use ((:instance char-code-code-char-is-identity (n n))
                         (:instance char-code-code-char-is-identity (n m)))))))

  (defthm equal-of-code-char-and-code-char
    (equal (equal (code-char x) (code-char y))
           (let ((zero-x (or (zp x) (>= x 256)))
                 (zero-y (or (zp y) (>= y 256))))
             (if zero-x
                 zero-y
               (equal x y))))
    :hints(("Goal"
            :in-theory (disable l2)
            :use ((:instance l2 (n x) (m y))))))

  (defthm equal-of-code-code-and-constant
    (implies (syntaxp (quotep c))
             (equal (equal (code-char x) c)
                    (and (characterp c)
                         (if (equal c (code-char 0))
                             (or (zp x)
                                 (not (< x 256)))
                           (equal x (char-code c))))))
    :hints(("goal" :use ((:instance completion-of-code-char))))))


(define char-fix (x)
  :returns (char characterp :rule-classes :type-prescription)
  :parents (equivalences)
  :short "Coerce to a character."

  :long "<p>@(call char-fix) is the identity on @(see acl2::characters), and
returns the NUL character (i.e., the character whose code is 0) for any
non-character.</p>

<p>This is similar to other fixing functions like @(see fix) and @(see nfix).
See also @(see chareqv).</p>"
  :inline t
  (if (characterp x)
      x
    (code-char 0))
  ///
  (defthm char-fix-default
    (implies (not (characterp x))
             (equal (char-fix x)
                    (code-char 0))))

  (defthm char-fix-when-characterp
    (implies (characterp x)
             (equal (char-fix x)
                    x))))


(defsection char-code-lemmas
  :parents (char-code)
  :short "Lemmas about @(see char-code) from the @(see str) library."

  (defthm equal-of-char-code-and-constant
    (implies (syntaxp (quotep c))
             (equal (equal (char-code x) c)
                    (if (characterp x)
                        (and (natp c)
                             (<= c 255)
                             (equal x (code-char c)))
                      (equal c 0)))))

  (local (defthm l0
           (implies (and (characterp x)
                         (characterp y))
                    (equal (equal (char-code x) (char-code y))
                           (equal x y)))
           :hints(("Goal" :use acl2::equal-char-code))))

  (defthm equal-of-char-codes
    (equal (equal (char-code x) (char-code y))
           (equal (char-fix x)
                  (char-fix y)))
    :hints(("Goal" :in-theory (enable char-fix)))))
