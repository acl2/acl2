; ACL2 String Library
; Copyright (C) 2009-2014 Centaur Technology
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
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/define" :dir :system)

(defsection code-char-lemmas
  :parents (code-char)
  :short "Lemmas about @(see code-char) from the @(see std/strings) library."

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




(defsection char-code-lemmas
  :parents (char-code)
  :short "Lemmas about @(see char-code) from the @(see std/strings) library."

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
