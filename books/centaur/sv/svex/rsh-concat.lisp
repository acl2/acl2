; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")

(include-book "4vec")
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (in-theory (disable ash logapp)))

(defthm 4vec-concat-associative
  (implies (and (2vec-p w1)
                (<= 0 (2vec->val w1))
                (2vec-p w2)
                (<= 0 (2vec->val w2)))
           (equal (4vec-concat w1 (4vec-concat w2 a b) c)
                  (if (<= (2vec->val w1) (2vec->val w2))
                      (4vec-concat w1 a c)
                    (4vec-concat w2 a (4vec-concat (2vec (- (2vec->val w1)
                                                            (2vec->val w2)))
                                                   b c)))))
  :hints(("Goal" :in-theory (enable 4vec-concat))
         (acl2::logbitp-reasoning)))

(defthm 4vec-concat-of-0
  (equal (4vec-concat 0 lo hi)
         (4vec-fix hi))
  :hints(("Goal" :in-theory (enable 4vec-concat))))

(defthm 4vec-rsh-0
    (equal (4vec-rsh 0 x)
           (4vec-fix x))
    :hints(("Goal" :in-theory (enable 4vec-rsh))))

(defthm 4vec-rsh-of-rsh
  (implies (and (2vec-p sh1)
                (<= 0 (2vec->val sh1))
                (2vec-p sh2)
                (<= 0 (2vec->val sh2)))
           (equal (4vec-rsh sh1 (4vec-rsh sh2 x))
                  (4vec-rsh (2vec (+ (2vec->val sh1)
                                     (2vec->val sh2)))
                            x)))
  :hints(("Goal" :in-theory (enable 4vec-rsh))))


(defthmd equal-of-logapp
  (equal (equal (logapp w x1 y1) (logapp w x2 y2))
         (and (equal (ifix y1) (ifix y2))
              (equal (loghead w x1) (loghead w x2))))
  :hints ((acl2::logbitp-reasoning :prune-examples nil)))

(defthm 4vec-rsh-of-concat
  (implies (and (2vec-p sh)
                (<= 0 (2vec->val sh))
                (2vec-p w)
                (<= 0 (2vec->val w)))
           (equal (4vec-rsh sh (4vec-concat w x y))
                  (if (< (2vec->val sh) (2vec->val w))
                      (4vec-concat (2vec (- (2vec->val w)
                                            (2vec->val sh)))
                                   (4vec-rsh sh x) y)
                    (4vec-rsh (2vec (- (2vec->val sh)
                                       (2vec->val w)))
                              y))))
  :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-concat))))

(defthmd equal-of-4vec-fix
  (equal (equal (4vec-fix x) (4vec-fix y))
         (and (equal (4vec->upper x) (4vec->upper y))
              (equal (4vec->lower x) (4vec->lower y))))
  :hints(("Goal" :in-theory (enable 4vec-fix 4vec->upper 4vec->lower 4vec-p))))

(defthmd equal-of-4vec-concat
  (implies (and (syntaxp (not (and (quotep y1) (quotep y2)
                                   (equal y1 y2)
                                   (equal (acl2::unquote y1) (4vec-z)))))
                (2vec-p w)
                (<= 0 (2vec->val w)))
           (equal (equal (4vec-concat w x1 y1) (4vec-concat w x2 y2))
                  (and (equal (4vec-fix y1) (4vec-fix y2))
                       (equal (4vec-concat w x1 (4vec-z))
                              (4vec-concat w x2 (4vec-z))))))
  :hints(("Goal" :in-theory (enable 4vec-concat equal-of-4vec-fix
                                    equal-of-logapp))))
