; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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
;
; Additional Copyright Notice.
;
; Portions of this file were adapted from the data-structures/memories library,
; Copyright (c) 2005-2006 Kookamara LLC, which is also available under an
; MIT/X11 style license.

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "integer-length"))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable floor mod integer-length logcdr)))




(defsection integer-length-of-floor
  (local (defthm floor-when-a-between-b-and-2b
           (implies (and (posp a) (posp b)
                         (<= b a) (< a (ash b 1)))
                    (equal (floor a b) 1))
           :hints(("Goal" :in-theory (e/d (ash)
                                          (acl2::floor-bounded-by-/))
                   :use ((:instance acl2::floor-bounded-by-/
                          (x a) (y b))))
                  (and stable-under-simplificationp
                       '(:cases ((and (< (/ a b) 2)
                                      (<= 1 (/ a b))))
                         :in-theory (disable acl2::<-*-/-left
                                             acl2::<-*-/-left-commuted
                                             acl2::<-*-/-right
                                             acl2::<-*-/-left-commuted)))
                  (and stable-under-simplificationp
                       '(:in-theory (Enable))))))

  (local (Defthmd ash-1-is-2*
           (equal (ash x 1)
                  (* 2 (ifix x)))
           :hints(("Goal" :in-theory (enable ash)))))

  (local (defthm integer-length-bound-when-a<b<<1
           (implies (and (< a (ash b 1))
                         (posp a) (posp b))
                    (<= (integer-length a) (+ 1 (integer-length b))))
           :hints (("goal" :use ((:instance bitops::integer-length-monotonic
                                  (i a) (j (ash b 1))))
                    :in-theory (disable ash)))
           :rule-classes (:linear :forward-chaining)))


  (local (Defun integer-length-of-floor-ind (a b)
           (declare (xargs :measure (nfix (+ 1 (- (integer-length a) (integer-length b))))))
           (if (or (zp a) (zp b) (< a b))
               0
             (+ 1 (integer-length-of-floor-ind a (ash b 1))))))

  (defthmd integer-length-of-floor
    (implies (and (posp a) (posp b) (<= b a))
             (equal (integer-length (floor a b))
                    (if (< a (ash b (- (integer-length a) (integer-length b))))
                        (- (integer-length a)
                           (integer-length b))
                      (+ 1 (- (integer-length a)
                              (integer-length b))))))
    :hints (("goal" :induct (integer-length-of-floor-ind a b))
            (and stable-under-simplificationp
                 '(:expand ((:with integer-length 
                             (integer-length (floor a b))))
                   :in-theory (enable ash-1-is-2*)
                   :do-not '(generalize))))))



(defthmd floor-monotonic-arg1
  (implies (and (<= a1 a2)
                (rationalp a1) (rationalp a2)
                (posp b))
           (<= (floor a1 b) (floor a2 b)))
  :hints (("goal" :use ((:instance acl2::floor-mod-elim
                         (x a1) (y b))
                        (:instance acl2::floor-mod-elim
                         (x a2) (y b)))
           :in-theory (disable acl2::floor-mod-elim))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes :linear)

(defthmd floor-monotonic-arg2
  (implies (and (<= b1 b2)
                (posp b1) (posp b2)
                (natp a))
           (<= (floor a b2) (floor a b1)))
  :hints (("goal" :use ((:instance acl2::floor-mod-elim
                         (x a) (y b1))
                        (:instance acl2::floor-mod-elim
                         (x a) (y b2)))
           :in-theory (disable acl2::floor-mod-elim
                               (force)))
          (and stable-under-simplificationp
               '(:nonlinearp t)))
  :rule-classes :linear)


