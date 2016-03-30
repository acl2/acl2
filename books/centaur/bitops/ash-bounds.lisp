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


; ash-bounds.lisp
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITOPS")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))


(defsection bitops/ash-bounds
  :parents (bitops)
  :short "A book with some basic bounding and monotonicity lemmas for @(see
ash) and @(see logtail)."

  :long "<p>This is a fast-loading book that can be used separately from the
rest of Bitops.</p>")


(defsection self-bounds-for-logtail
  :parents (bitops/ash-bounds logtail)
  :short "Lemmas for the bounds of @('(logtail n a)') versus @('a')."

  :long "<p>These are lemmas for:</p>
<ul>
<li>@('  (< (logtail n a) a)  ')</li>
<li>@('  (= a (logtail n a))  ')</li>
<li>@('  (< a (logtail n a))  ')</li>
</ul>"

  ;; 1. (< (LOGTAIL N A) A) ---------------------------------------------------

  (local (defthm c0
           (implies (zp n)
                    (equal (logtail n a) (ifix a)))))

  (local (defthm c1
           (implies (zip a)
                    (equal (logtail n a)
                           0))))

  (local (defthm c2
           (equal (logtail n -1)
                  -1)))

  (local (defthm l0
           (implies (and (posp a)
                         (posp n))
                    (< (logtail n a) a))
           :hints(("Goal" :in-theory (enable logtail**
                                             logtail-induct
                                             logcdr)))))

  (local (defthm l1
           (implies (and (integerp a)
                         (< a 0))
                    (equal (< a (logtail n a))
                           (and (posp n)
                                (not (equal a -1)))))
           :hints(("Goal" :in-theory (enable logtail**
                                             logtail-induct
                                             logcdr)))))

  (local (defthm l2
           (implies (and (integerp a)
                         (< a 0))
                    (equal (< (logtail n a) a)
                           nil))
           :hints(("Goal" :in-theory (disable l1)
                   :use ((:instance l1))))))

  (defthm |(< (logtail n a) a)|
    (equal (< (logtail n a) a)
           (if (zip a)
               ;; Degenerate, yucky case: the logtail term is going to be zero so
               ;; this *should* just be NIL, but if A is not a well-formed
               ;; integer, i.e., we're asking about (logtail n 1/2) or something,
               ;; then it boils down to (< 0 1/2) instead.
               (< 0 a)
             (and (posp a)
                  (posp n))))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (and (posp a)
                                          (posp n))
                                     (< (logtail n a) a)))))


  ;; 2. (= A (LOGTAIL N A)) ---------------------------------------------------

  (local (defthm j1
           (implies (and (posp a)
                         (posp n))
                    (equal (equal (logtail n a) a)
                           nil))))

  (local (defthm j2
           (implies (posp a)
                    (equal (equal (logtail n a) a)
                           (zp n)))))

  (local (defthm j3
           (equal (equal (logtail n -1) -1)
                  t)))

  (local (defthm j4
           (implies (and (integerp a)
                         (< a -1))
                    (equal (equal (logtail n a) a)
                           (zp n)))
           :hints(("Goal"
                   :in-theory (disable l1)
                   :use ((:instance l1))))))

  (local (defthm j5
           (implies (and (integerp a)
                         (< a 0))
                    (equal (equal (logtail n a) a)
                           (or (equal a -1)
                               (zp n))))))

  (defthm |(= a (logtail n a))|
    (equal (= a (logtail n a))
           (if (zip a)
               ;; Sort of degenerate: this should really just be true any time A
               ;; is zero, but again the non-integer case gets in the way, e.g.,
               ;; if we take the logtail of 1/2, then we're going to get zero.
               (equal a 0)
             (or (zp n)
                 (equal a -1))))
    :hints(("Goal" :use ((:instance j5)))))


  ;; 3. (< A (LOGTAIL N A)) ---------------------------------------------------

  (local (defthm k1
           (implies (posp a)
                    (equal (< a (logtail n a))
                           nil))
           :hints(("Goal"
                   :in-theory (disable |(< (logtail n a) a)|)
                   :use ((:instance |(< (logtail n a) a)|))))))

  (local (defthm k2
           (implies (zip a)
                    (equal (< a (logtail n a))
                           (< a 0)))))

  (local (defthm k3
           (implies (and (integerp a)
                         (< a 0))
                    (equal (< a (logtail n a))
                           (and (posp n)
                                (not (equal a -1)))))))

  (local (defthm k4
           (equal (< a (logtail n a))
                  (cond ((zip a)
                         (< a 0))
                        ((posp a)
                         nil)
                        (t
                         (and (posp n)
                              (not (equal a -1))))))))

  (defthm |(< a (logtail n a))|
    (equal (< a (logtail n a))
           (if (zip a)
               (< a 0)
             (and (posp n)
                  (< a -1))))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (and (posp n)
                                          (< a -1))
                                     (< a (logtail n a)))))))


(defsection self-bounds-for-ash
  :parents (bitops/ash-bounds ash)
  :short "Lemmas for the bounds of @('(ash a b)') versus @('a')."

  :long "<p>These are lemmas for:</p>
<ul>
<li>@('  (< (ASH A B) A)  ')</li>
<li>@('  (= A (ASH A B))  ')</li>
<li>@('  (< A (ASH A B))  ')</li>
</ul>

<p>BOZO these only address when A is positive.  We should extend these
to negative numbers.</p>"

  (local (defthm l1
           (implies (and (posp a)
                         (posp b))
                    (< a (ash a b)))
           :rule-classes :linear
           :hints(("Goal"
                   :in-theory (enable ash**
                                      ash**-induct
                                      logcons)))))

  (local (defthm l2
           (implies (zip b)
                    (equal (ash a b) (ifix a)))))

  (local (defthm l3
           (implies (and (posp a)
                         (integerp b)
                         (< b 0))
                    (< (ash a b) a))
           :rule-classes :linear
           :hints(("Goal"
                   :in-theory (enable ash**
                                      ash**-induct)))))

  (defthm |(< a (ash a b)) when (posp a)|
    (implies (posp a)
             (equal (< a (ash a b))
                    (posp b)))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (and (posp a)
                                          (posp b))
                                     (< a (ash a b))))))

  (defthm |(= a (ash a b)) when (posp a)|
    (implies (posp a)
             (equal (equal a (ash a b))
                    (zip b)))
    :hints(("Goal" :use ((:instance l3)))))

  (defthm |(< (ash a b) a) when (posp a)|
    (implies (posp a)
             (equal (< (ash a b) a)
                    (negp b)))
    :rule-classes ((:rewrite)
                   (:linear :corollary
                            (implies (and (posp a)
                                          (negp b))
                                     (< (ash a b) a))))
    :hints(("Goal"
            :in-theory (disable |(< a (ash a b)) when (posp a)|
                                |(= a (ash a b)) when (posp a)|)
            :use ((:instance |(< a (ash a b)) when (posp a)|)
                  (:instance |(= a (ash a b)) when (posp a)|))))))



(defsection monotonicity-properties-of-ash
  :parents (bitops/ash-bounds ash)
  :short "Lemmas about @('(ash a b)') versus @('(ash a c)')."

  :long "<p>These are basic lemmas about:</p>

<ul>
<li>@('  (< (ASH A B) (ASH A C))  ')</li>
<li>@('  (= (ASH A B) (ASH A C))  ')</li>
</ul>

<p>BOZO these only address when A is positive and B/C are naturals.  We should
extend these to negative numbers.</p>"

  (local (defun pos-induct (a b c)
           (if (or (zp b)
                   (zp c))
               (list a b c)
             (pos-induct a (- b 1) (- c 1)))))

  (defthm |(< (ash a b) (ash a c))|
    (implies (and (posp a)
                  (natp b)
                  (natp c))
             (equal (< (ash a b)
                       (ash a c))
                    (< b c)))
    :hints(("Goal"
            :induct (pos-induct a b c)
            :in-theory (enable ash** logcons))))

  (defthm |(= (ash a b) (ash a c))|
    (implies (and (posp a)
                  (natp b)
                  (natp c))
             (equal (equal (ash a b)
                           (ash a c))
                    (equal b c)))
    :hints(("Goal"
            :induct (pos-induct a b c)
            :in-theory (enable ash** logcons)))))




(defsection |(= 0 (ash 1 x))|
  :parents (bitops/ash-bounds ash)

  (local (defthm l0
           (implies (zip x)
                    (equal (ash 1 x) 1))))

  (local (defthm l1
           (implies (posp x)
                    (< 1 (ash 1 x)))))

  (local (defthm l2
           (implies (and (integerp x)
                         (< x 0))
                    (equal (ash 1 x) 0))))

  (defthm |(= 0 (ash 1 x))|
    (equal (equal 0 (ash 1 x))
           (negp x))
    :hints(("Goal" :in-theory (enable negp)))))
