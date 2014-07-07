; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "multiply")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm natp-of-expt
  (equal (natp (expt a n))
         t)
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (expt a n)
                  (if (zp n)
                      1
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-not-natp-right-cheap
  (implies (not (natp n))
           (equal (expt a n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-zp-left-cheap
  (implies (zp a)
           (equal (expt a n)
                  (if (zp n)
                      1
                    0)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm expt-when-zp-right-cheap
  (implies (zp n)
           (equal (expt a n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (expt a n))))

(defthm |(expt 0 n)|
  (equal (expt 0 n)
         (if (zp n)
             1
           0)))

(defthm |(expt a 0)|
  (equal (expt a 0)
         1))

(defthm |(expt (nfix a) n)|
  (equal (expt (nfix a) n)
         (expt a n))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(expt a (nfix n))|
  (equal (expt a (nfix n))
         (expt a n))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(expt 1 n)|
  (equal (expt 1 n)
         1)
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt 1 n))))

(defthm |(expt n 1)|
  (equal (expt n 1)
         (nfix n))
  :hints(("Goal" :expand (expt n 1))))

(defthm |(= 0 (expt a n))|
  (equal (equal 0 (expt a n))
         (and (zp a)
              (not (zp n))))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

(defthmd lemma-for-expt-of-plus-right
  (equal (expt a (+ 1 n))
         (* a (expt a n)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand ((expt a (+ 1 n))
                   (expt a 2)))))

(defthm |(expt a (+ n m))|
  (equal (expt a (+ n m))
         (* (expt a n)
            (expt a m)))
  :hints(("Goal"
          :induct (dec-induction m)
          :in-theory (enable lemma-for-expt-of-plus-right)
          :expand ((expt a (+ m n))
                   (expt a m)))))

(defthm |(< a (expt a n))|
  (equal (< a (expt a n))
         (cond ((zp a) (zp n))
               ((equal a 1) nil)
               (t (< 1 n))))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand ((expt a n)
                   (expt a (- n 1))))))

(defthm |(< (expt a n) a)|
  (equal (< (expt a n) a)
         (and (< 1 a)
              (zp n)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

(defthm |(< (expt a n) (expt a m))|
  (equal (< (expt a n) (expt a m))
         (cond ((zp a)      (and (zp m) (not (zp n))))
               ((equal a 1) nil)
               (t           (< n m))))
  :hints(("Goal"
          :induct (dec-dec-induction n m)
          :expand ((expt a n)
                   (expt a m)))))

(defthm |(= 1 (expt a n))|
  (equal (equal 1 (expt a n))
         (or (zp n)
             (equal a 1)))
  :hints(("Goal"
          :induct (dec-induction n)
          :expand (expt a n))))

