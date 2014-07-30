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


(defthm natp-of-floor
  (equal (natp (floor a b))
         t)
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-zp-left-cheap
  (implies (zp a)
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm floor-when-zp-right-cheap
  (implies (zp b)
           (equal (floor a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (floor a b))))

(defthm |(floor 0 a)|
  (equal (floor 0 a)
         0))

(defthm |(floor a 0)|
  (equal (floor a 0)
         0))

(defthm floor-when-smaller
  (implies (< a b)
           (equal (floor a b)
                  0))
  :hints(("Goal" :expand (floor a b))))

(defthm |(floor a a)|
  (equal (floor a a)
         (if (zp a)
             0
           1))
  :hints(("Goal" :expand (floor a a))))

(defthm |(floor 1 a)|
  (equal (floor 1 a)
         (if (equal a 1)
             1
           0))
  :hints(("Goal" :expand (floor 1 a))))

(defthm |(floor a 1)|
  (equal (floor a 1)
         (nfix a))
  :hints(("Goal"
          :induct (sub-induction a 1)
          :expand (floor a 1))))

(defthm |(< a (floor a b))|
  (equal (< a (floor a b))
         nil)
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (floor a b))))

(defthm |(< (floor a b) a)|
  (equal (< (floor a b) a)
         (cond ((zp a) nil)
               ((zp b) t)
               ((equal a 1) (< a b))
               ((equal b 1) nil)
               (t t)))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (floor a b))))

(defthm |(floor (* a b) b)|
  (equal (floor (* a b) b)
         (if (zp b)
             0
           (nfix a)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (floor (* a b) b))))

(defthm |(floor (* a b) a)|
  (equal (floor (* a b) a)
         (if (zp a)
             0
           (nfix b)))
  :hints(("Goal"
          :in-theory (disable |(floor (* a b) b)|)
          :use ((:instance |(floor (* a b) b)| (a b) (b a))))))

