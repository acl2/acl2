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
(include-book "extended-primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm natp-of-*
  (equal (natp (* a b))
         t)
  :hints(("Goal" :expand (* a b))))

(defthm *-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (* a b))))

(defthm *-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm *-when-zp-left-cheap
  (implies (zp a)
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (* a b))))

(defthm *-when-zp-right-cheap
  (implies (zp b)
           (equal (* a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm |(* 0 a)|
  (equal (* 0 a)
         0)
  :hints(("Goal" :expand (* 0 a))))

(defthm |(* a 0)|
  (equal (* a 0)
         0)
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a 0))))

(defthm |(* (nfix a) b)|
  (equal (* (nfix a) b)
         (* a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(* a (nfix b))|
  (equal (* a (nfix b))
         (* a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm |(* 1 a)|
  (equal (* 1 a)
         (nfix a))
  :hints(("Goal" :expand (* 1 a))))

(defthm |(* a 1)|
  (equal (* a 1)
         (nfix a))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a 1))))

(defthm |(equal (* a b) 0)|
  (equal (equal (* a b) 0)
         (or (zp a)
             (zp b)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b))))

(defthm |(* (+ a c) b)|
  (equal (* (+ a c) b)
         (+ (* a b) (* c b)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* (+ 1 c) b)
                   (* (+ a c) b)
                   (* a b)))))

(defthm |(* a (+ b c))|
  (equal (* a (+ b c))
         (+ (* a b) (* a c)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* a (+ b c))
                   (* a b)
                   (* a c)))))

(defthm |(* (- a b) c)|
  (equal (* (- a b) c)
         (- (* a c) (* b c)))
  :hints(("Goal"
          :induct (dec-dec-induction a b)
          :expand ((* (- a b) c)
                   (* a c)
                   (* b c)))))

(defthm |(* a (- b c))|
  (equal (* a (- b c))
         (- (* a b) (* a c)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand ((* a b)
                   (* a c)
                   (* a (- b c)))
          :in-theory (disable |(* (- a b) c)|)
          :do-not-induct t)))

(defthm |(< a (* a b))|
  (equal (< a (* a b))
         (and (not (zp a))
              (< 1 b)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< b (* a b))|
  (equal (< b (* a b))
         (and (not (zp b))
              (< 1 a)))
  :hints(("Goal"
          :induct (dec-induction a)
          :expand (* a b)
          :in-theory (disable |(* (- a b) c)|))))

(defthm |(< (* a b) a)|
  (equal (< (* a b) a)
         (and (not (zp a))
              (zp b)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< (* a b) b)|
  (equal (< (* a b) b)
         (and (not (zp b))
              (zp a)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm |(< (* a c) (* b c))|
  (equal (< (* a c) (* b c))
         (and (< a b)
              (not (zp c))))
  :hints(("Goal" :induct (dec-dec-induction a b))))

(defthm |(< (* a b) (* a c))|
  (equal (< (* a b) (* a c))
         (and (< b c)
              (not (zp a))))
  :hints(("Goal" :induct (dec-induction a))))

(defthm associativity-of-*
  (equal (* (* a b) c)
         (* a (* b c)))
  :hints(("Goal" :induct (dec-induction a))))

(defthm commutativity-of-*
  (equal (* a b)
         (* b a))
  :hints(("Goal" :induct (dec-induction a))))

(defthm commutativity-of-*-two
  (equal (* a (* b c))
         (* b (* a c)))
  :hints(("Goal" :use ((:instance commutativity-of-* (a a) (b (* b c)))))))

(defthm |(= a (* a b))|
  (equal (equal a (* a b))
         (if (zp a)
             (natp a)
           (equal b 1)))
  :hints(("Goal"
          :expand ((* a b)
                   (* b (- a 1)))
          :in-theory (disable |(* a (- b c))|))))

(defthm |(= 1 (* a b))|
  (equal (equal 1 (* a b))
         (and (equal a 1)
              (equal b 1)))
  :hints(("Goal"
          :expand ((* a b))
          :use ((:instance |(* a (- b c))| (a b) (b a) (c 1)))
          :in-theory (disable |(* a (- b c))|))))

