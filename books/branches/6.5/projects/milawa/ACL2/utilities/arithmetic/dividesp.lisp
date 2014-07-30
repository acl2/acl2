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
(include-book "mod")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(definlined dividesp (a b)
  ;; By convention we say 0 does not divide anything.  We use a mod-based
  ;; definition here, but we then immediately introduce definition-of-dividesp
  ;; which gives it a recursive form.
  (declare (xargs :guard t))
  (if (zp a)
      nil
    (equal (mod b a) 0)))

(defund recursive-dividesp (a b)
  (declare (xargs :measure (nfix b)))
  (cond ((zp a)  nil)
        ((zp b)  t)
        ((< b a) nil)
        (t       (recursive-dividesp a (- b a)))))

(defthmd lemma-for-definition-of-dividesp
  (equal (equal 0 (mod a b))
         (if (zp b)
             (zp a)
           (recursive-dividesp b a)))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand ((recursive-dividesp b a)))))

(defthmd lemma-2-for-definition-of-dividesp
  (equal (dividesp a b)
         (recursive-dividesp a b))
  :hints(("Goal"
          :in-theory (enable dividesp
                             lemma-for-definition-of-dividesp)
          :expand (recursive-dividesp a b))))

(defthmd definition-of-dividesp
   (equal (dividesp a b)
          (cond ((zp a)  nil)
                ((zp b)  t)
                ((< b a) nil)
                (t       (dividesp a (- b a)))))
   :rule-classes ((:definition)
                  (:induction :corollary t
                              :pattern (dividesp a b)
                              :scheme (recursive-dividesp a b)))
   :hints(("Goal"
           :in-theory (enable lemma-for-definition-of-dividesp
                              lemma-2-for-definition-of-dividesp)
           :expand (recursive-dividesp a b))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition dividesp))))

(defthm recursive-dividesp-removal
  (equal (recursive-dividesp a b)
         (dividesp a b))
  :hints(("Goal" :in-theory (enable lemma-2-for-definition-of-dividesp))))

(defthm |(= 0 (mod a b))|
  (equal (equal 0 (mod a b))
         (if (zp b)
             (zp a)
           (dividesp b a)))
  :hints(("Goal" :in-theory (enable lemma-for-definition-of-dividesp))))

(defthm booleanp-of-dividesp
  (equal (booleanp (dividesp a b))
         t)
  :hints(("Goal"
          :induct (sub-induction b a)
          :expand (dividesp a b))))

(defthm divides-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (dividesp a b)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (dividesp a b))))

(defthm divides-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (dividesp a b)
                  (not (zp a))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (dividesp a b))))

(defthm divides-when-zp-left-cheap
  (implies (zp a)
           (equal (dividesp a b)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (dividesp a b))))

(defthm divides-when-zp-right-cheap
  (implies (zp b)
           (equal (dividesp a b)
                  (not (zp a))))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (dividesp a b))))

(defthm dividesp-of-nfix-left
  (equal (dividesp (nfix a) b)
         (dividesp a b))
  :hints(("Goal" :expand ((dividesp (nfix a) b)
                          (dividesp a b)))))

(defthm dividesp-of-nfix-right
  (equal (dividesp a (nfix b))
         (dividesp a b))
  :hints(("Goal" :expand ((dividesp a (nfix b))
                          (dividesp a b)))))

(defthm |(dividesp 0 a)|
  (equal (dividesp 0 a)
         nil))

(defthm |(dividesp a 0)|
  (equal (dividesp a 0)
         (not (zp a))))

(defthm |(dividesp 1 a)|
  (equal (dividesp 1 a)
         t)
  :hints(("Goal"
          :induct (sub-induction a 1)
          :expand (dividesp 1 a))))

(defthm |(dividesp a 1)|
  (equal (dividesp a 1)
         (equal a 1))
  :hints(("Goal" :expand (dividesp a 1))))

(defthm |(dividesp a a)|
  (equal (dividesp a a)
         (not (zp a)))
  :hints(("Goal" :expand (dividesp a a))))

(defthm |(< b a) when (dividesp a b)|
  (implies (dividesp a b)
           (equal (< b a)
                  (zp b)))
  :hints(("Goal" :expand (dividesp a b))))

(defthm |(< a b) when (dividesp a b)|
  (implies (dividesp a b)
           (equal (< a b)
                  (and (not (zp b))
                       (not (equal a b)))))
  :hints(("Goal" :expand (dividesp a b))))

(defthm |(dividesp a (+ a b))|
  (equal (dividesp a (+ a b))
         (dividesp a b))
  :hints(("Goal" :expand (dividesp a (+ a b)))))

(defthm |(dividesp a (+ b a))|
  (equal (dividesp a (+ b a))
         (dividesp a b))
  :hints(("Goal" :expand (dividesp a (+ a b)))))

(defthm mod-when-dividesp
  (implies (dividesp a b)
           (equal (mod b a)
                  0)))

(defthm dividesp-of-plus-when-dividesp
  (implies (dividesp a b)
           (equal (dividesp a (+ b c))
                  (dividesp a c)))
  :hints(("Goal"
          :induct (sub-induction b a)
          :expand ((dividesp a b)
                   (dividesp a (+ b c))))))

(defthm dividesp-of-plus-when-dividesp-alt
  (implies (dividesp a b)
           (equal (dividesp a (+ c b))
                  (dividesp a c))))

(defthm |(dividesp a (- b a))|
  (equal (dividesp a (- b a))
         (if (< b a)
             t
           (dividesp a b)))
  :hints(("Goal"
          :expand (dividesp a b)
          :induct (sub-induction a b))))

(defthm |(dividesp a (- a b))|
  (equal (dividesp a (- a b))
         (cond ((zp a) nil)
               ((zp b) t)
               (t      (not (< b a)))))
  :hints(("Goal" :expand (dividesp a (- a b)))))










#|


(defthm lemma
  (implies (and (dividesp a b)
                (dividesp a c))
           (dividesp a (- b c)))
  :hints(("Goal" :in-theory (enable definition-of-dividesp))))


(defthm dividesp-of-minus-when-dividesp
  (implies (dividesp a b)
           (equal (dividesp a (- b c))
                  (if (< b c)
                      t
                    (dividesp a c))))
  :hints(("Goal"
          :in-theory (enable dividesp)
          :induct (dividesp a b))))


(defthm equal-zero-of-left-when-dividesp-free
  (implies (dividesp a b)
           (equal (equal 0 a)
                  nil)))

(defthm natp-of-left-when-dividesp-free
  (implies (dividesp a b)
           (equal (natp a)
                  t)))

(defthm positive-of-left-when-dividesp-free
  (implies (dividesp a b)
           (equal (< 0 a)
                  t)))




(defthm crock
  (implies (and (natp b)
                (not (equal b 0))
                (not (< c b)))
           (equal (< b c)
                  (not (equal b c))))
  :hints(("Goal"
          :use ((:instance trichotomy-of-<
                           (a b) (b c))))))

(defthm crock2
  (implies (and (< c b)
                (< b (+ a c))
                (dividesp a b))
           (not (dividesp a c)))
  :hints(("Goal" :in-theory (enable definition-of-dividesp))))



(defthm dividesp-of-times-when-divides-left
  (implies (dividesp a b)
           (equal (dividesp a (* b c))
                  t))
  :hints(("Goal"
          :induct (dec-induction b)
          :in-theory (enable definition-of-dividesp))))

(defthm dividesp-mod-when-divides-both
  (implies (and (dividesp a b)
                (dividesp a c))
           (dividesp a (mod b c)))
  :hints(("Goal"
          :in-theory (enable dividesp mod)
          :induct (mod b c))))

(defthm transitivity-of-dividesp
  (implies (and (dividesp a b)
                (dividesp b c))
           (equal (dividesp a c)
                  t))
  :hints(("Goal"
          :in-theory (enable definition-of-dividesp))))

|#