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
(include-book "floor")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm natp-of-mod
  (equal (natp (mod a b))
         t)
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (mod a b))))

(defthm mod-when-not-natp-left-cheap
  (implies (not (natp a))
           (equal (mod a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (mod a b))))

(defthm mod-when-not-natp-right-cheap
  (implies (not (natp b))
           (equal (mod a b)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (mod a b))))

(defthm mod-when-zp-left-cheap
  (implies (zp a)
           (equal (mod a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (mod a b))))

(defthm mod-when-zp-right-cheap
  (implies (zp b)
           (equal (mod a b)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :expand (mod a b))))

(defthm mod-of-nfix-left
  (equal (mod (nfix a) b)
         (mod a b))
  :hints(("Goal" :expand ((mod (nfix a) b)
                          (mod a b)))))

(defthm mod-of-nfix-right
  (equal (mod a (nfix b))
         (mod a b))
  :hints(("Goal" :expand ((mod a (nfix b))
                          (mod a b)))))

(defthm |(mod 0 a)|
  (equal (mod 0 a)
         0))

(defthm |(mod a 0)|
  (equal (mod a 0)
         (nfix a)))

(defthm |(mod a 1)|
  (equal (mod a 1)
         0)
  :hints(("Goal"
          :induct (sub-induction a 1)
          :expand (mod a 1))))

(defthm |(mod 1 a)|
  (equal (mod 1 a)
         (if (equal a 1)
             0
           1))
  :hints(("Goal" :expand (mod 1 a))))

(defthm mod-when-in-range
  (implies (< a b)
           (equal (mod a b)
                  (nfix a)))
  :hints(("Goal" :expand (mod a b))))

(defthm floor-mod-elim
  (equal (+ (mod a b) (* b (floor a b)))
         (nfix a))
  :hints(("Goal"
          :expand ((mod a b)
                   (floor a b))
          :induct (sub-induction a b))))

(defthm |(< a (* b (floor a b)))|
  (equal (< a (* b (floor a b)))
         nil)
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (floor a b))))

(defthm |(< (* b (floor a b)) a)|
  (equal (< (* b (floor a b)) a)
         (not (equal (mod a b) 0)))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand ((floor a b)
                   (mod a b)))))

(defthmd eliminate-mod
  (equal (mod a b)
         (- a (* b (floor a b)))))

(defthm |(< a (mod a b))|
  (equal (< a (mod a b))
         nil)
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (mod a b))))

(defthm |(< b (mod a b))|
  (equal (< b (mod a b))
         (and (zp b)
              (not (zp a))))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (mod a b))))

(defthm |(< (mod a b) b)|
  (equal (< (mod a b) b)
         (not (zp b)))
  :hints(("Goal"
          :induct (sub-induction a b)
          :expand (mod a b))))

(defthm |(< (mod a b) a)|
  (equal (< (mod a b) a)
         (if (zp b)
             nil
           (not (< a b)))))

(defthm |(mod a a)|
  (equal (mod a a)
         0)
  :hints(("Goal" :expand (mod a a))))

(defthm |(mod (+ a b) b)|
  (equal (mod (+ a b) b)
         (mod a b))
  :hints(("Goal" :expand (mod (+ a b) b))))

(defthm |(mod (- a b) b)|
  (equal (mod (- a b) b)
         (if (< a b)
             0
           (mod a b)))
  :hints(("Goal" :expand (mod a b))))




#|


(defun my-induction (a b x)
  (declare (xargs :measure (nfix a)))
  (cond ((zp x) nil)
        ((or (zp a)
             (zp b))
         nil)
        (t
         (my-induction (- a x) (- b x) x))))


;; (defthm crock
;;   (equal (equal (mod (- b a) x) 0)
;;          (equal (mod b x) a)))

(defthm subcrock
  (implies (and (not (zp x))
                (not (< b x)))
           (equal (< b (+ x (mod b x)))
                  nil))
  :hints(("Goal"
          :cases ((equal b x))
          :do-not-induct t)
         ("Subgoal 2"
          :in-theory (disable floor-mod-elim)
          :do-not '(generalize)
          :use ((:instance floor-mod-elim (a b) (b x)))))

  :otf-flg t)


(defthm crock
  (implies (and (not (zp x))
                (equal (mod b x) a))
           (equal (mod (- b a) x)
                  0))
  :hints(("Goal" :induct (mod b x))))

(defthm my-lemma
  (implies (and (not (zp x))
                (equal (mod a x) result))
           (equal (equal (mod b x) result)
                  (if (< a b)
                      (equal (mod (- b a) x) 0)
                    (equal (mod (- a b) x) 0))))
  :hints(("Goal"
          :induct (my-induction a b x))))


(defthm crock
  (implies (and (natp b)
                (not (equal b 0))
                (not (< c b)))
           (equal (< b c)
                  (not (equal b c))))
  :hints(("Goal"
          :use ((:instance trichotomy-of-<
                           (a b) (b c))))))

(defthm |(mod (+ a b) x)|
  (implies (< (+ (mod a x) (mod b x)) x)
           (equal (mod (+ a b) x)
                  (+ (mod a x) (mod b x))))
  :hints(("Goal" :in-theory (enable definition-of-mod))))

|#