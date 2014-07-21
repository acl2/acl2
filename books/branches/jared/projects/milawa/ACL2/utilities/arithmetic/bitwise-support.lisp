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

(in-package "ACL2")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (in-theory (disable evenp oddp floor mod logior logxor logand logbitp)))

(local (defun floor2-floor2-induction (a b)
         (declare (xargs :measure (nfix a)))
         (if (or (zp a)
                 (zp b))
             nil
           (floor2-floor2-induction (floor a 2) (floor b 2)))))

(local (defthm evenp-when-natp
         (implies (force (natp a))
                  (equal (evenp a)
                         (equal (mod a 2)
                                0)))
         :hints(("Goal" :in-theory (enable evenp)))))

(local (defthm oddp-when-natp
         (implies (force (natp a))
                  (equal (oddp a)
                         (equal (mod a 2)
                                1)))
         :hints(("Goal" :in-theory (enable oddp)))))


(defthm logand-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logand a b)))
  :hints(("Goal" :in-theory (enable logand))))

(defthm recursive-logand-when-natps
  (implies (and (natp a)
                (natp b))
           (equal (logand a b)
                  (cond ((zp a) 0)
                        ((zp b) 0)
                        (t (+ (if (or (equal (mod a 2) 0)
                                      (equal (mod b 2) 0))
                                  0
                                1)
                              (* 2 (logand (floor a 2) (floor b 2))))))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logand))))


(defthm logior-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logior a b)))
  :hints(("Goal"
          :in-theory (enable logior*)
          :induct (floor2-floor2-induction a b))))

(defthm recursive-logior-when-natps
   (implies (and (natp a)
                 (natp b))
            (equal (logior a b)
                   (cond ((zp a) b)
                         ((zp b) a)
                         (t (+ (if (or (equal (mod a 2) 1)
                                       (equal (mod b 2) 1))
                                   1
                                 0)
                               (* 2 (logior (floor a 2) (floor b 2))))))))
   :rule-classes :definition
   :hints(("Goal"
           :do-not '(generalize fertilize)
           :in-theory (enable logior*)
           :induct (floor2-floor2-induction a b))))


(defthm logxor-positive-when-natps
  (implies (and (<= 0 a)
                (<= 0 b)
                (integerp a)
                (integerp b))
           (<= 0 (logxor a b)))
  :hints(("Goal"
          :in-theory (enable logxor*)
          :induct (floor2-floor2-induction a b))))

(defthm recursive-logxor-when-natps
   (implies (and (natp a)
                 (natp b))
            (equal (logxor a b)
                   (cond ((zp a) b)
                         ((zp b) a)
                         (t (+ (if (equal (mod a 2) (mod b 2))
                                   0
                                 1)
                               (* 2 (logxor (floor a 2) (floor b 2))))))))
   :rule-classes :definition
   :hints(("Goal"
           :in-theory (enable logxor*)
           :induct (floor2-floor2-induction a b))))



(local (defun dec-floor2-induction (n a)
         (declare (xargs :measure (nfix n)))
         (if (zp n)
             a
           (dec-floor2-induction (- n 1) (floor a 2)))))

(defthm recursive-logbitp-when-natps
  (implies (and (natp n)
                (natp a))
           (equal (logbitp n a)
                  (if (zp n)
                      (equal (mod a 2) 1)
                    (logbitp (- n 1) (floor a 2)))))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable logbitp*)
          :induct (dec-floor2-induction n a))))
