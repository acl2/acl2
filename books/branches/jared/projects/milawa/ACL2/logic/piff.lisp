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
(include-book "pand")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; BOZO Dammit I hate this stupid file too.  I wish it would die in a fire.

;; Recall that F <-> G is an abbreviation for (F -> G) ^ (G -> F).
;; I.e., (~F v G) ^ (~G v F)

(defund logic.iff-structurep (x)
  (declare (xargs :guard t))
  (and (logic.and-structurep x)
       (let ((or-not-f-g (logic.andlhs x))
             (or-not-g-f (logic.andrhs x)))
         (and (equal (logic.fmtype or-not-f-g) 'por*)
              (equal (logic.fmtype or-not-g-f) 'por*)
              (let ((not-f (logic.vlhs or-not-f-g))
                    (not-g (logic.vlhs or-not-g-f)))
                (and (equal (logic.fmtype not-f) 'pnot*)
                     (equal (logic.fmtype not-g) 'pnot*)
                     (equal (logic.~arg not-f) (logic.vrhs or-not-g-f))
                     (equal (logic.~arg not-g) (logic.vrhs or-not-f-g))))))))

(defthm booleanp-of-logic.iff-structurep
  (booleanp (logic.iff-structurep x))
  :hints(("Goal" :in-theory (enable logic.iff-structurep))))

(defund logic.ifflhs (x)
  (declare (xargs :guard (logic.iff-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.iff-structurep)))))
  (logic.vrhs      ;; F
   (logic.andrhs   ;; (~G v F)
    x)))           ;; (~F v G) ^ (~G v F)

(defund logic.iffrhs (x)
  (declare (xargs :guard (logic.iff-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.iff-structurep)))))
  (logic.vrhs      ;; G
   (logic.andlhs   ;; (~F v G)
    x)))           ;; (~F v G) ^ (~G v F)

(defund logic.piff (x y)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formulap y))))
  (logic.pand (logic.por (logic.pnot x) y)
              (logic.por (logic.pnot y) x)))

(in-theory (disable (:executable-counterpart logic.piff)))

(defthm logic.piff-under-iff
  (iff (logic.piff x y)
       t)
  :hints(("Goal" :in-theory (enable logic.piff))))

(defthm forcing-logic.iff-structurep-of-logic.piff
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.iff-structurep (logic.piff x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.piff logic.iff-structurep))))

(defthm forcing-logic.formulap-of-logic.piff
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.formulap (logic.piff x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.piff))))

(defthm forcing-logic.formula-atblp-of-logic.piff
  (implies (and (force (logic.formula-atblp x atbl))
                (force (logic.formula-atblp y atbl)))
           (equal (logic.formula-atblp (logic.piff x y) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.piff))))

(defthm forcing-logic.formulap-of-logic.ifflhs
  (implies (force (logic.iff-structurep x))
           (equal (logic.formulap (logic.ifflhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.ifflhs logic.iff-structurep))))

(defthm forcing-logic.formulap-of-logic.iffrhs
  (implies (force (logic.iff-structurep x))
           (equal (logic.formulap (logic.iffrhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.iffrhs logic.iff-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.ifflhs
  (implies (and (force (logic.iff-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.ifflhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.ifflhs logic.iff-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.iffrhs
  (implies (and (force (logic.iff-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.iffrhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.iffrhs logic.iff-structurep))))

(defthm forcing-logic.ifflhs-of-logic.piff
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.ifflhs (logic.piff x y))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.ifflhs logic.piff))))

(defthm forcing-logic.iffrhs-of-logic.piff
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.iffrhs (logic.piff x y))
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.iffrhs logic.piff))))
