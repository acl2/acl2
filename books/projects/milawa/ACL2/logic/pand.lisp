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
(include-book "formulas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO Dammit I hate this stupid file.  I wish it would die.


;; We interpret F ^ G as an abbreviation for ~(~F v ~G).  We write the function
;; logic.and-structurep to recognize formulas of this form.

(defund logic.and-structurep (x)
  ;; BOZO this should be guarded with formulap instead of checking it
  (declare (xargs :guard t))
  (and (logic.formulap x)
       (equal (logic.fmtype x) 'pnot*)
       (let ((or-not-f-not-g (logic.~arg x)))
         (and (equal (logic.fmtype or-not-f-not-g) 'por*)
              (let ((not-f (logic.vlhs or-not-f-not-g))
                    (not-g (logic.vrhs or-not-f-not-g)))
                (and (equal (logic.fmtype not-f) 'pnot*)
                     (equal (logic.fmtype not-g) 'pnot*)))))))

(defthm booleanp-of-logic.and-structurep
  (equal (booleanp (logic.and-structurep x))
         t)
  :hints(("Goal" :in-theory (enable logic.and-structurep))))

(defund logic.andlhs (x)
  (declare (xargs :guard (logic.and-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.and-structurep)))))
  (logic.~arg          ;; F
   (logic.vlhs         ;; ~F
    (logic.~arg        ;; ~F v ~G
     x))))       ;; ~(~F v ~G)

(defund logic.andrhs (x)
  (declare (xargs :guard (logic.and-structurep x)
                  :guard-hints (("Goal" :in-theory (enable logic.and-structurep)))))
  (logic.~arg          ;; G
   (logic.vrhs         ;; ~G
    (logic.~arg        ;; ~F v ~G
     x))))       ;; ~(~F v ~G)

(defund logic.pand (x y)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formulap y))))
  (logic.pnot (logic.por (logic.pnot x)
                         (logic.pnot y))))

(in-theory (disable (:executable-counterpart logic.pand)))

(defthm logic.pand-under-iff
  (iff (logic.pand x y)
       t)
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.and-structurep-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.and-structurep (logic.pand x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.pand logic.and-structurep))))

(defthm forcing-logic.formulap-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.formulap (logic.pand x y))
                  t))
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.formula-atblp-of-logic.pand
  (implies (and (force (logic.formula-atblp x atbl))
                (force (logic.formula-atblp y atbl)))
           (equal (logic.formula-atblp (logic.pand x y) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-logic.formulap-of-logic.andlhs
  (implies (force (logic.and-structurep x))
           (equal (logic.formulap (logic.andlhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.and-structurep))))

(defthm forcing-logic.formulap-of-logic.andrhs
  (implies (force (logic.and-structurep x))
           (equal (logic.formulap (logic.andrhs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.and-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.andlhs
  (implies (and (force (logic.and-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.andlhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.and-structurep))))

(defthm forcing-logic.formula-atblp-of-logic.andrhs
  (implies (and (force (logic.and-structurep x))
                (force (logic.formula-atblp x atbl)))
           (equal (logic.formula-atblp (logic.andrhs x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.and-structurep))))

(defthm forcing-logic.andlhs-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.andlhs (logic.pand x y))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.andlhs logic.pand))))

(defthm forcing-logic.andrhs-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (logic.andrhs (logic.pand x y))
                  y))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.andrhs logic.pand))))


