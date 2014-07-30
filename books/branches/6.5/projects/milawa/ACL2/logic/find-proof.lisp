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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; BOZO implement a deffinder sort of macro?

(defund logic.find-proof (a x)
  ;; We return the first proof in x which concludes a, or nil if no such proof
  ;; is present.
  (declare (xargs :guard (and (logic.formulap a)
                              (logic.appeal-listp x))))
  (if (consp x)
      (if (equal (logic.conclusion (car x)) a)
          (car x)
        (logic.find-proof a (cdr x)))
    nil))


(defthm logic.find-proof-when-not-consp
  (implies (not (consp x))
           (equal (logic.find-proof a x)
                  nil))
  :hints(("Goal" :in-theory (enable logic.find-proof))))

(defthm logic.find-proof-of-cons
  (equal (logic.find-proof a (cons b x))
         (if (equal (logic.conclusion b) a)
             b
           (logic.find-proof a x)))
  :hints(("Goal" :in-theory (enable logic.find-proof))))

(defthm logic.find-proof-of-list-fix
  (equal (logic.find-proof a (list-fix x))
         (logic.find-proof a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.find-proof-of-app
  (implies (and (force (logic.appeal-listp x))
                (force (logic.appeal-listp y)))
           (equal (logic.find-proof a (app x y))
                  (or (logic.find-proof a x)
                      (logic.find-proof a y))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm conclusion-of-logic.find-proof
  (implies (logic.find-proof a x)
           (equal (logic.conclusion (logic.find-proof a x))
                  a))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.find-proof-under-iff-when-memberp-of-logic.strip-conclusions
  (implies (and (memberp a (logic.strip-conclusions x))
                (force (logic.appeal-listp x)))
           (iff (logic.find-proof a x)
                t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-memberp-of-logic.strip-conclusions-when-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.appeal-listp x)))
           (equal (memberp a (logic.strip-conclusions x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.appealp-of-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.appeal-listp x)))
           (equal (logic.appealp (logic.find-proof a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.proofp-of-logic.find-proof
  (implies (and (logic.find-proof a x)
                (force (logic.proof-listp x axioms thms atbl)))
           (logic.proofp (logic.find-proof a x) axioms thms atbl))
  :hints(("Goal" :induct (cdr-induction x))))



(defprojection :list (logic.find-proofs x proofs)
               :element (logic.find-proof x proofs)
               :guard (and (logic.formula-listp x)
                           (logic.appeal-listp proofs)))

