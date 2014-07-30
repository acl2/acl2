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


(defund logic.functional-axiom (fn ti si)
  ;; Create the functional axiom instance for fn, ti, and si.
  (declare (xargs :guard (and (logic.function-namep fn)
                              (logic.term-listp ti)
                              (logic.term-listp si)
                              (equal (len ti) (len si)))))
  (logic.disjoin-formulas (fast-app (logic.negate-formulas (logic.pequal-list ti si))
                                    (list (logic.pequal (logic.function fn (list-fix ti))
                                                        (logic.function fn (list-fix si)))))))

(defthm forcing-logic.formulap-of-logic.functional-axiom
  (implies (force (and (logic.function-namep fn)
                       (equal (len ti) (len si))
                       (logic.term-listp ti)
                       (logic.term-listp si)))
           (equal (logic.formulap (logic.functional-axiom fn ti si))
                  t))
  :hints(("Goal" :in-theory (enable logic.functional-axiom))))

(defthm forcing-logic.formula-atblp-of-logic.functional-axiom
  (implies (force (and (logic.function-namep fn)
                       (logic.term-list-atblp ti atbl)
                       (logic.term-list-atblp si atbl)
                       (equal (cdr (lookup fn atbl)) (len ti))
                       (equal (len ti) (len si))))
           (equal (logic.formula-atblp (logic.functional-axiom fn ti si) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.functional-axiom))))



;; We introduce two intermediate functions to bridge the gap between our axiom
;; generator and the checker in proofp.

(defund logic.functional-axiom-alt1 (fn ti si tacc sacc)
  (declare (xargs :verify-guards nil))
  (if (and (consp ti)
           (consp si))
      (logic.por (logic.pnot (logic.pequal (car ti) (car si)))
                 (logic.functional-axiom-alt1 fn (cdr ti) (cdr si) (cons (car ti) tacc) (cons (car si) sacc)))
    (logic.pequal (logic.function fn (rev tacc))
                  (logic.function fn (rev sacc)))))

(defthm logic.check-functional-axiom-of-logic.functional-axiom-alt1
  (implies (and (logic.function-namep fn)
                (equal (len ti) (len si)))
           (equal (logic.check-functional-axiom (logic.functional-axiom-alt1 fn ti si tacc sacc) tacc sacc)
                  t))
  :hints(("Goal"
          :in-theory (enable logic.check-functional-axiom
                             logic.functional-axiom-alt1)
          :induct (logic.functional-axiom-alt1 fn ti si tacc sacc))))

(defund logic.functional-axiom-alt2 (fn ti si tacc sacc)
  (declare (xargs :verify-guards nil))
  (logic.disjoin-formulas
   (app (logic.negate-formulas (logic.pequal-list ti si))
        (list (logic.pequal (logic.function fn (rev (revappend ti tacc)))
                            (logic.function fn (rev (revappend si sacc))))))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm logic.functional-axiom-alt1/alt2-equivalence
   (implies (and (logic.function-namep fn)
                 (equal (len ti) (len si))
                 (true-listp tacc)
                 (true-listp sacc))
            (equal (logic.functional-axiom-alt1 fn ti si tacc sacc)
                   (logic.functional-axiom-alt2 fn ti si tacc sacc)))
   :hints(("Goal"
           :in-theory (e/d (logic.functional-axiom-alt2
                            logic.functional-axiom-alt1)
                           (forcing-logic.formulap-of-logic.pequal
                            forcing-logic.formulap-of-logic.pnot
                            forcing-equal-of-logic.por-rewrite-two
                            forcing-equal-of-logic.por-rewrite))
           :induct (logic.functional-axiom-alt1 fn ti si tacc sacc)))))

(defthm logic.functional-axiom-alt2/main-equivalence
  (implies (and (logic.function-namep fn)
                (equal (len ti) (len si)))
           (equal (logic.functional-axiom-alt2 fn ti si nil nil)
                  (logic.functional-axiom fn ti si)))
  :hints(("Goal" :in-theory (enable logic.functional-axiom-alt2
                                    logic.functional-axiom))))

(defthm forcing-logic.check-functional-axiom-of-logic.functional-axiom
   (implies (force (and (logic.function-namep fn)
                        (equal (len ti) (len si))))
            (equal (logic.check-functional-axiom (logic.functional-axiom fn ti si) nil nil)
                   t))
   :hints(("Goal"
           :use ((:instance logic.check-functional-axiom-of-logic.functional-axiom-alt1
                            (tacc nil)
                            (sacc nil))))))
