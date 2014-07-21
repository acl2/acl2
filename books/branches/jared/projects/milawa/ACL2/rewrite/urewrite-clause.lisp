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
(include-book "urewrite")
(include-book "traces/trace-compiler")
(include-book "../clauses/update-clause-iff-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund rw.urewrite-clause-bldr (x control n traces proof)
  ;; Suppose x is a clause, [T1...Tn], which rewrites to [T1'...Tn'].
  ;; Suppose proof is a proof of T1' v ... v Tn'.
  ;; We prove T1 v ... v Tn.
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (rw.controlp control)
                              (natp n)
                              (equal traces (rw.urewrite-list x t control n))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (clause.clause-formula (rw.trace-list-rhses traces)))))
           (ignore x n))
  (clause.update-clause-iff-bldr (rw.trace-list-rhses traces)
                                 proof
                                 ;; We know that urewrite generates no forced goals, so we can use nil as
                                 ;; our fproofs.
                                 (rw.compile-trace-list traces (rw.control->defs control) nil)))

(defobligations rw.urewrite-clause-bldr
  (rw.compile-trace-list
   clause.update-clause-iff-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-clause-bldr)))

 (defthm forcing-logic.appealp-of-rw.urewrite-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list x t control n))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula (rw.trace-list-rhses traces)))))
            (equal (logic.appealp (rw.urewrite-clause-bldr x control n traces proof))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.urewrite-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list x t control n))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula (rw.trace-list-rhses traces)))))
            (equal (logic.conclusion (rw.urewrite-clause-bldr x control n traces proof))
                   (clause.clause-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.urewrite-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list x t control n))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula (rw.trace-list-rhses traces)))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.urewrite-clause-bldr)
                        ))
            (equal (logic.proofp (rw.urewrite-clause-bldr x control n traces proof) axioms thms atbl)
                   t))))



(defund rw.urewrite-clause-list-bldr (x control n traces proofs)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (rw.controlp control)
                              (natp n)
                              (equal traces (rw.urewrite-list-list x t control n))
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (rw.trace-list-list-rhses traces))))))
  (if (consp x)
      (cons (rw.urewrite-clause-bldr (car x) control n (car traces) (car proofs))
            (rw.urewrite-clause-list-bldr (cdr x) control n (cdr traces) (cdr proofs)))
    nil))

(defobligations rw.urewrite-clause-list-bldr
  (rw.urewrite-clause-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-clause-list-bldr)))

 (defthm forcing-logic.appeal-listp-of-rw.urewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list-list x t control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.trace-list-list-rhses traces)))))
            (equal (logic.appeal-listp (rw.urewrite-clause-list-bldr x control n traces proofs))
                   t))
   :hints(("Goal" :in-theory (enable rw.urewrite-clause-list-bldr))))

 (defthm forcing-logic.strip-conclusions-of-rw.urewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list-list x t control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.trace-list-list-rhses traces)))))
            (equal (logic.strip-conclusions (rw.urewrite-clause-list-bldr x control n traces proofs))
                   (clause.clause-list-formulas x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-rw.urewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (rw.controlp control)
                        (equal traces (rw.urewrite-list-list x t control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.trace-list-list-rhses traces)))
                        ;; ---
                        (logic.term-list-list-atblp x atbl)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.urewrite-clause-list-bldr)))
            (equal (logic.proof-listp (rw.urewrite-clause-list-bldr x control n traces proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.urewrite-clause-list-bldr)))))

