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
(include-book "basic")
(include-book "../build/formula-compiler")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.make-clause-from-arbitrary-formula (x)
  (declare (xargs :guard (logic.formulap x)))
  (list (logic.compile-formula x)))

(defthm consp-of-clause.make-clause-from-arbitrary-formula
  (equal (consp (clause.make-clause-from-arbitrary-formula x))
         t)
  :hints(("Goal" :in-theory (enable clause.make-clause-from-arbitrary-formula))))

(defthm forcing-logic.term-listp-of-clause.make-clause-from-arbitrary-formula
  (implies (force (logic.formulap x))
           (equal (logic.term-listp (clause.make-clause-from-arbitrary-formula x))
                  t))
  :hints(("Goal" :in-theory (enable clause.make-clause-from-arbitrary-formula))))

(defthm forcing-logic.term-list-atblp-of-clause.make-clause-from-arbitrary-formula
  (implies (force (and (logic.formulap x)
                       (logic.formula-atblp x atbl)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-atblp (clause.make-clause-from-arbitrary-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.make-clause-from-arbitrary-formula))))




(defund@ clause.prove-arbitrary-formula-from-its-clause (f proof)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (clause.make-clause-from-arbitrary-formula f))))
                  :verify-guards nil))
  (@derive
   ((v F (= term-f nil))    (@given (second (build.compile-formula f))))
   ((v (= term-f nil) F)    (build.commute-or @-))
   ((!= term-f nil)         (@given proof))
   (F                       (build.modus-ponens-2 @- @--))))

(defobligations clause.prove-arbitrary-formula-from-its-clause
  (build.compile-formula
   build.commute-or
   build.modus-ponens-2))

(encapsulate
 ()
 (local (in-theory (enable clause.prove-arbitrary-formula-from-its-clause
                           clause.make-clause-from-arbitrary-formula
                           logic.term-formula)))

 (verify-guards clause.prove-arbitrary-formula-from-its-clause)

 (defthm forcing-logic.appealp-of-clause.prove-arbitrary-formula-from-its-clause
   (implies (force (and (logic.formulap f)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (clause.make-clause-from-arbitrary-formula f)))))
            (equal (logic.appealp (clause.prove-arbitrary-formula-from-its-clause f proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.prove-arbitrary-formula-from-its-clause
   (implies (force (and (logic.formulap f)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (clause.make-clause-from-arbitrary-formula f)))))
            (equal (logic.conclusion (clause.prove-arbitrary-formula-from-its-clause f proof))
                   f)))

 (defthm@ forcing-logic.proofp-of-clause.prove-arbitrary-formula-from-its-clause
   (implies (force (and (logic.formulap f)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (clause.make-clause-from-arbitrary-formula f)))
                        ;; ---
                        (logic.formula-atblp f atbl)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations clause.prove-arbitrary-formula-from-its-clause)))
            (equal (logic.proofp (clause.prove-arbitrary-formula-from-its-clause f proof) axioms thms atbl)
                   t))))



(defund clause.prove-arbitrary-formula-from-its-clause-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.prove-arbitrary-formula-from-its-clause)
         (not extras)
         (tuplep 1 subproofs)
         (equal (logic.conclusion (car subproofs))
                (clause.clause-formula
                 (clause.make-clause-from-arbitrary-formula conclusion))))))

(defund clause.prove-arbitrary-formula-from-its-clause-high (f proof)
  (DECLARE (XARGS :GUARD (AND (LOGIC.FORMULAP F)
                              (LOGIC.APPEALP PROOF)
                              (EQUAL (LOGIC.CONCLUSION PROOF)
                                     (CLAUSE.CLAUSE-FORMULA
                                      (CLAUSE.MAKE-CLAUSE-FROM-ARBITRARY-FORMULA F))))))
  (logic.appeal 'clause.prove-arbitrary-formula-from-its-clause
                f
                (list proof)
                nil))

(defthm clause.prove-arbitrary-formula-from-its-clause-okp-of-clause.prove-arbitrary-formula-from-its-clause-high
  (implies (AND (LOGIC.FORMULAP F)
                              (LOGIC.APPEALP PROOF)
                              (EQUAL (LOGIC.CONCLUSION PROOF)
                                     (CLAUSE.CLAUSE-FORMULA
                                      (CLAUSE.MAKE-CLAUSE-FROM-ARBITRARY-FORMULA F))))
           (clause.prove-arbitrary-formula-from-its-clause-okp
            (clause.prove-arbitrary-formula-from-its-clause-high f proof)))
  :hints(("Goal"
          :in-theory (enable clause.prove-arbitrary-formula-from-its-clause-okp
                             clause.prove-arbitrary-formula-from-its-clause-high))))

(defthmd hack-for-compile-formula-okp-1
   (implies (force (and (logic.formulap f)
                        (EQUAL (CDR (LOOKUP 'IF ATBL)) 3)
                        (EQUAL (CDR (LOOKUP 'EQUAL ATBL)) 2)))
            (equal (logic.term-atblp (logic.compile-formula f) atbl)
                   (logic.formula-atblp f atbl)))
   :hints(("Goal"
           :induct (logic.compile-formula f)
           :in-theory (e/d (logic.compile-formula)
                           (FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VRHS
                            FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.VLHS
                            FORCING-LOGIC.FORMULA-ATBLP-OF-LOGIC.~ARG
                            FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=RHS
                            FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.=LHS
                            FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.FUNCTION
                            FORCING-LOGIC.TERM-ATBLP-OF-LOGIC.COMPILE-FORMULA))
           :expand ((logic.formula-atblp f atbl)
                    (logic.term-atblp (logic.function 'if
                                                      (LIST (LOGIC.COMPILE-FORMULA (LOGIC.VLHS F))
                                                            ''T
                                                            (LOGIC.COMPILE-FORMULA (LOGIC.VRHS F))))
                                      atbl)
                    (logic.term-atblp (LOGIC.FUNCTION 'IF
                                                      (CONS (LOGIC.COMPILE-FORMULA (LOGIC.~ARG F))
                                                            '('NIL 'T)))
                                      atbl)
                    (logic.term-atblp (LOGIC.FUNCTION 'EQUAL
                                                      (LIST (LOGIC.=LHS F) (LOGIC.=RHS F)))
                                      atbl)))))

(encapsulate
  ()
  (local (acl2::allow-fertilize t))
  (defthmd hack-for-compile-formula-okp-2
    (implies (and (clause.prove-arbitrary-formula-from-its-clause-okp x)
                  (logic.appealp x)
                  (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                  (equal (cdr (lookup 'equal atbl)) 2)
                  (equal (cdr (lookup 'if atbl)) 3))
             (logic.formula-atblp (logic.conclusion x) atbl))
    :hints(("Goal"
            :in-theory (e/d (clause.make-clause-from-arbitrary-formula
                             clause.prove-arbitrary-formula-from-its-clause-okp
                             logic.term-formula)
                            (lOGIC.FORMULA-ATBLP-WHEN-LOGIC.PROVABLEP
                             LOGIC.FORMULA-LIST-ATBLP-OF-WHEN-LOGIC.PROVABLE-LISTP
                             hack-for-compile-formula-okp-1
                             (:executable-counterpart acl2::force)))
            :use ((:instance LOGIC.FORMULA-ATBLP-WHEN-LOGIC.PROVABLEP
                             (x (logic.conclusion (car (logic.subproofs x)))))
                  (:instance hack-for-compile-formula-okp-1
                             (f (logic.conclusion x))))))))

(encapsulate
 ()
 (local (in-theory (enable clause.prove-arbitrary-formula-from-its-clause-okp)))

 (defthm booleanp-of-clause.prove-arbitrary-formula-from-its-clause-okp
   (equal (booleanp (clause.prove-arbitrary-formula-from-its-clause-okp x))
          t)
   :hints(("Goal" :in-theory (e/d (clause.prove-arbitrary-formula-from-its-clause-okp)
                                  ((:executable-counterpart ACL2::force))))))

 (defthm clause.prove-arbitrary-formula-from-its-clause-okp-of-logic.appeal-identity
   (equal (clause.prove-arbitrary-formula-from-its-clause-okp (logic.appeal-identity x))
          (clause.prove-arbitrary-formula-from-its-clause-okp x))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
   (implies (and (clause.prove-arbitrary-formula-from-its-clause-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (clause.prove-arbitrary-formula-from-its-clause
                     (logic.conclusion x)
                     (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                             axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
   (implies (and (clause.prove-arbitrary-formula-from-its-clause-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.prove-arbitrary-formula-from-its-clause)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3)
                 )
            (equal (logic.proofp
                    (clause.prove-arbitrary-formula-from-its-clause
                     (logic.conclusion x)
                     (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                             axioms thms atbl))
                    axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable hack-for-compile-formula-okp-2))))

 (defthm@ forcing-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
   (implies (and (clause.prove-arbitrary-formula-from-its-clause-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.prove-arbitrary-formula-from-its-clause)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp
                               lemma-2-for-soundness-of-clause.prove-arbitrary-formula-from-its-clause-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.prove-arbitrary-formula-from-its-clause
                                 (logic.conclusion x)
                                 (logic.provable-witness (logic.conclusion (car (logic.subproofs x)))
                                                         axioms thms atbl)))))))))






(defprojection :list (clause.make-clauses-from-arbitrary-formulas x)
               :element (clause.make-clause-from-arbitrary-formula x)
               :guard (logic.formula-listp x)
               :nil-preservingp nil)

(defthm consp-listp-of-clause.make-clauses-from-arbitrary-formulas
  (equal (cons-listp (clause.make-clauses-from-arbitrary-formulas x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-clause.make-clauses-from-arbitrary-formulas
  (implies (force (logic.formula-listp x))
           (equal (logic.term-list-listp (clause.make-clauses-from-arbitrary-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-clause.make-clauses-from-arbitrary-formulas
  (implies (force (and (logic.formula-listp x)
                       (logic.formula-list-atblp x atbl)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-list-atblp (clause.make-clauses-from-arbitrary-formulas x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.make-clauses-from-arbitrary-formulas))))




(defund clause.prove-arbitrary-formulas-from-their-clauses (fs proofs)
  (declare (xargs :guard (and (logic.formula-listp fs)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (clause.make-clauses-from-arbitrary-formulas fs))))))
  (if (consp fs)
      (cons (clause.prove-arbitrary-formula-from-its-clause (car fs) (car proofs))
            (clause.prove-arbitrary-formulas-from-their-clauses (cdr fs) (cdr proofs)))
    nil))

(defobligations clause.prove-arbitrary-formulas-from-their-clauses
  (clause.prove-arbitrary-formula-from-its-clause))

(encapsulate
 ()
 (local (in-theory (enable clause.prove-arbitrary-formulas-from-their-clauses)))

 (defthm forcing-logic.appeal-listp-of-clause.prove-arbitrary-formulas-from-their-clauses
   (implies (force (and (logic.formula-listp fs)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.make-clauses-from-arbitrary-formulas fs)))))
            (equal (logic.appeal-listp (clause.prove-arbitrary-formulas-from-their-clauses fs proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-clause.prove-arbitrary-formulas-from-their-clauses
   (implies (force (and (logic.formula-listp fs)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.make-clauses-from-arbitrary-formulas fs)))))
            (equal (logic.strip-conclusions (clause.prove-arbitrary-formulas-from-their-clauses fs proofs))
                   (list-fix fs))))

 (defthm@ forcing-logic.proofp-of-clause.prove-arbitrary-formulas-from-their-clauses
   (implies (force (and (logic.formula-listp fs)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.make-clauses-from-arbitrary-formulas fs)))
                        ;; ---
                        (logic.formula-list-atblp fs atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations clause.prove-arbitrary-formulas-from-their-clauses)))
            (equal (logic.proof-listp (clause.prove-arbitrary-formulas-from-their-clauses fs proofs) axioms thms atbl)
                   t))))
