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
(include-book "aux-split-support")
(include-book "aux-split")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.aux-split-bldr (todo done proofs)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo) (consp done))
                              (logic.appeal-listp proofs)
                              (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                                       (logic.strip-conclusions proofs)))
                  :verify-guards nil
                  :measure (clause.split-count-list todo)))
  (if (consp todo)
      (let ((t1 (car todo)))
        (if (clause.negative-termp t1)
            (let ((guts (clause.negative-term-guts t1)))

              (cond ((clause.negative-termp guts)
                     (clause.aux-split-double-negate t1 (cdr todo) done
                                                     (clause.aux-split-bldr (cons (clause.negative-term-guts guts) (cdr todo))
                                                                            done proofs)))
                    ((and (logic.functionp guts)
                          (equal (logic.function-name guts) 'if)
                          (equal (len (logic.function-args guts)) 3))
                     (let ((args (logic.function-args guts)))
                       (let ((a      (first args))
                             (not-a  (logic.function 'not (list (first args))))
                             (not-b  (logic.function 'not (list (second args))))
                             (not-c  (logic.function 'not (list (third args))))
                             (rest   (cdr todo)))
                         (let ((triv1 (clause.aux-split-trivial-branchp not-a not-b rest done))
                               (triv2 (clause.aux-split-trivial-branchp a not-c rest done)))
                           (cond ((and triv1 triv2)
                                  (clause.aux-split-negated-if t1 rest done
                                                               (clause.aux-split-trivial-branch-bldr not-a not-b rest done)
                                                               (clause.aux-split-trivial-branch-bldr a not-c rest done)))
                                 (triv1
                                  (clause.aux-split-negated-if t1 rest done
                                                               (clause.aux-split-trivial-branch-bldr not-a not-b rest done)
                                                               (clause.aux-split-bldr (cons a (cons not-c rest)) done proofs)))
                                 (triv2
                                  (clause.aux-split-negated-if t1 rest done
                                                               (clause.aux-split-bldr (cons not-a (cons not-b rest)) done proofs)
                                                               (clause.aux-split-trivial-branch-bldr a not-c rest done)))
                                 (t
                                  (clause.aux-split-negated-if t1 rest done
                                                               (clause.aux-split-bldr (cons not-a (cons not-b rest)) done proofs)
                                                               (clause.aux-split-bldr (cons a (cons not-c rest)) done proofs))))))))

                    (t
                     (clause.aux-split-negative-default t1 (cdr todo) done
                                                        (clause.aux-split-bldr (cdr todo)
                                                                               (cons (logic.function 'not (list guts)) done)
                                                                               proofs)))))
          (cond ((and (logic.functionp t1)
                      (equal (logic.function-name t1) 'if)
                      (equal (len (logic.function-args t1)) 3))
                 (let ((args (logic.function-args t1)))
                   (let ((a     (first args))
                         (not-a (logic.function 'not (list (first args))))
                         (b     (second args))
                         (c     (third args))
                         (rest  (cdr todo)))
                     (let ((triv1 (clause.aux-split-trivial-branchp not-a b rest done))
                           (triv2 (clause.aux-split-trivial-branchp a c rest done)))
                       (cond ((and triv1 triv2)
                              (clause.aux-split-positive-if t1 rest done
                                                            (clause.aux-split-trivial-branch-bldr not-a b rest done)
                                                            (clause.aux-split-trivial-branch-bldr a c rest done)))
                             (triv1
                              (clause.aux-split-positive-if t1 rest done
                                                            (clause.aux-split-trivial-branch-bldr not-a b rest done)
                                                            (clause.aux-split-bldr (cons a (cons c rest)) done proofs)))
                             (triv2
                              (clause.aux-split-positive-if t1 rest done
                                                            (clause.aux-split-bldr (cons not-a (cons b rest)) done proofs)
                                                            (clause.aux-split-trivial-branch-bldr a c rest done)))
                             (t
                              (clause.aux-split-positive-if t1 rest done
                                                            (clause.aux-split-bldr (cons not-a (cons b rest)) done proofs)
                                                            (clause.aux-split-bldr (cons a (cons c rest)) done proofs))))))))

                (t
                 (clause.aux-split-positive-default t1 (cdr todo) done
                                                    (clause.aux-split-bldr (cdr todo) (cons t1 done) proofs))))))

    (logic.find-proof (clause.clause-formula done) proofs)))

(defobligations clause.aux-split-bldr
  (clause.aux-split-double-negate
   clause.aux-split-negated-if
   clause.aux-split-negative-default
   clause.aux-split-positive-if
   clause.aux-split-positive-default
   clause.aux-split-trivial-branch-bldr))

(encapsulate
 ()
 ;; Now we can carry out the correctness proof entirely using the
 ;; clause.aux-split-goal abstraction. Then, we get rid of it in the final
 ;; conclusion proof, so nobody has to deal with it except us.

 (local (in-theory (enable clause.aux-split-bldr
                           clause.aux-split-goal-when-not-consp-of-todo)))

 (defthm lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr
   (implies (and (logic.term-listp todo)
                 (logic.term-listp done)
                 (or (consp todo) (consp done))
                 (logic.appeal-listp proofs)
                 (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                          (logic.strip-conclusions proofs)))
            (and (logic.appealp (clause.aux-split-bldr todo done proofs))
                 (equal (logic.conclusion (clause.aux-split-bldr todo done proofs))
                        (clause.aux-split-goal todo done))))
   :rule-classes nil
   :hints(("Goal"
           :induct (clause.aux-split-bldr todo done proofs)
           :expand (clause.aux-split todo done))))

 (defthm forcing-logic.appealp-of-clause.aux-split-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.appealp (clause.aux-split-bldr todo done proofs))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr)))))

 ;; We want to keep working with clause.aux-split-goal, for now.
 (defthmd lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.aux-split-bldr todo done proofs))
                   (clause.aux-split-goal todo done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.aux-split-bldr)))))

 (verify-guards clause.aux-split-bldr
                :hints(("Goal"
                        :in-theory (enable lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)
                        :expand (clause.aux-split todo done)
                        )))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                                 (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-atblp todo atbl)
                        (logic.term-list-atblp done atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.aux-split-bldr)
                        ))
            (equal (logic.proofp (clause.aux-split-bldr todo done proofs) axioms thms atbl)
                   t))
   :hints(("Goal"
           :induct (clause.aux-split-bldr todo done proofs)
           :in-theory (enable lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr)
           :expand (clause.aux-split todo done)
           )))

 (defthm forcing-logic.conclusion-of-clause.aux-split-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-split todo done))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.aux-split-bldr todo done proofs))
                   (cond ((and (consp todo)
                               (consp done))
                          (logic.por (clause.clause-formula todo)
                                     (clause.clause-formula done)))
                         ((consp todo)
                          (clause.clause-formula todo))
                         (t
                          (clause.clause-formula done)))))
   :hints(("Goal"
           :in-theory (enable clause.aux-split-goal)
           :use ((:instance lemma-for-forcing-logic.proofp-of-clause.aux-split-bldr))))))






(defund clause.simple-split-bldr (clause proofs)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (clause.simple-split clause))
                                     (logic.strip-conclusions proofs)))
                  :guard-hints (("Goal" :in-theory (enable clause.simple-split)))))
  (clause.aux-split-bldr clause nil proofs))

(defobligations clause.simple-split-bldr
  (clause.aux-split-bldr))

(defthm forcing-logic.appealp-of-clause.simple-split-bldr
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-split clause))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appealp (clause.simple-split-bldr clause proofs))
                   t))
   :hints(("Goal" :in-theory (enable clause.simple-split
                                     clause.simple-split-bldr))))

(defthm forcing-logic.conclusion-of-clause.simple-split-bldr
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-split clause))
                               (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.simple-split-bldr clause proofs))
                   (clause.clause-formula clause)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable clause.simple-split
                                     clause.simple-split-bldr))))

(defthm@ forcing-logic.proofp-of-clause.simple-split-bldr
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-split clause))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-atblp clause atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.simple-split-bldr)
                        ))
            (equal (logic.proofp (clause.simple-split-bldr clause proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable clause.simple-split
                                     clause.simple-split-bldr))))


(defund clause.simple-split-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    ;; Extras holds the input clause to split.
    (and (equal method 'clause.simple-split-bldr)
         (logic.term-listp extras)
         (logic.term-list-atblp extras atbl)
         (consp extras)
         (equal (clause.clause-list-formulas (clause.simple-split extras))
                (logic.strip-conclusions subproofs))
         (equal conclusion
                (clause.clause-formula extras)))))

(defund clause.simple-split-bldr-high (clause proofs)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (clause.simple-split clause))
                                     (logic.strip-conclusions proofs)))))
  (logic.appeal 'clause.simple-split-bldr
                (clause.clause-formula clause)
                (list-fix proofs)
                clause))

(defobligations clause.simple-split-bldr-okp
  (clause.simple-split-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.simple-split-bldr-okp)))

 (defthm booleanp-of-clause.simple-split-bldr-okp
   (equal (booleanp (clause.simple-split-bldr-okp x atbl))
          t))

 (defthm clause.simple-split-bldr-okp-of-logic.appeal-identity
   (equal (clause.simple-split-bldr-okp (logic.appeal-identity x) atbl)
          (clause.simple-split-bldr-okp x atbl)))

 (defthmd lemma-1-for-soundness-of-clause.simple-split-bldr-okp
   (implies (and (clause.simple-split-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (clause.simple-split-bldr (logic.extras x)
                                              (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                           axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.simple-split-bldr-okp
   (implies (and (clause.simple-split-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.simple-split-bldr-okp)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3))
            (equal (logic.proofp
                    (clause.simple-split-bldr (logic.extras x)
                                              (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                           axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.simple-split-bldr-okp
   (implies (and (clause.simple-split-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.simple-split-bldr-okp)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             )))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.simple-split-bldr-okp
                               lemma-2-for-soundness-of-clause.simple-split-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.simple-split-bldr (logic.extras x)
                                                          (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                       axioms thms atbl)))))))))
