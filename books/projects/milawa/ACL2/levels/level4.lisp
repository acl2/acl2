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
(include-book "level3")
(include-book "../rewrite/ccsteps")
(include-book "../rewrite/traces/trace-arities")
(include-book "../clauses/aux-split-support")
(include-book "../clauses/aux-limsplit-bldr")
(include-book "../clauses/if-lifting/casesplit-bldr")
(include-book "../clauses/update-clause-bldr")
(include-book "../clauses/compiler")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund level4.step-okp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ;; Clause basics
     ((equal method 'clause.substitute-iff-into-literal-bldr)            (clause.substitute-iff-into-literal-bldr-okp x atbl))
     ((equal method 'clause.disjoined-substitute-iff-into-literal-bldr)  (clause.disjoined-substitute-iff-into-literal-bldr-okp x atbl))
     ((equal method 'clause.standardize-negative-term-bldr)              (clause.standardize-negative-term-bldr-okp x atbl))
     ((equal method 'clause.standardize-double-negative-term-bldr)       (clause.standardize-double-negative-term-bldr-okp x atbl))

     ;; Aux split
     ((equal method 'clause.aux-split-double-negate-lemma1-bldr)         (clause.aux-split-double-negate-lemma1-bldr-okp x atbl))
     ((equal method 'clause.aux-split-double-negate-lemma2-bldr)         (clause.aux-split-double-negate-lemma2-bldr-okp x atbl))
     ((equal method 'clause.aux-split-positive-bldr)                     (clause.aux-split-positive-bldr-okp x atbl))
     ((equal method 'clause.aux-split-positive-1-bldr)                   (clause.aux-split-positive-1-bldr-okp x atbl))
     ((equal method 'clause.aux-split-positive-2-bldr)                   (clause.aux-split-positive-2-bldr-okp x atbl))
     ((equal method 'clause.aux-split-negative-bldr)                     (clause.aux-split-negative-bldr-okp x atbl))
     ((equal method 'clause.disjoined-aux-split-negative-bldr)           (clause.disjoined-aux-split-negative-bldr-okp x atbl))
     ;((equal method 'clause.aux-split-negative-1-bldr)                   (clause.aux-split-negative-1-bldr-okp x))
     ;((equal method 'clause.aux-split-negative-2-bldr)                   (clause.aux-split-negative-2-bldr-okp x))
     ((equal method 'clause.aux-split-default-1-bldr)                    (clause.aux-split-default-1-bldr-okp x atbl))
     ((equal method 'clause.aux-split-default-2-bldr)                    (clause.aux-split-default-2-bldr-okp x atbl))
     ((equal method 'clause.limsplit-cutoff-bldr-nice)                   (clause.limsplit-cutoff-bldr-nice-okp x))

     ;; Case splitting
     ((equal method 'clause.cases-lemma1-bldr)                       (clause.cases-lemma1-bldr-okp x atbl))
     ((equal method 'clause.disjoined-cases-lemma1-bldr)             (clause.disjoined-cases-lemma1-bldr-okp x atbl))

     ;; Update clause
     ((equal method 'clause.aux-update-clause-lemma1-bldr)               (clause.aux-update-clause-lemma1-bldr-okp x atbl))
     ((equal method 'clause.aux-update-clause-lemma2-bldr)               (clause.aux-update-clause-lemma2-bldr-okp x atbl))
     ((equal method 'clause.aux-update-clause-iff-lemma1-bldr)           (clause.aux-update-clause-iff-lemma1-bldr-okp x atbl))
     ((equal method 'clause.aux-update-clause-iff-lemma2-bldr)           (clause.aux-update-clause-iff-lemma2-bldr-okp x atbl))

     ;; Ccstep lemmas
     ((equal method 'rw.ccstep-lemma-1)                                  (rw.ccstep-lemma-1-okp x atbl))
     ((equal method 'rw.ccstep-lemma-2)                                  (rw.ccstep-lemma-2-okp x atbl))
     ((equal method 'rw.ccstep-lemma-3)                                  (rw.ccstep-lemma-3-okp x atbl))
     ((equal method 'rw.ccstep-lemma-4)                                  (rw.ccstep-lemma-4-okp x atbl))

     ;; Clean clauses
     ((equal method 'clause.obvious-term-bldr)                           (clause.obvious-term-bldr-okp x atbl))

     ;; Eval
     ((equal method 'eval-lemma-1-bldr)                                  (eval-lemma-1-bldr-okp x atbl))
     ((equal method 'eval-lemma-2-bldr)                                  (eval-lemma-2-bldr-okp x atbl))

     ;; Rewrite rules
     ((equal method 'rw.compile-crewrite-rule-trace-lemma1)              (rw.compile-crewrite-rule-trace-lemma1-okp x thms atbl))
     ((equal method 'rw.compile-crewrite-rule-trace-lemma2)              (rw.compile-crewrite-rule-trace-lemma2-okp x thms atbl))

     ;; Factor
     ((equal method 'clause.factor-bldr-lemma-1)                         (clause.factor-bldr-lemma-1-okp x atbl))
     ((equal method 'clause.factor-bldr-lemma-2)                         (clause.factor-bldr-lemma-2-okp x atbl))

     ;; Equal by args
     ((equal method 'build.equal-by-args)                                (build.equal-by-args-okp x atbl))
     ((equal method 'build.disjoined-equal-by-args)                      (build.disjoined-equal-by-args-okp x atbl))

     ;; Compiling formulas
     ((equal method 'clause.prove-arbitrary-formula-from-its-clause)
      (clause.prove-arbitrary-formula-from-its-clause-okp x))

     (t
      (level3.step-okp x axioms thms atbl)))))

(defobligations level4.step-okp
  (clause.substitute-iff-into-literal-bldr
   clause.disjoined-substitute-iff-into-literal-bldr
   clause.standardize-negative-term-bldr
   clause.standardize-double-negative-term-bldr

   clause.aux-split-double-negate-lemma1-bldr
   clause.aux-split-double-negate-lemma2-bldr
   clause.aux-split-positive-bldr
   clause.aux-split-positive-1-bldr
   clause.aux-split-positive-2-bldr
   clause.aux-split-negative-bldr
   clause.disjoined-aux-split-negative-bldr
;   clause.aux-split-negative-1-bldr
;   clause.aux-split-negative-2-bldr
   clause.aux-split-default-1-bldr
   clause.aux-split-default-2-bldr
   clause.limsplit-cutoff-bldr-nice-okp

   clause.cases-lemma1-bldr
   clause.disjoined-cases-lemma1-bldr

   clause.aux-update-clause-lemma1-bldr
   clause.aux-update-clause-lemma2-bldr
   clause.aux-update-clause-iff-lemma1-bldr
   clause.aux-update-clause-iff-lemma2-bldr

   rw.ccstep-lemma-1
   rw.ccstep-lemma-2
   rw.ccstep-lemma-3
   rw.ccstep-lemma-4

   clause.obvious-term-bldr

   eval-lemma-1-bldr
   eval-lemma-2-bldr

   rw.compile-crewrite-rule-trace-lemma1
   rw.compile-crewrite-rule-trace-lemma2

   clause.factor-bldr-lemma-1
   clause.factor-bldr-lemma-2

   build.equal-by-args
   build.disjoined-equal-by-args

   clause.prove-arbitrary-formula-from-its-clause

   level3.step-okp))


(encapsulate
 ()
 (local (in-theory (enable level4.step-okp)))

 (defthm@ soundness-of-level4.step-okp
   (implies (and (level4.step-okp x axioms thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (@obligations level4.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level4.step-okp-when-level3.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level3.step-okp x axioms thms atbl)
            (level4.step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable level3.step-okp level2.step-okp logic.appeal-step-okp))))

 (defthm level4.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level4.step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))

(encapsulate
 ()
 (defund level4.flag-proofp-aux (flag x axioms thms atbl)
   (declare (xargs :guard (and (if (equal flag 'proof)
                                   (logic.appealp x)
                                 (and (equal flag 'list)
                                      (logic.appeal-listp x)))
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))
                   :measure (two-nats-measure (rank x)
                                              (if (equal flag 'proof) 1 0))))
   (if (equal flag 'proof)
       (and (level4.step-okp x axioms thms atbl)
            (level4.flag-proofp-aux 'list (logic.subproofs x) axioms thms atbl))
     (if (consp x)
         (and (level4.flag-proofp-aux 'proof (car x) axioms thms atbl)
              (level4.flag-proofp-aux 'list (cdr x) axioms thms atbl))
       t)))

 (definlined level4.proofp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level4.flag-proofp-aux 'proof x axioms thms atbl))

 (definlined level4.proof-listp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level4.flag-proofp-aux 'list x axioms thms atbl))

 (defthmd definition-of-level4.proofp-aux
   (equal (level4.proofp-aux x axioms thms atbl)
          (and (level4.step-okp x axioms thms atbl)
               (level4.proof-listp-aux (logic.subproofs x) axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level4.proofp-aux level4.proof-listp-aux level4.flag-proofp-aux))))

 (defthmd definition-of-level4.proof-listp-aux
   (equal (level4.proof-listp-aux x axioms thms atbl)
          (if (consp x)
              (and (level4.proofp-aux (car x) axioms thms atbl)
                   (level4.proof-listp-aux (cdr x) axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level4.proofp-aux level4.proof-listp-aux level4.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level4.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list)))))



(defthm level4.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level4.proofp-aux x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level4.proofp-aux))))

(defthm level4.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level4.proof-listp-aux x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level4.proof-listp-aux))))

(defthm level4.proof-listp-aux-of-cons
  (equal (level4.proof-listp-aux (cons a x) axioms thms atbl)
         (and (level4.proofp-aux a axioms thms atbl)
              (level4.proof-listp-aux x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level4.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level4.proofp-aux
                (equal (booleanp (level4.proofp-aux x axioms thms atbl))
                       t))
         (t booleanp-of-level4.proof-listp-aux
            (equal (booleanp (level4.proof-listp-aux x axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level4.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level4.proof-listp-aux (x axioms thms atbl)
  (level4.proofp-aux x axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level4.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level4.step-okp)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3))
  :thms ((proof logic.provablep-when-level4.proofp-aux
                (implies (and (logic.appealp x)
                              (level4.proofp-aux x axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level4.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level4.proof-listp-aux x axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level4.proofp-aux))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level4.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level4.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level4.proofp-aux x axioms thms atbl)
                                t)))
         (t level4.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level4.proof-listp-aux x axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level4.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level4.proofp-aux-when-logic.proofp
                    level4.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level4.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level4.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level4.proofp-aux (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level4.proofp-aux-when-logic.proofp))))



(definlined@ level4.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (@obligations level4.step-okp)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (level4.proofp-aux x axioms thms atbl)))

(defthm booleanp-of-level4.proofp
  (equal (booleanp (level4.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level4.proofp))))

(defthm logic.provablep-when-level4.proofp
  (implies (and (logic.appealp x)
                (level4.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level4.proofp))))

