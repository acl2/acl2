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
(include-book "../build/prop")
(include-book "../clauses/prop")
(include-book "../rewrite/prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund level2.step-okp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond ((equal method 'build.commute-or)                     (build.commute-or-okp x atbl))
          ((equal method 'build.right-expansion)                (build.right-expansion-okp x atbl))
          ((equal method 'build.modus-ponens)                   (build.modus-ponens-okp x atbl))
          ((equal method 'build.modus-ponens-2)                 (build.modus-ponens-2-okp x atbl))
          ((equal method 'build.right-associativity)            (build.right-associativity-okp x atbl))
          ((equal method 'build.disjoined-left-expansion)       (build.disjoined-left-expansion-okp x atbl))
          ((equal method 'build.disjoined-right-expansion)      (build.disjoined-right-expansion-okp x atbl))
          ((equal method 'build.disjoined-contraction)          (build.disjoined-contraction-okp x atbl))
          ((equal method 'build.cancel-neg-neg)                 (build.cancel-neg-neg-okp x atbl))
          ((equal method 'build.insert-neg-neg)                 (build.insert-neg-neg-okp x atbl))
          ((equal method 'build.lhs-insert-neg-neg)             (build.lhs-insert-neg-neg-okp x atbl))
          ((equal method 'build.merge-negatives)                (build.merge-negatives-okp x atbl))
          ((equal method 'build.merge-implications)             (build.merge-implications-okp x atbl))
          ((equal method 'build.disjoined-commute-or)           (build.disjoined-commute-or-okp x atbl))
          ((equal method 'build.disjoined-right-associativity)  (build.disjoined-right-associativity-okp x atbl))
          ((equal method 'build.disjoined-associativity)        (build.disjoined-associativity-okp x atbl))
          ((equal method 'build.disjoined-cut)                  (build.disjoined-cut-okp x atbl))
          ((equal method 'build.disjoined-modus-ponens)         (build.disjoined-modus-ponens-okp x atbl))
          ((equal method 'build.disjoined-modus-ponens-2)       (build.disjoined-modus-ponens-2-okp x atbl))
          ((equal method 'build.lhs-commute-or-then-rassoc)     (build.lhs-commute-or-then-rassoc-okp x atbl))
          ((equal method 'rw.crewrite-twiddle-bldr)             (rw.crewrite-twiddle-bldr-okp x atbl))
          ((equal method 'rw.crewrite-twiddle2-bldr)            (rw.crewrite-twiddle2-bldr-okp x atbl))
          ((equal method 'clause.aux-split-twiddle)             (clause.aux-split-twiddle-okp x atbl))
          ((equal method 'clause.aux-split-twiddle2)            (clause.aux-split-twiddle2-okp x atbl))
          ((equal method 'clause.aux-split-default-3-bldr)      (clause.aux-split-default-3-bldr-okp x atbl))
          ((equal method 'clause.aux-limsplit-cutoff-step-bldr) (clause.aux-limsplit-cutoff-step-bldr-okp x atbl))
          (t
           (logic.appeal-step-okp x axioms thms atbl)))))


(encapsulate
 ()
 (local (in-theory (enable level2.step-okp)))

 (defthm soundness-of-level2.step-okp
   (implies (and (logic.appealp x)
                 (level2.step-okp x axioms thms atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level2.step-okp-when-logic.appeal-step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (logic.appeal-step-okp x axioms thms atbl)
            (level2.step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

 (defthm level2.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level2.step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))

(encapsulate
 ()
 (defund level2.flag-proofp (flag x axioms thms atbl)
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
       (and (level2.step-okp x axioms thms atbl)
            (level2.flag-proofp 'list (logic.subproofs x) axioms thms atbl))
     (if (consp x)
         (and (level2.flag-proofp 'proof (car x) axioms thms atbl)
              (level2.flag-proofp 'list (cdr x) axioms thms atbl))
       t)))

 (definlined level2.proofp (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level2.flag-proofp 'proof x axioms thms atbl))

 (definlined level2.proof-listp (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level2.flag-proofp 'list x axioms thms atbl))

 (defthmd definition-of-level2.proofp
   (equal (level2.proofp x axioms thms atbl)
          (and (level2.step-okp x axioms thms atbl)
               (level2.proof-listp (logic.subproofs x) axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level2.proofp level2.proof-listp level2.flag-proofp))))

 (defthmd definition-of-level2.proof-listp
   (equal (level2.proof-listp x axioms thms atbl)
          (if (consp x)
              (and (level2.proofp (car x) axioms thms atbl)
                   (level2.proof-listp (cdr x) axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level2.proofp level2.proof-listp level2.flag-proofp))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level2.proofp))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list)))))


(defthm level2.proofp-when-not-consp
  (implies (not (consp x))
           (equal (level2.proofp x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level2.proofp))))

(defthm level2.proof-listp-when-not-consp
  (implies (not (consp x))
           (equal (level2.proof-listp x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level2.proof-listp))))

(defthm level2.proof-listp-of-cons
  (equal (level2.proof-listp (cons a x) axioms thms atbl)
         (and (level2.proofp a axioms thms atbl)
              (level2.proof-listp x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level2.proof-listp))))

(defthms-flag
  :thms ((proof booleanp-of-level2.proofp
                (equal (booleanp (level2.proofp x axioms thms atbl))
                       t))
         (t booleanp-of-level2.proof-listp
            (equal (booleanp (level2.proof-listp x axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level2.proofp)
          :induct (logic.appeal-induction flag x))))

(deflist level2.proof-listp (x axioms thms atbl)
  (level2.proofp x axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level2.proofp is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :thms ((proof logic.provablep-when-level2.proofp
                (implies (and (logic.appealp x)
                              (level2.proofp x axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level2.proof-listp
            (implies (and (logic.appeal-listp x)
                          (level2.proof-listp x axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level2.proofp))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level2.proofp is "strictly more capable" than logic.proofp.
  ;;
  ;; WARNING: THESE THEOREMS MUST BE LEFT DISABLED!
  ;;
  ;; Suppose this rule is enabled, and we are trying to prove (level2.proofp X
  ;; ...)  Using this rule, we backchain and try to show (logic.proofp X ...),
  ;; which causes our forcing rules to kick in and assert that the subproofs of
  ;; X are acceptable using logic.proofp.
  ;;
  ;; But this is horrible; if any of the subproofs are derived rules that only
  ;; level2.proofp understands, we end up stuck in forcing rounds that we cannot
  ;; relieve.  So, we should always be reasoning about some single layer and
  ;; never about previous layers.
  :thms ((proof level2.proofp-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level2.proofp x axioms thms atbl)
                                t)))
         (t level2.proof-listp-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level2.proof-listp x axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level2.proofp
                              definition-of-logic.proofp))))

(in-theory (disable level2.proofp-when-logic.proofp
                    level2.proof-listp-when-logic.proof-listp))

(defthm forcing-level2.proofp-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level2.proofp.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level2.proofp (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level2.proofp-when-logic.proofp))))

