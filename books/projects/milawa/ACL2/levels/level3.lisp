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
(include-book "level2")
(include-book "../build/prop-list")
(include-book "../build/disjoined-subset")
(include-book "../build/equal")
(include-book "../build/iff")
(include-book "../build/if")
(include-book "../build/not")
(include-book "../clauses/disjoined-update-clause-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund level3.step-okp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ;; Propositional rules
     ((equal method 'build.modus-ponens-list)                     (build.modus-ponens-list-okp x))
     ((equal method 'build.disjoined-modus-ponens-list)           (build.disjoined-modus-ponens-list-okp x))
     ((equal method 'build.generic-subset)                        (build.generic-subset-okp x atbl))
     ((equal method 'build.multi-assoc-expansion)                 (build.multi-assoc-expansion-okp x atbl))
     ((equal method 'clause.aux-disjoined-update-clause-twiddle)  (clause.aux-disjoined-update-clause-twiddle-okp x atbl))

     ;; Pequal rules
     ((equal method 'build.reflexivity)                           (build.reflexivity-okp x atbl))
     ((equal method 'build.commute-pequal)                        (build.commute-pequal-okp x atbl))
     ((equal method 'build.disjoined-commute-pequal)              (build.disjoined-commute-pequal-okp x atbl))
     ((equal method 'build.commute-not-pequal)                    (build.commute-not-pequal-okp x atbl))
     ((equal method 'build.disjoined-commute-not-pequal)          (build.disjoined-commute-not-pequal-okp x atbl))
     ((equal method 'build.substitute-into-not-pequal)            (build.substitute-into-not-pequal-okp x atbl))
     ((equal method 'build.disjoined-substitute-into-not-pequal)  (build.disjoined-substitute-into-not-pequal-okp x atbl))
     ((equal method 'build.transitivity-of-pequal)                (build.transitivity-of-pequal-okp x atbl))
     ((equal method 'build.disjoined-transitivity-of-pequal)      (build.disjoined-transitivity-of-pequal-okp x atbl))
     ((equal method 'build.not-nil-from-t)                        (build.not-nil-from-t-okp x atbl))
     ((equal method 'build.disjoined-not-nil-from-t)              (build.disjoined-not-nil-from-t-okp x atbl))
     ((equal method 'build.not-t-from-nil)                        (build.not-t-from-nil-okp x atbl))
     ((equal method 'build.disjoined-not-t-from-nil)              (build.disjoined-not-t-from-nil-okp x atbl))

     ;; Equal rules
     ((equal method 'build.equal-reflexivity)                     (build.equal-reflexivity-okp x atbl))
     ((equal method 'build.equal-t-from-not-nil)                  (build.equal-t-from-not-nil-okp x atbl))
     ((equal method 'build.disjoined-equal-t-from-not-nil)        (build.disjoined-equal-t-from-not-nil-okp x atbl))
     ((equal method 'build.equal-nil-from-not-t)                  (build.equal-nil-from-not-t-okp x atbl))
     ((equal method 'build.disjoined-equal-nil-from-not-t)        (build.disjoined-equal-nil-from-not-t-okp x atbl))
     ((equal method 'build.pequal-from-equal)                     (build.pequal-from-equal-okp x atbl))
     ((equal method 'build.disjoined-pequal-from-equal)           (build.disjoined-pequal-from-equal-okp x atbl))
     ((equal method 'build.not-equal-from-not-pequal)             (build.not-equal-from-not-pequal-okp x atbl))
     ((equal method 'build.disjoined-not-equal-from-not-pequal)   (build.disjoined-not-equal-from-not-pequal-okp x atbl))
     ((equal method 'build.commute-equal)                         (build.commute-equal-okp x atbl))
     ((equal method 'build.disjoined-commute-equal)               (build.disjoined-commute-equal-okp x atbl))
     ((equal method 'build.equal-from-pequal)                     (build.equal-from-pequal-okp x atbl))
     ((equal method 'build.disjoined-equal-from-pequal)           (build.disjoined-equal-from-pequal-okp x atbl))
     ((equal method 'build.not-pequal-from-not-equal)             (build.not-pequal-from-not-equal-okp x atbl))
     ((equal method 'build.disjoined-not-pequal-from-not-equal)   (build.disjoined-not-pequal-from-not-equal-okp x atbl))
     ((equal method 'build.transitivity-of-equal)                 (build.transitivity-of-equal-okp x atbl))
     ((equal method 'build.disjoined-transitivity-of-equal)       (build.disjoined-transitivity-of-equal-okp x atbl))
     ((equal method 'build.not-pequal-constants)                  (build.not-pequal-constants-okp x atbl))

     ;; If rules
     ((equal method 'build.if-when-not-nil)                       (build.if-when-not-nil-okp x atbl))
     ((equal method 'build.if-when-nil)                           (build.if-when-nil-okp x atbl))

     ;; Iff rules
     ((equal method 'build.iff-t-from-not-pequal-nil)             (build.iff-t-from-not-pequal-nil-okp x atbl))
     ((equal method 'build.disjoined-iff-t-from-not-pequal-nil)   (build.disjoined-iff-t-from-not-pequal-nil-okp x atbl))
     ((equal method 'build.not-pequal-nil-from-iff-t)             (build.not-pequal-nil-from-iff-t-okp x atbl))
     ((equal method 'build.disjoined-not-pequal-nil-from-iff-t)   (build.disjoined-not-pequal-nil-from-iff-t-okp x atbl))
     ((equal method 'build.iff-t-from-not-nil)                    (build.iff-t-from-not-nil-okp x atbl))
     ((equal method 'build.disjoined-iff-t-from-not-nil)          (build.disjoined-iff-t-from-not-nil-okp x atbl))
     ((equal method 'build.iff-reflexivity)                       (build.iff-reflexivity-okp x atbl))
     ((equal method 'build.commute-iff)                           (build.commute-iff-okp x atbl))
     ((equal method 'build.disjoined-commute-iff)                 (build.disjoined-commute-iff-okp x atbl))
     ((equal method 'build.transitivity-of-iff)                   (build.transitivity-of-iff-okp x atbl))
     ((equal method 'build.disjoined-transitivity-of-iff)         (build.disjoined-transitivity-of-iff-okp x atbl))
     ((equal method 'build.iff-from-pequal)                       (build.iff-from-pequal-okp x atbl))
     ((equal method 'build.disjoined-iff-from-pequal)             (build.disjoined-iff-from-pequal-okp x atbl))
     ((equal method 'build.iff-from-equal)                        (build.iff-from-equal-okp x atbl))
     ((equal method 'build.disjoined-iff-from-equal)              (build.disjoined-iff-from-equal-okp x atbl))

     ;; dead rules now, i think
     ;;((equal method 'build.pequal-nil-from-iff-nil)               (build.pequal-nil-from-iff-nil-okp x atbl))
     ;;((equal method 'build.disjoined-pequal-nil-from-iff-nil)     (build.disjoined-pequal-nil-from-iff-nil-okp x atbl))
     ;;((equal method 'build.not-equal-from-not-iff)                (build.not-equal-from-not-iff-okp x atbl))
     ;;((equal method 'build.iff-nil-from-not-t)                    (build.iff-nil-from-not-t-okp x atbl))
     ;;((equal method 'build.disjoined-iff-nil-from-not-t)          (build.disjoined-iff-nil-from-not-t-okp x atbl))

     ;; Not rules
     ((equal method 'build.disjoined-negative-lit-from-pequal-nil)   (build.disjoined-negative-lit-from-pequal-nil-okp x atbl))
     ((equal method 'build.disjoined-pequal-nil-from-negative-lit)   (build.disjoined-pequal-nil-from-negative-lit-okp x atbl))
     ((equal method 'build.disjoined-iff-when-not-nil)               (build.disjoined-iff-when-not-nil-okp x atbl))

     ;; Extended propositional rules
     ;; Other rules
     (t
      (level2.step-okp x axioms thms atbl)))))

(defobligations level3.step-okp
  (build.modus-ponens-list
   build.disjoined-modus-ponens-list
   build.generic-subset
   build.multi-assoc-expansion
   clause.aux-disjoined-update-clause-twiddle

   build.reflexivity
   build.commute-pequal
   build.disjoined-commute-pequal
   build.commute-not-pequal
   build.disjoined-commute-not-pequal
   build.substitute-into-not-pequal
   build.disjoined-substitute-into-not-pequal
   build.transitivity-of-pequal
   build.disjoined-transitivity-of-pequal
   build.not-nil-from-t
   build.disjoined-not-nil-from-t
   build.not-t-from-nil
   build.disjoined-not-t-from-nil

   build.equal-reflexivity
   build.equal-t-from-not-nil
   build.disjoined-equal-t-from-not-nil
   build.equal-nil-from-not-t
   build.disjoined-equal-nil-from-not-t
   build.pequal-from-equal
   build.disjoined-pequal-from-equal
   build.not-equal-from-not-pequal
   build.disjoined-not-equal-from-not-pequal
   build.commute-equal
   build.disjoined-commute-equal
   build.equal-from-pequal
   build.disjoined-equal-from-pequal
   build.not-pequal-from-not-equal
   build.disjoined-not-pequal-from-not-equal
   build.transitivity-of-equal
   build.disjoined-transitivity-of-equal
   build.not-pequal-constants

   build.if-when-not-nil
   build.if-when-nil

   build.iff-t-from-not-pequal-nil
   build.disjoined-iff-t-from-not-pequal-nil
   build.not-pequal-nil-from-iff-t
   build.disjoined-not-pequal-nil-from-iff-t
   build.iff-t-from-not-nil
   build.disjoined-iff-t-from-not-nil
   build.iff-reflexivity
   build.commute-iff
   build.disjoined-commute-iff
   build.transitivity-of-iff
   build.disjoined-transitivity-of-iff
   build.iff-from-pequal
   build.disjoined-iff-from-pequal
   build.iff-from-equal
   build.disjoined-iff-from-equal

   build.disjoined-negative-lit-from-pequal-nil
   build.disjoined-pequal-nil-from-negative-lit
   build.disjoined-iff-when-not-nil))



(encapsulate
 ()
 (local (in-theory (enable level3.step-okp)))

 (defthm@ soundness-of-level3.step-okp
   (implies (and (logic.appealp x)
                 (level3.step-okp x axioms thms atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3)
                 (@obligations level3.step-okp))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level3.step-okp-when-level2.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level2.step-okp x axioms thms atbl)
            (level3.step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable level2.step-okp logic.appeal-step-okp))))

 (defthm level3.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level3.step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))

(encapsulate
 ()
 (defund level3.flag-proofp-aux (flag x axioms thms atbl)
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
       (and (level3.step-okp x axioms thms atbl)
            (level3.flag-proofp-aux 'list (logic.subproofs x) axioms thms atbl))
     (if (consp x)
         (and (level3.flag-proofp-aux 'proof (car x) axioms thms atbl)
              (level3.flag-proofp-aux 'list (cdr x) axioms thms atbl))
       t)))

 (definlined level3.proofp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level3.flag-proofp-aux 'proof x axioms thms atbl))

 (definlined level3.proof-listp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level3.flag-proofp-aux 'list x axioms thms atbl))

 (defthmd definition-of-level3.proofp-aux
   (equal (level3.proofp-aux x axioms thms atbl)
          (and (level3.step-okp x axioms thms atbl)
               (level3.proof-listp-aux (logic.subproofs x) axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level3.proofp-aux level3.proof-listp-aux level3.flag-proofp-aux))))

 (defthmd definition-of-level3.proof-listp-aux
   (equal (level3.proof-listp-aux x axioms thms atbl)
          (if (consp x)
              (and (level3.proofp-aux (car x) axioms thms atbl)
                   (level3.proof-listp-aux (cdr x) axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level3.proofp-aux level3.proof-listp-aux level3.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level3.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list)))))



(defthm level3.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level3.proofp-aux x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level3.proofp-aux))))

(defthm level3.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level3.proof-listp-aux x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level3.proof-listp-aux))))

(defthm level3.proof-listp-aux-of-cons
  (equal (level3.proof-listp-aux (cons a x) axioms thms atbl)
         (and (level3.proofp-aux a axioms thms atbl)
              (level3.proof-listp-aux x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level3.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level3.proofp-aux
                (equal (booleanp (level3.proofp-aux x axioms thms atbl))
                       t))
         (t booleanp-of-level3.proof-listp-aux
            (equal (booleanp (level3.proof-listp-aux x axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level3.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level3.proof-listp-aux (x axioms thms atbl)
  (level3.proofp-aux x axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level3.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level3.step-okp)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3))
  :thms ((proof logic.provablep-when-level3.proofp-aux
                (implies (and (logic.appealp x)
                              (level3.proofp-aux x axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level3.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level3.proof-listp-aux x axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level3.proofp-aux))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level3.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level3.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level3.proofp-aux x axioms thms atbl)
                                t)))
         (t level3.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level3.proof-listp-aux x axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level3.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level3.proofp-aux-when-logic.proofp
                    level3.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level3.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level3.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level3.proofp-aux (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level3.proofp-aux-when-logic.proofp))))




(definlined@ level3.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (@obligations level3.step-okp)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (level3.proofp-aux x axioms thms atbl)))

(defthm booleanp-of-level3.proofp
  (equal (booleanp (level3.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level3.proofp))))

(defthm logic.provablep-when-level3.proofp
  (implies (and (logic.appealp x)
                (level3.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level3.proofp))))




;; The reflective transition to Level 3.
;;
;; This is a particularly interesting transition because the generic subset
;; builder can be used to replace a whole lot of other builders.

(defund build.generic-subset-high (as bs proof)
  (declare (xargs :guard (and (logic.formula-listp bs)
                              (subsetp as bs)
                              (consp as)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas as)))))
  (if (equal as bs)
      ;; Important optimization since clause cleaning will apply this to each clause,
      ;; and often clauses are unchanged.
      proof
    (logic.appeal 'build.generic-subset
                  (logic.disjoin-formulas bs)
                  (list proof)
                  (list as bs))))

(defund@ build.multi-expansion-high (x as)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp as)
                              (@match (proof x A_i))
                              (memberp (@formula A_i) as))))
  (build.generic-subset-high (@formulas A_i) as x))

(defund@ build.multi-or-expansion-step-high (base as)
  (declare (xargs :guard (and (logic.appealp base)
                              (logic.formula-listp as)
                              (@match (proof base (v P Ai)))
                              (memberp (@formula Ai) as))))
  (build.generic-subset-high (@formulas P Ai) (cons (@formula P) as) base))

(defund@ build.multi-or-expansion-high (base as)
  (declare (xargs :guard (and (logic.appealp base)
                              (logic.formula-listp as)
                              (@match (proof base (v Ai Aj)))
                              (memberp (@formula Ai) as)
                              (memberp (@formula Aj) as))))
  (build.generic-subset-high (@formulas Ai Aj) as base))

(defund build.rev-disjunction-high (x proof)
  (declare (xargs :guard (and (consp x)
                              (logic.formula-listp x)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas x)))))
  (build.generic-subset-high x (fast-rev x) proof))

(defund build.ordered-subset-high (sub sup proof)
  (declare (xargs :guard (and (logic.formula-listp sup)
                              (logic.appealp proof)
                              (consp sub)
                              (ordered-subsetp sub sup)
                              (equal (logic.conclusion proof) (logic.disjoin-formulas sub)))))
  (build.generic-subset-high sub sup proof))

(defund build.disjoined-rev-disjunction-high (x proof)
  (declare (xargs :guard (and (consp x)
                              (logic.formula-listp x)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof))
                                     (logic.disjoin-formulas x)))))
  (let ((P (logic.vlhs (logic.conclusion proof))))
    (build.generic-subset-high (cons P x) (cons P (fast-rev x)) proof)))
