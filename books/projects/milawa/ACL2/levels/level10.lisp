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
(include-book "level9")
(include-book "../tactics/crewrite-world")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund level10.step-okp (x worlds defs axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (tactic.world-listp worlds)
                              (definition-listp defs)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ((equal method 'rw.crewrite-clause-plan-compiler)
      (rw.crewrite-clause-plan-compiler-okp x worlds atbl))
     (t
      (level9.step-okp x worlds defs axioms thms atbl)))))

(defobligations level10.step-okp
  (rw.crewrite-clause-plan-compiler
   level9.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level10.step-okp)))

 (defthm@ soundness-of-level10.step-okp
   (implies (and (level10.step-okp x worlds defs axioms thms atbl)
                 (force (and (logic.appealp x)
                             (tactic.world-listp worlds)
                             (tactic.world-list-atblp worlds atbl)
                             (tactic.world-list-env-okp worlds axioms thms)
                             (logic.formula-list-atblp defs atbl)
                             (definition-listp defs)
                             (subsetp defs axioms)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (@obligations level10.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level10.step-okp-when-level9.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level9.step-okp x worlds defs axioms thms atbl)
            (level10.step-okp x worlds defs axioms thms atbl))
   :hints(("Goal" :in-theory (enable level9.step-okp
                                     level8.step-okp
                                     level7.step-okp
                                     level6.step-okp
                                     level5.step-okp
                                     level4.step-okp
                                     level3.step-okp
                                     level2.step-okp
                                     logic.appeal-step-okp))))

 (defthm level10.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level10.step-okp x worlds defs axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))


(encapsulate
 ()
(defund level10.flag-proofp-aux (flag x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (if (equal flag 'proof)
                                   (logic.appealp x)
                                 (and (equal flag 'list)
                                      (logic.appeal-listp x)))
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))
                   :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))))
   (if (equal flag 'proof)
       (and (level10.step-okp x worlds defs axioms thms atbl)
            (level10.flag-proofp-aux 'list (logic.subproofs x) worlds defs axioms thms atbl))
     (if (consp x)
         (and (level10.flag-proofp-aux 'proof (car x) worlds defs axioms thms atbl)
              (level10.flag-proofp-aux 'list (cdr x) worlds defs axioms thms atbl))
       t)))

(definlined level10.proofp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level10.flag-proofp-aux 'proof x worlds defs axioms thms atbl))

(definlined level10.proof-listp-aux (x worlds defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (tactic.world-listp worlds)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level10.flag-proofp-aux 'list x worlds defs axioms thms atbl))

(defthmd definition-of-level10.proofp-aux
   (equal (level10.proofp-aux x worlds defs axioms thms atbl)
          (and (level10.step-okp x worlds defs axioms thms atbl)
               (level10.proof-listp-aux (logic.subproofs x) worlds defs axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level10.proofp-aux level10.proof-listp-aux level10.flag-proofp-aux))))

(defthmd definition-of-level10.proof-listp-aux
   (equal (level10.proof-listp-aux x worlds defs axioms thms atbl)
          (if (consp x)
              (and (level10.proofp-aux (car x) worlds defs axioms thms atbl)
                   (level10.proof-listp-aux (cdr x) worlds defs axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level10.proofp-aux level10.proof-listp-aux level10.flag-proofp-aux))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition level10.proofp-aux))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition level10.proof-listp)))))



(defthm level10.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level10.proofp-aux x worlds defs axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level10.proofp-aux))))

(defthm level10.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level10.proof-listp-aux x worlds defs axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level10.proof-listp-aux))))

(defthm level10.proof-listp-aux-of-cons
  (equal (level10.proof-listp-aux (cons a x) worlds defs axioms thms atbl)
         (and (level10.proofp-aux a worlds defs axioms thms atbl)
              (level10.proof-listp-aux x worlds defs axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level10.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level10.proofp-aux
                (equal (booleanp (level10.proofp-aux x worlds defs axioms thms atbl))
                       t))
         (t booleanp-of-level10.proof-listp-aux
            (equal (booleanp (level10.proof-listp-aux x worlds defs axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level10.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level10.proof-listp-aux (x worlds defs axioms thms atbl)
  (level10.proofp-aux x worlds defs axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level10.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level10.step-okp)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3)
                   (logic.formula-list-atblp defs atbl)
                   (definition-listp defs)
                   (subsetp defs axioms)
                   (mapp atbl)
                   (tactic.world-listp worlds)
                   (tactic.world-list-atblp worlds atbl)
                   (tactic.world-list-env-okp worlds axioms thms)
                   )
  :thms ((proof logic.provablep-when-level10.proofp-aux
                (implies (and (logic.appealp x)
                              (level10.proofp-aux x worlds defs axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level10.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level10.proof-listp-aux x worlds defs axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level10.proofp-aux))))


(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level10.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level10.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level10.proofp-aux x worlds defs axioms thms atbl)
                                t)))
         (t level10.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level10.proof-listp-aux x worlds defs axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level10.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level10.proofp-aux-when-logic.proofp
                    level10.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level10.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level10.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level10.proofp-aux (logic.provable-witness formula axioms thms atbl) worlds defs axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level10.proofp-aux-when-logic.proofp))))


;; The level 10 adapter trace will be named level10.proofp and will have, as its extras,
;; a list of the form (defs worlds core).

(defun@ level10.static-checksp (worlds defs axioms thms atbl)
  ;; NOTE!  We leave this enabled!
  (declare (xargs :guard (and (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (mapp atbl)
       (@obligations level10.step-okp)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (definition-listp defs)
       (logic.fast-arities-okp (logic.formula-list-arities defs nil) atbl)
       (ordered-list-subsetp (mergesort defs) (mergesort axioms))
       (tactic.world-listp worlds)
       (tactic.fast-world-list-atblp worlds atbl)
       (tactic.fast-world-list-env-okp worlds axioms thms)))

(defund@ level10.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'level10.proofp)
         (not subproofs)
         (tuplep 3 extras)
         (let ((defs   (first extras))
               (worlds (second extras))
               (core   (third extras)))
           (and
            (ACL2::time$ (level10.static-checksp worlds defs axioms thms atbl))
            (logic.appealp core)
            (equal conclusion (logic.conclusion core))
            (level10.proofp-aux core worlds defs axioms thms atbl))))))

(defthm booleanp-of-level10.proofp
  (equal (booleanp (level10.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level10.proofp))))

(defthm logic.provablep-when-level10.proofp
  (implies (and (logic.appealp x)
                (level10.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (e/d (level10.proofp)
                          (logic.provablep-when-level10.proofp-aux))
          :use ((:instance logic.provablep-when-level10.proofp-aux
                           (x      (third (logic.extras x)))
                           (defs   (first (logic.extras x)))
                           (worlds (second (logic.extras x))))))))

(defun level10.adapter (proof defs initial-world all-worlds)
  (declare (xargs :mode :program)
           (ignore initial-world))
  (logic.appeal 'level10.proofp
                (logic.conclusion proof)
                nil
                (list defs all-worlds proof)))

