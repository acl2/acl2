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
(include-book "level7")
(include-book "../rewrite/ccstep-check")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund level8.step-okp (x defs axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (definition-listp defs)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ;; The ccstep-list-bldr is the most significant new step and subsumes compile-trace
     ;; whenever crewrite is being used.  But we also add rw.compile-trace as a new rule,
     ;; since, for example, urewrite builds traces but does not use ccsteps to rewrite the
     ;; clauses.
     ((equal method 'rw.ccstep-list-bldr)     (rw.ccstep-list-bldr-okp x defs thms atbl))
     ((equal method 'rw.compile-trace)        (rw.compile-trace-okp x defs thms atbl))
     (t
      (level7.step-okp x axioms thms atbl)))))

(defobligations level8.step-okp
  (rw.compile-trace
   rw.ccstep-list-bldr
   level7.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level8.step-okp)))

 (defthm@ soundness-of-level8.step-okp
   (implies (and (level8.step-okp x defs axioms thms atbl)
                 (force (and (logic.appealp x)
                             (logic.formula-list-atblp defs atbl)
                             (definition-listp defs)
                             (subsetp defs axioms)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (@obligations level8.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level8.step-okp-when-level7.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level7.step-okp x axioms thms atbl)
            (level8.step-okp x defs axioms thms atbl))
   :hints(("Goal" :in-theory (enable level7.step-okp
                                     level6.step-okp
                                     level5.step-okp
                                     level4.step-okp
                                     level3.step-okp
                                     level2.step-okp
                                     logic.appeal-step-okp))))

 (defthm level8.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level8.step-okp x defs axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))



(encapsulate
 ()
 (defund level8.flag-proofp-aux (flag x defs axioms thms atbl)
   (declare (xargs :guard (and (if (equal flag 'proof)
                                   (logic.appealp x)
                                 (and (equal flag 'list)
                                      (logic.appeal-listp x)))
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))
                   :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))))
   (if (equal flag 'proof)
       (and (level8.step-okp x defs axioms thms atbl)
            (level8.flag-proofp-aux 'list (logic.subproofs x) defs axioms thms atbl))
     (if (consp x)
         (and (level8.flag-proofp-aux 'proof (car x) defs axioms thms atbl)
              (level8.flag-proofp-aux 'list (cdr x) defs axioms thms atbl))
       t)))

 (definlined level8.proofp-aux (x defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level8.flag-proofp-aux 'proof x defs axioms thms atbl))

 (definlined level8.proof-listp-aux (x defs axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (definition-listp defs)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level8.flag-proofp-aux 'list x defs axioms thms atbl))

 (defthmd definition-of-level8.proofp-aux
   (equal (level8.proofp-aux x defs axioms thms atbl)
          (and (level8.step-okp x defs axioms thms atbl)
               (level8.proof-listp-aux (logic.subproofs x) defs axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level8.proofp-aux level8.proof-listp-aux level8.flag-proofp-aux))))

 (defthmd definition-of-level8.proof-listp-aux
   (equal (level8.proof-listp-aux x defs axioms thms atbl)
          (if (consp x)
              (and (level8.proofp-aux (car x) defs axioms thms atbl)
                   (level8.proof-listp-aux (cdr x) defs axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level8.proofp-aux level8.proof-listp-aux level8.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level8.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level8.proof-listp)))))



(defthm level8.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level8.proofp-aux x defs axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level8.proofp-aux))))

(defthm level8.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level8.proof-listp-aux x defs axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level8.proof-listp-aux))))

(defthm level8.proof-listp-aux-of-cons
  (equal (level8.proof-listp-aux (cons a x) defs axioms thms atbl)
         (and (level8.proofp-aux a defs axioms thms atbl)
              (level8.proof-listp-aux x defs axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level8.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level8.proofp-aux
                (equal (booleanp (level8.proofp-aux x defs axioms thms atbl))
                       t))
         (t booleanp-of-level8.proof-listp-aux
            (equal (booleanp (level8.proof-listp-aux x defs axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level8.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level8.proof-listp-aux (x defs axioms thms atbl)
  (level8.proofp-aux x defs axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level8.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level8.step-okp)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3)
                   (mapp atbl)
                   (logic.formula-list-atblp defs atbl)
                   (definition-listp defs)
                   (subsetp defs axioms))
  :thms ((proof logic.provablep-when-level8.proofp-aux
                (implies (and (logic.appealp x)
                              (level8.proofp-aux x defs axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level8.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level8.proof-listp-aux x defs axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level8.proofp-aux))))


(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level8.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level8.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level8.proofp-aux x defs axioms thms atbl)
                                t)))
         (t level8.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level8.proof-listp-aux x defs axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level8.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level8.proofp-aux-when-logic.proofp
                    level8.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level8.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level8.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level8.proofp-aux (logic.provable-witness formula axioms thms atbl) defs axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level8.proofp-aux-when-logic.proofp))))




(defund@ level8.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'level8.proofp)
         (not subproofs)
         (tuplep 2 extras)
         (let ((defs (first extras))
               (core (second extras)))
           (and
            ;; (1) General requirements for level8.
            (@obligations level8.step-okp)
            (mapp atbl)
            (equal (cdr (lookup 'not atbl)) 1)
            (equal (cdr (lookup 'equal atbl)) 2)
            (equal (cdr (lookup 'iff atbl)) 2)
            (equal (cdr (lookup 'if atbl)) 3)
            ;; (2) Top-level check that the definitions are okay.
            (definition-listp defs)
            (logic.formula-list-atblp defs atbl)
            (subsetp defs axioms)
            ;; (3) Actual proof checking with defs pre-checked and included.
            (logic.appealp core)
            (equal conclusion (logic.conclusion core))
            (level8.proofp-aux core defs axioms thms atbl))))))

(defthm booleanp-of-level8.proofp
  (equal (booleanp (level8.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level8.proofp))))

(defthm logic.provablep-when-level8.proofp
  (implies (and (logic.appealp x)
                (level8.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (e/d (level8.proofp)
                          (logic.provablep-when-level8.proofp-aux))
          :use ((:instance logic.provablep-when-level8.proofp-aux
                           (x    (second (logic.extras x)))
                           (defs (first (logic.extras x))))))))



(defun level8.adapter (proof defs initial-world all-worlds)
  (declare (xargs :mode :program)
           (ignore initial-world all-worlds))
  (logic.appeal 'level8.proofp
                (logic.conclusion proof)
                nil
                (list defs proof)))