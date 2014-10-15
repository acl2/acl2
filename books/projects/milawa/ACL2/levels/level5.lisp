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
(include-book "level4")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund level5.step-okp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method (logic.method x)))
    (cond
     ((equal method 'rw.eqtrace-bldr)                                         (rw.eqtrace-bldr-okp x atbl))
     ((equal method 'rw.eqtrace-contradiction-bldr)                           (rw.eqtrace-contradiction-bldr-okp x atbl))
     ((equal method 'clause.update-clause-bldr)                               (clause.update-clause-bldr-okp x))
     ((equal method 'clause.update-clause-iff-bldr)                           (clause.update-clause-iff-bldr-okp x))
     ((equal method 'clause.disjoined-update-clause-bldr)                     (clause.disjoined-update-clause-bldr-okp x))
     ((equal method 'build.lambda-pequal-by-args)                             (build.lambda-pequal-by-args-okp x atbl))
     ((equal method 'build.disjoined-lambda-pequal-by-args)                   (build.disjoined-lambda-pequal-by-args-okp x atbl))
     ((equal method 'clause.aux-split-negative-1-bldr)                        (clause.aux-split-negative-1-bldr-okp x atbl))
     ((equal method 'clause.aux-split-negative-2-bldr)                        (clause.aux-split-negative-2-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-equal-if-specialcase-nil-bldr)            (rw.iff-implies-equal-if-specialcase-nil-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-iff-if-specialcase-nil-bldr)              (rw.iff-implies-iff-if-specialcase-nil-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-equal-if-specialcase-t-bldr)              (rw.iff-implies-equal-if-specialcase-t-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-iff-if-specialcase-t-bldr)                (rw.iff-implies-iff-if-specialcase-t-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr)  (rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr)    (rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-equal-if-specialcase-t-bldr)    (rw.disjoined-iff-implies-equal-if-specialcase-t-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-iff-if-specialcase-t-bldr)      (rw.disjoined-iff-implies-iff-if-specialcase-t-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-equal-if-bldr)                            (rw.iff-implies-equal-if-bldr-okp x atbl))
     ((equal method 'rw.iff-implies-iff-if-bldr)                              (rw.iff-implies-iff-if-bldr-okp x atbl))
     ((equal method 'rw.equal-of-if-x-y-y-bldr)                               (rw.equal-of-if-x-y-y-bldr-okp x atbl))
     ((equal method 'rw.iff-of-if-x-y-y-bldr)                                 (rw.iff-of-if-x-y-y-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-equal-if-bldr)                  (rw.disjoined-iff-implies-equal-if-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-implies-iff-if-bldr)                    (rw.disjoined-iff-implies-iff-if-bldr-okp x atbl))
     ((equal method 'rw.disjoined-equal-of-if-x-y-y-bldr)                     (rw.disjoined-equal-of-if-x-y-y-bldr-okp x atbl))
     ((equal method 'rw.disjoined-iff-of-if-x-y-y-bldr)                       (rw.disjoined-iff-of-if-x-y-y-bldr-okp x atbl))
     (t
      (level4.step-okp x axioms thms atbl)))))

(defobligations level5.step-okp
  (rw.eqtrace-bldr
   rw.eqtrace-contradiction-bldr
   clause.update-clause-bldr
   clause.update-clause-iff-bldr
   clause.disjoined-update-clause-bldr
   build.lambda-pequal-by-args
   build.disjoined-lambda-pequal-by-args
   clause.aux-split-negative-1-bldr
   clause.aux-split-negative-2-bldr
   rw.iff-implies-equal-if-specialcase-nil-bldr
   rw.iff-implies-iff-if-specialcase-nil-bldr
   rw.iff-implies-equal-if-specialcase-t-bldr
   rw.iff-implies-iff-if-specialcase-t-bldr
   rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr
   rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr
   rw.disjoined-iff-implies-equal-if-specialcase-t-bldr
   rw.disjoined-iff-implies-iff-if-specialcase-t-bldr
   rw.iff-implies-equal-if-bldr
   rw.iff-implies-iff-if-bldr
   rw.equal-of-if-x-y-y-bldr
   rw.iff-of-if-x-y-y-bldr
   rw.disjoined-iff-implies-equal-if-bldr
   rw.disjoined-iff-implies-iff-if-bldr
   rw.disjoined-equal-of-if-x-y-y-bldr
   rw.disjoined-iff-of-if-x-y-y-bldr
   level4.step-okp))

(encapsulate
 ()
 (local (in-theory (enable level5.step-okp)))

 (defthm@ soundness-of-level5.step-okp
   (implies (and (level5.step-okp x axioms thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3)
                             (mapp atbl)
                             (@obligations level5.step-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t)))

 (defthm level5.step-okp-when-level4.step-okp
   ;; This shows that our new step checker is "complete" in the sense that all
   ;; previously acceptable appeals are still acceptable.
   (implies (level4.step-okp x axioms thms atbl)
            (level5.step-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (enable level4.step-okp level3.step-okp level2.step-okp logic.appeal-step-okp))))

 (defthm level5.step-okp-when-not-consp
   (implies (not (consp x))
            (equal (level5.step-okp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable logic.method)))))



(encapsulate
 ()
 (defund level5.flag-proofp-aux (flag x axioms thms atbl)
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
       (and (level5.step-okp x axioms thms atbl)
            (level5.flag-proofp-aux 'list (logic.subproofs x) axioms thms atbl))
     (if (consp x)
         (and (level5.flag-proofp-aux 'proof (car x) axioms thms atbl)
              (level5.flag-proofp-aux 'list (cdr x) axioms thms atbl))
       t)))

 (definlined level5.proofp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appealp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level5.flag-proofp-aux 'proof x axioms thms atbl))

 (definlined level5.proof-listp-aux (x axioms thms atbl)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (logic.formula-listp axioms)
                               (logic.formula-listp thms)
                               (logic.arity-tablep atbl))))
   (level5.flag-proofp-aux 'list x axioms thms atbl))

 (defthmd definition-of-level5.proofp-aux
   (equal (level5.proofp-aux x axioms thms atbl)
          (and (level5.step-okp x axioms thms atbl)
               (level5.proof-listp-aux (logic.subproofs x) axioms thms atbl)))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level5.proofp-aux level5.proof-listp-aux level5.flag-proofp-aux))))

 (defthmd definition-of-level5.proof-listp-aux
   (equal (level5.proof-listp-aux x axioms thms atbl)
          (if (consp x)
              (and (level5.proofp-aux (car x) axioms thms atbl)
                   (level5.proof-listp-aux (cdr x) axioms thms atbl))
            t))
   :rule-classes :definition
   :hints(("Goal" :in-theory (enable level5.proofp-aux level5.proof-listp-aux level5.flag-proofp-aux))))

 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition level5.proofp-aux))))
 (ACL2::theory-invariant (not (ACL2::active-runep '(:definition demo.proof-list)))))



(defthm level5.proofp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level5.proofp-aux x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-level5.proofp-aux))))

(defthm level5.proof-listp-aux-when-not-consp
  (implies (not (consp x))
           (equal (level5.proof-listp-aux x axioms thms atbl)
                  t))
  :hints (("Goal" :in-theory (enable definition-of-level5.proof-listp-aux))))

(defthm level5.proof-listp-aux-of-cons
  (equal (level5.proof-listp-aux (cons a x) axioms thms atbl)
         (and (level5.proofp-aux a axioms thms atbl)
              (level5.proof-listp-aux x axioms thms atbl)))
  :hints (("Goal" :in-theory (enable definition-of-level5.proof-listp-aux))))

(defthms-flag
  :thms ((proof booleanp-of-level5.proofp-aux
                (equal (booleanp (level5.proofp-aux x axioms thms atbl))
                       t))
         (t booleanp-of-level5.proof-listp-aux
            (equal (booleanp (level5.proof-listp-aux x axioms thms atbl))
                   t)))
  :hints(("Goal"
          :in-theory (enable definition-of-level5.proofp-aux)
          :induct (logic.appeal-induction flag x))))

(deflist level5.proof-listp-aux (x axioms thms atbl)
  (level5.proofp-aux x axioms thms atbl)
  :already-definedp t)

(defthms-flag
  ;; We now prove that level5.proofp-aux is sound.  I.e., it only accepts appeals
  ;; whose conclusions are provable in the sense of logic.proofp.
  :@contextp t
  :shared-hyp (and (@obligations level5.step-okp)
                   (mapp atbl)
                   (equal (cdr (lookup 'not atbl)) 1)
                   (equal (cdr (lookup 'equal atbl)) 2)
                   (equal (cdr (lookup 'iff atbl)) 2)
                   (equal (cdr (lookup 'if atbl)) 3))
  :thms ((proof logic.provablep-when-level5.proofp-aux
                (implies (and (logic.appealp x)
                              (level5.proofp-aux x axioms thms atbl))
                         (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                t)))
         (t logic.provable-listp-when-level5.proof-listp-aux
            (implies (and (logic.appeal-listp x)
                          (level5.proof-listp-aux x axioms thms atbl))
                     (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                            t))))
  :hints(("Goal"
          :induct (logic.appeal-induction flag x)
          :in-theory (enable definition-of-level5.proofp-aux))))

(defthms-flag
  ;; We also show that any proof accepted by logic.proofp is still accepted,
  ;; i.e., level5.proofp-aux is "strictly more capable" than logic.proofp.
  ;; THESE THEOREMS MUST BE LEFT DISABLED!
  :thms ((proof level5.proofp-aux-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (level5.proofp-aux x axioms thms atbl)
                                t)))
         (t level5.proof-listp-aux-when-logic.proof-listp
            (implies (logic.proof-listp x axioms thms atbl)
                     (equal (level5.proof-listp-aux x axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.appeal-induction flag x)
           :in-theory (enable definition-of-level5.proofp-aux
                              definition-of-logic.proofp))))

(in-theory (disable level5.proofp-aux-when-logic.proofp
                    level5.proof-listp-aux-when-logic.proof-listp))

(defthm forcing-level5.proofp-aux-of-logic.provable-witness
  ;; Corollary: Suppose F is any provable formula.  Then, the witnessing
  ;; proof of F is acceptable by level5.proofp-aux.
  (implies (force (logic.provablep formula axioms thms atbl))
           (equal (level5.proofp-aux (logic.provable-witness formula axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level5.proofp-aux-when-logic.proofp))))



(definlined@ level5.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (and (@obligations level5.step-okp)
       (mapp atbl)
       (equal (cdr (lookup 'not atbl)) 1)
       (equal (cdr (lookup 'equal atbl)) 2)
       (equal (cdr (lookup 'iff atbl)) 2)
       (equal (cdr (lookup 'if atbl)) 3)
       (level5.proofp-aux x axioms thms atbl)))

(defthm booleanp-of-level5.proofp
  (equal (booleanp (level5.proofp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable level5.proofp))))

(defthm logic.provablep-when-level5.proofp
  (implies (and (logic.appealp x)
                (level5.proofp x axioms thms atbl))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable level5.proofp))))

