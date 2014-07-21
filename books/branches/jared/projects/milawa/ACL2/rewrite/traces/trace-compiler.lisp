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
(include-book "basic-compilers")
(include-book "urewrite-compilers")
(include-book "crewrite-compilers")
(include-book "crewrite-rule-compiler")
(include-book "not-compiler")
(include-book "collect-forced-goals")
(include-book "trace-arities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.compile-trace-step (x defs proofs fproofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.trace-step-okp x defs)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (let ((method (rw.trace->method x)))
    (cond ((equal method 'fail)                          (rw.compile-fail-trace x))
          ((equal method 'transitivity)                  (rw.compile-transitivity-trace x proofs))
          ((equal method 'equiv-by-args)                 (rw.compile-equiv-by-args-trace x proofs))
          ((equal method 'lambda-equiv-by-args)          (rw.compile-lambda-equiv-by-args-trace x proofs))
          ((equal method 'beta-reduction)                (rw.compile-beta-reduction-trace x))
          ((equal method 'ground)                        (rw.compile-ground-trace x defs))
          ((equal method 'if-specialcase-nil)            (rw.compile-if-specialcase-nil-trace x proofs))
          ((equal method 'if-specialcase-t)              (rw.compile-if-specialcase-t-trace x proofs))
          ((equal method 'not)                           (rw.compile-not-trace x proofs))
          ((equal method 'negative-if)                   (rw.compile-negative-if-trace x))
          ;; ---
          ((equal method 'urewrite-if-specialcase-same)  (rw.compile-urewrite-if-specialcase-same-trace x proofs))
          ((equal method 'urewrite-if-generalcase)       (rw.compile-urewrite-if-generalcase-trace x proofs))
          ((equal method 'urewrite-rule)                 (rw.compile-urewrite-rule-trace x))
          ;; ---
          ((equal method 'crewrite-if-specialcase-same)  (rw.compile-crewrite-if-specialcase-same-trace x proofs))
          ((equal method 'crewrite-if-generalcase)       (rw.compile-crewrite-if-generalcase-trace x proofs))
          ((equal method 'crewrite-rule)                 (rw.compile-crewrite-rule-trace x proofs))
          ((equal method 'assumptions)                   (rw.compile-assumptions-trace x))
          ((equal method 'force)                         (rw.compile-force-trace x fproofs))
          ((equal method 'weakening)                     (rw.compile-weakening-trace x proofs))
          ;; Sneaky twiddle for hypless iff theorem
          (t t))))

(defobligations rw.compile-trace-step
  (rw.compile-fail-trace
   rw.compile-transitivity-trace
   rw.compile-equiv-by-args-trace
   rw.compile-lambda-equiv-by-args-trace
   rw.compile-beta-reduction-trace
   rw.compile-ground-trace
   rw.compile-if-specialcase-nil-trace
   rw.compile-if-specialcase-t-trace
   rw.compile-not-trace
   rw.compile-negative-if-trace
   ;; ---
   rw.compile-urewrite-if-specialcase-same-trace
   rw.compile-urewrite-if-generalcase-trace
   rw.compile-urewrite-rule-trace
   ;; ---
   rw.compile-crewrite-if-specialcase-same-trace
   rw.compile-crewrite-if-generalcase-trace
   rw.compile-crewrite-rule-trace
   rw.compile-assumptions-trace
   rw.compile-force-trace
   rw.compile-weakening-trace
   ))

(encapsulate
 ()
 (local (in-theory (enable rw.trace-step-okp
                           rw.trace-step-env-okp
                           rw.compile-trace-step)))

 (verify-guards rw.compile-trace-step)

 (defthm rw.compile-trace-step-under-iff
   (iff (rw.compile-trace-step x defs proofs fproofs)
        t))

 (defthm forcing-logic.appealp-of-rw.compile-trace-step
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.trace-step-okp x defs)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))))
            (equal (logic.appealp (rw.compile-trace-step x defs proofs fproofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-trace-step
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.trace-step-okp x defs)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))))
            (equal (logic.conclusion (rw.compile-trace-step x defs proofs fproofs))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-trace-step
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.trace-step-okp x defs)
                        (rw.trace-step-env-okp x defs thms atbl)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.proof-listp fproofs axioms thms atbl)
                        (logic.formula-list-atblp defs atbl)
                        (subsetp defs axioms)
                        (@obligations rw.compile-trace-step)))
            (equal (logic.proofp (rw.compile-trace-step x defs proofs fproofs) axioms thms atbl)
                   t))))




(defund rw.flag-compile-trace (flag x defs fproofs)
  (declare (xargs :guard (if (equal flag 'term)
                             (and (rw.tracep x)
                                  (definition-listp defs)
                                  (rw.trace-okp x defs)
                                  (logic.appeal-listp fproofs)
                                  (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs)))
                           (and (rw.trace-listp x)
                                (definition-listp defs)
                                (rw.trace-list-okp x defs)
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.collect-forced-goals-list x) (logic.strip-conclusions fproofs))))
                  :measure (two-nats-measure (rank x)
                                             (if (equal flag 'term) 1 0))
                  :verify-guards nil))
  (if (equal flag 'term)
      (rw.compile-trace-step x
                             defs
                             (rw.flag-compile-trace 'list (rw.trace->subtraces x) defs fproofs)
                             fproofs)
    (if (consp x)
        (cons (rw.flag-compile-trace 'term (car x) defs fproofs)
              (rw.flag-compile-trace 'list (cdr x) defs fproofs))
      nil)))

(defund rw.compile-trace (x defs fproofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.trace-okp x defs)
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (rw.flag-compile-trace 'term x defs fproofs))

(defund rw.compile-trace-list (x defs fproofs)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (definition-listp defs)
                              (rw.trace-list-okp x defs)
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.collect-forced-goals-list x) (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (rw.flag-compile-trace 'list x defs fproofs))

(defthmd definition-of-rw.compile-trace
  (equal (rw.compile-trace x defs fproofs)
         (rw.compile-trace-step x
                                defs
                                (rw.compile-trace-list (rw.trace->subtraces x) defs fproofs)
                                fproofs))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.flag-compile-trace
                                    rw.compile-trace
                                    rw.compile-trace-list))))

(defthmd definition-of-rw.compile-trace-list
  (equal (rw.compile-trace-list x defs fproofs)
         (if (consp x)
             (cons (rw.compile-trace (car x) defs fproofs)
                   (rw.compile-trace-list (cdr x) defs fproofs))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.flag-compile-trace
                                    rw.compile-trace
                                    rw.compile-trace-list))))

(defthm rw.flag-compile-trace-of-term-removal
  (equal (rw.flag-compile-trace 'term x defs fproofs)
         (rw.compile-trace x defs fproofs))
  :hints(("Goal" :in-theory (enable rw.compile-trace))))

(defthm rw.flag-compile-trace-of-list-removal
  (equal (rw.flag-compile-trace 'list x defs fproofs)
         (rw.compile-trace-list x defs fproofs))
  :hints(("Goal" :in-theory (enable rw.compile-trace-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.compile-trace))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.compile-trace-list))))


(defobligations rw.flag-compile-trace
  (rw.compile-trace-step))

(defobligations rw.compile-trace
  (rw.flag-compile-trace))

(defobligations rw.compile-trace-list
  (rw.flag-compile-trace))


(defthms-flag
  :shared-hyp (force (and (logic.appeal-listp fproofs)
                          (definition-listp defs)))
  :thms ((term forcing-logic.appealp-of-rw.compile-trace
               (implies (force (and (rw.tracep x)
                                    (rw.trace-okp x defs)
                                    (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))))
                        (equal (logic.appealp (rw.compile-trace x defs fproofs))
                               t)))
         (term forcing-logic.conclusion-of-rw.compile-trace
               (implies (force (and (rw.tracep x)
                                    (rw.trace-okp x defs)
                                    (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))))
                        (equal (logic.conclusion (rw.compile-trace x defs fproofs))
                               (rw.trace-formula x))))
         (t forcing-logic.appeal-listp-of-rw.compile-trace-list
            (implies (force (and (rw.trace-listp x)
                                 (rw.trace-list-okp x defs)
                                 (subsetp (rw.collect-forced-goals-list x) (logic.strip-conclusions fproofs))))
                     (equal (logic.appeal-listp (rw.compile-trace-list x defs fproofs))
                            t)))
         (t forcing-logic.strip-conclusions-of-rw.compile-trace-list
            (implies (force (and (rw.trace-listp x)
                                 (rw.trace-list-okp x defs)
                                 (subsetp (rw.collect-forced-goals-list x) (logic.strip-conclusions fproofs))))
                     (equal (logic.strip-conclusions (rw.compile-trace-list x defs fproofs))
                            (rw.trace-list-formulas x)))))
  :hints(("Goal"
          :in-theory (enable definition-of-rw.compile-trace
                             definition-of-rw.compile-trace-list)
          :expand ((rw.compile-trace x defs fproofs)
                   (rw.compile-trace-list x defs fproofs))
          :induct (rw.trace-induction flag x))))

(verify-guards rw.flag-compile-trace)
(verify-guards rw.compile-trace)
(verify-guards rw.compile-trace-list)

(defthms-flag
  :shared-hyp (force (and (logic.appeal-listp fproofs)
                          (logic.proof-listp fproofs axioms thms atbl)
                          (definition-listp defs)
                          (logic.formula-list-atblp defs atbl)
                          (subsetp defs axioms)
                          (equal (cdr (lookup 'equal atbl)) 2)
                          (equal (cdr (lookup 'iff atbl)) 2)
                          (equal (cdr (lookup 'if atbl)) 3)
                          (equal (cdr (lookup 'not atbl)) 1)))
  :thms ((term forcing-logic.proofp-of-rw.compile-trace
               (implies (force (and (rw.tracep x)
                                    (rw.trace-okp x defs)
                                    (subsetp (rw.collect-forced-goals x) (logic.strip-conclusions fproofs))
                                    ;; ---
                                    (rw.trace-atblp x atbl)
                                    (rw.trace-env-okp x defs thms atbl)
                                    (@obligations rw.compile-trace)))
                        (equal (logic.proofp (rw.compile-trace x defs fproofs) axioms thms atbl)
                               t)))
         (t forcing-logic.proof-listp-of-rw.compile-trace
            (implies (force (and (rw.trace-listp x)
                                 (rw.trace-list-okp x defs)
                                 (subsetp (rw.collect-forced-goals-list x) (logic.strip-conclusions fproofs))
                                 ;; ---
                                 (rw.trace-list-atblp x atbl)
                                 (rw.trace-list-env-okp x defs thms atbl)
                                 (@obligations rw.compile-trace-list)))
                     (equal (logic.proof-listp (rw.compile-trace-list x defs fproofs) axioms thms atbl)
                            t))))
  :@contextp t
  :hints (("Goal"
           :in-theory (enable definition-of-rw.compile-trace
                              definition-of-rw.compile-trace-list)
           :expand ((rw.compile-trace x defs fproofs)
                    (rw.compile-trace-list x defs fproofs))
           :induct (rw.trace-induction flag x))))





(defund rw.compile-trace-okp (x defs thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (definition-listp defs)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x))
        (hypbox     (rw.hypbox nil nil)) ;; silly, used for fast checks
        )
    (and (equal method 'rw.compile-trace)
         ;; extras is a valid trace
         (rw.faster-tracep extras hypbox)
         (logic.fast-arities-okp (rw.faster-trace-arities extras hypbox nil) atbl)
         (rw.trace-okp extras defs)
         (rw.trace-env-okp extras defs thms atbl)
         ;; the trace has the right conclusion
         (equal conclusion (rw.trace-formula extras))
         ;; subproofs are the fproofs
         (equal (remove-duplicates (rw.collect-forced-goals extras))
                (logic.strip-conclusions subproofs)))))

(defthm forcing-logic.appeal-listp-of-logic.find-proofs
  ;; BOZO move to logic.find-proofs
  (implies (force (and (logic.appeal-listp proofs)
                       (subsetp formulas (logic.strip-conclusions proofs))))
           (equal (logic.appeal-listp (logic.find-proofs formulas proofs))
                  t))
  :hints(("Goal" :induct (cdr-induction formulas))))

(defthm forcing-logic.strip-conclusions-of-logic.find-proofs
  ;; BOZO move to logic.find-proofs
  (implies (force (and (logic.appeal-listp proofs)
                       (subsetp formulas (logic.strip-conclusions proofs))))
           (equal (logic.strip-conclusions (logic.find-proofs formulas proofs))
                  (list-fix formulas)))
  :hints(("Goal" :induct (cdr-induction formulas))))

(defund rw.compile-trace-high (x defs fproofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.trace-okp x defs)
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.collect-forced-goals x)
                                       (logic.strip-conclusions fproofs))))
           (ignore defs))
  (let* ((forced-goals         (rw.collect-forced-goals x))
         (cleaned-forced-goals (remove-duplicates forced-goals)))
    (ACl2::prog2$
     (or (same-lengthp forced-goals cleaned-forced-goals)
         (ACL2::cw! ";;; Removing forced duplicates reduced ~x0 goals to ~x1. (single trace)~%"
                    (fast-len forced-goals 0)
                    (fast-len cleaned-forced-goals 0)))
     (logic.appeal 'rw.compile-trace
                   (rw.trace-formula x)
                   (logic.find-proofs cleaned-forced-goals fproofs)
                   x))))

(defthm rw.compile-trace-okp-of-rw.compile-trace-high
  ;; Sanity check to make sure the high-level builder is going to work.
  (implies (and (rw.tracep x)
                (mapp atbl)
                (definition-listp defs)
                (rw.trace-okp x defs)
                (logic.appeal-listp fproofs)
                (subsetp (rw.collect-forced-goals x)
                         (logic.strip-conclusions fproofs))
                (rw.trace-atblp x atbl)
                (rw.trace-env-okp x defs thms atbl))
           (equal (rw.compile-trace-okp (rw.compile-trace-high x defs fproofs) defs thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.compile-trace-high
                                    rw.compile-trace-okp))))


(encapsulate
 ()
 (local (in-theory (enable rw.compile-trace-okp)))

 (defthm booleanp-of-rw.compile-trace-okp
   (equal (booleanp (rw.compile-trace-okp x defs thms atbl))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm rw.compile-trace-okp-of-logic.appeal-identity
   (equal (rw.compile-trace-okp (logic.appeal-identity x) axioms thms atbl)
          (rw.compile-trace-okp x axioms thms atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthmd lemma-0-for-soundness-of-rw.compile-trace-okp
   (implies (equal (remove-duplicates x) y)
            (equal (subsetp x y)
                   t)))

 (local (in-theory (enable lemma-0-for-soundness-of-rw.compile-trace-okp)))

 (defthmd lemma-1-for-soundness-of-rw.compile-trace-okp
   (implies (and (rw.compile-trace-okp x defs thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (definition-listp defs))
            (equal (logic.conclusion
                    (rw.compile-trace (logic.extras x)
                                      defs
                                      (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                   axioms thms atbl)))
                   (logic.conclusion x)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthmd@ lemma-2-for-soundness-of-rw.compile-trace-okp
   (implies (and (rw.compile-trace-okp x defs thms atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 ;; --
                 (mapp atbl)
                 (definition-listp defs)
                 (logic.formula-list-atblp defs atbl)
                 (subsetp defs axioms)
                 (@obligations rw.compile-trace)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3))
            (equal (logic.proofp
                    (rw.compile-trace (logic.extras x)
                                      defs
                                      (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                   axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.compile-trace-okp
   (implies (and (rw.compile-trace-okp x defs thms atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (mapp atbl)
                             (definition-listp defs)
                             (logic.formula-list-atblp defs atbl)
                             (subsetp defs axioms)
                             (@obligations rw.compile-trace)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-rw.compile-trace-okp
                               lemma-2-for-soundness-of-rw.compile-trace-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (rw.compile-trace (logic.extras x)
                                                  defs
                                                  (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                               axioms thms atbl)))))))))
