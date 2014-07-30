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
(include-book "eqtrace-okp")
(include-book "primary-eqtrace-bldr")
(include-book "secondary-eqtrace-bldr")
(include-book "trans1-eqtrace-bldr")
(include-book "trans2-eqtrace-bldr")
(include-book "trans3-eqtrace-bldr")
(include-book "weakening-eqtrace-bldr")
(include-book "direct-iff-eqtrace-bldr")
(include-book "negative-iff-eqtrace-bldr")
(include-book "hypbox-arities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund rw.eqtrace-step-bldr (x box proofs)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box)))
                  :verify-guards nil))
  (let ((method (rw.eqtrace->method x)))
    (cond ((equal method 'primary)    (rw.primary-eqtrace-bldr x box))
          ((equal method 'secondary)  (rw.secondary-eqtrace-bldr x box))
          ((equal method 'trans1)     (rw.trans1-eqtrace-bldr x box proofs))
          ((equal method 'trans2)     (rw.trans2-eqtrace-bldr x box proofs))
          ((equal method 'trans3)     (rw.trans3-eqtrace-bldr x box proofs))
          ((equal method 'weakening)  (rw.weakening-eqtrace-bldr x box proofs))
          ((equal method 'direct-iff) (rw.direct-iff-eqtrace-bldr x box))
          ((equal method 'negative-iff) (rw.negative-iff-eqtrace-bldr x box))
          ;; Sneaky twiddle for hypless iff theorem.
          (t t))))

(defobligations rw.eqtrace-step-bldr
  (rw.primary-eqtrace-bldr
   rw.secondary-eqtrace-bldr
   rw.trans1-eqtrace-bldr
   rw.trans2-eqtrace-bldr
   rw.trans3-eqtrace-bldr
   rw.weakening-eqtrace-bldr
   rw.direct-iff-eqtrace-bldr
   rw.negative-iff-eqtrace-bldr
   ))

(encapsulate
 ()
 (local (in-theory (e/d (rw.eqtrace-step-bldr
                         definition-of-rw.eqtrace-okp
                         rw.eqtrace-step-okp)
                        (forcing-rw.eqtrace-list-okp-of-rw.eqtrace-subtraces))))

 (defthm rw.eqtrace-step-bldr-under-iff
   (iff (rw.eqtrace-step-bldr x box proofs)
        t))

 (defthm forcing-logic.appealp-of-rw.eqtrace-step-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.appealp (rw.eqtrace-step-bldr x box proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.eqtrace-step-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))))
            (equal (logic.conclusion (rw.eqtrace-step-bldr x box proofs))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.eqtrace-step-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (rw.eqtrace-formula-list (rw.eqtrace->subtraces x) box))
                        ;; ---
                        (rw.hypbox-atblp box atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.eqtrace-step-bldr)
                        ))
            (equal (logic.proofp (rw.eqtrace-step-bldr x box proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.eqtrace-step-bldr))




(defun rw.flag-eqtrace-bldr (flag x box)
  (declare (xargs :guard (if (equal flag 'trace)
                             (and (rw.eqtracep x)
                                  (rw.hypboxp box)
                                  (rw.eqtrace-okp x box))
                           (and (equal flag 'list)
                                (rw.eqtrace-listp x)
                                (rw.hypboxp box)
                                (rw.eqtrace-list-okp x box)))
                  :verify-guards nil
                  :measure (two-nats-measure (rank x) (if (equal flag 'trace) 1 0))))
  (if (equal flag 'trace)
      (rw.eqtrace-step-bldr x box
                            (rw.flag-eqtrace-bldr 'list (rw.eqtrace->subtraces x) box))
    (if (consp x)
        (cons (rw.flag-eqtrace-bldr 'trace (car x) box)
              (rw.flag-eqtrace-bldr 'list (cdr x) box))
      nil)))

(defund rw.eqtrace-bldr (x box)
  ;; Don't inline this since we want to redefine it.
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box))
                  :verify-guards nil))
  (rw.flag-eqtrace-bldr 'trace x box))

(defund rw.eqtrace-list-bldr (x box)
  (declare (xargs :guard (and (rw.eqtrace-listp x)
                              (rw.hypboxp box)
                              (rw.eqtrace-list-okp x box))
                  :verify-guards nil))
  (rw.flag-eqtrace-bldr 'list x box))

(defobligations rw.flag-eqtrace-bldr
  (rw.eqtrace-step-bldr))

(defobligations rw.eqtrace-bldr
  (rw.flag-eqtrace-bldr))

(defobligations rw.eqtrace-list-bldr
  (rw.flag-eqtrace-bldr))

(defthmd definition-of-rw.eqtrace-bldr
  (equal (rw.eqtrace-bldr x box)
         (rw.eqtrace-step-bldr x box (rw.eqtrace-list-bldr (rw.eqtrace->subtraces x) box)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-bldr rw.eqtrace-list-bldr))))

(defthmd definition-of-rw.eqtrace-list-bldr
  (equal (rw.eqtrace-list-bldr x box)
         (if (consp x)
             (cons (rw.eqtrace-bldr (car x) box)
                   (rw.eqtrace-list-bldr (cdr x) box))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable rw.eqtrace-bldr rw.eqtrace-list-bldr))))

(defthm rw.flag-eqtrace-bldr-of-trace
  (equal (rw.flag-eqtrace-bldr 'trace x box)
         (rw.eqtrace-bldr x box))
  :hints(("Goal" :in-theory (enable rw.eqtrace-bldr))))

(defthm rw.flag-eqtrace-bldr-of-list
  (equal (rw.flag-eqtrace-bldr 'list x box)
         (rw.eqtrace-list-bldr x box))
  :hints(("Goal" :in-theory (enable rw.eqtrace-list-bldr))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-bldr))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.eqtrace-list-bldr))))

(encapsulate
 ()
 (defthm rw.eqtrace-list-bldr-when-not-consp
   (implies (not (consp x))
            (equal (rw.eqtrace-list-bldr x box)
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-bldr))))

 (defthm rw.eqtrace-list-bldr-of-cons
   (equal (rw.eqtrace-list-bldr (cons a x) box)
          (cons (rw.eqtrace-bldr a box)
                (rw.eqtrace-list-bldr x box)))
   :hints(("Goal" :in-theory (enable definition-of-rw.eqtrace-list-bldr))))

 (defprojection
   :list (rw.eqtrace-list-bldr x box)
   :element (rw.eqtrace-bldr x box)
   :already-definedp t))




(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'trace)
              (implies (and (rw.eqtracep x)
                            (rw.hypboxp box)
                            (rw.eqtrace-okp x box))
                       (and (logic.appealp (rw.eqtrace-bldr x box))
                            (equal (logic.conclusion (rw.eqtrace-bldr x box))
                                   (rw.eqtrace-formula x box))))
            (implies (and (rw.eqtrace-listp x)
                          (rw.hypboxp box)
                          (rw.eqtrace-list-okp x box))
                     (and (logic.appeal-listp (rw.eqtrace-list-bldr x box))
                          (equal (logic.strip-conclusions (rw.eqtrace-list-bldr x box))
                                 (rw.eqtrace-formula-list x box)))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (rw.flag-eqtrace-bldr flag x box)
                  :expand (rw.eqtrace-bldr x box)))))

 (defthm forcing-logic.appealp-of-rw.eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)))
            (equal (logic.appealp (rw.eqtrace-bldr x box))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'trace))))))

 (defthm forcing-logic.conclusion-of-rw.eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)))
            (equal (logic.conclusion (rw.eqtrace-bldr x box))
                   (rw.eqtrace-formula x box)))
   :hints(("Goal" :use ((:instance lemma (flag 'trace))))))

 (defthm forcing-logic.appeal-listp-of-rw.eqtrace-list-bldr
   (implies (force (and (rw.eqtrace-listp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-list-okp x box)))
            (equal (logic.appeal-listp (rw.eqtrace-list-bldr x box))
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list))))))

 (defthm forcing-logic.strip-conclusions-of-rw.eqtrace-list-bldr
   (implies (force (and (rw.eqtrace-listp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-list-okp x box)))
            (equal (logic.strip-conclusions (rw.eqtrace-list-bldr x box))
                   (rw.eqtrace-formula-list x box)))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(verify-guards rw.flag-eqtrace-bldr)
(verify-guards rw.eqtrace-bldr)
(verify-guards rw.eqtrace-list-bldr)

(encapsulate
 ()
 (local (defthm@ lemma
          (if (equal flag 'trace)
              (implies (and (rw.eqtracep x)
                            (rw.hypboxp box)
                            (rw.eqtrace-okp x box)
                            ;; ---
                            (rw.hypbox-atblp box atbl)
                            (equal (cdr (lookup 'not atbl)) 1)
                            (equal (cdr (lookup 'equal atbl)) 2)
                            (equal (cdr (lookup 'iff atbl)) 2)
                            (@obligations rw.eqtrace-bldr))
                       (equal (logic.proofp (rw.eqtrace-bldr x box) axioms thms atbl)
                              t))
            (implies (and (rw.eqtrace-listp x)
                          (rw.hypboxp box)
                          (rw.eqtrace-list-okp x box)
                          ;; ---
                          (rw.hypbox-atblp box atbl)
                          (equal (cdr (lookup 'not atbl)) 1)
                          (equal (cdr (lookup 'equal atbl)) 2)
                          (equal (cdr (lookup 'iff atbl)) 2)
                          (@obligations rw.eqtrace-list-bldr))
                     (equal (logic.proof-listp (rw.eqtrace-list-bldr x box) axioms thms atbl)
                            t)))
          :rule-classes nil
          :hints(("Goal"
                  :induct (rw.flag-eqtrace-bldr flag x box)
                  :expand (rw.eqtrace-bldr x box)))))

 (defthm@ forcing-logic.proofp-of-rw.eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)
                        ;; ---
                        (rw.hypbox-atblp box atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.eqtrace-bldr)))
            (equal (logic.proofp (rw.eqtrace-bldr x box) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'trace))))))

 (defthm@ forcing-logic.proof-listp-of-rw.eqtrace-list-bldr
   (implies (force (and (rw.eqtrace-listp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-list-okp x box)
                        ;; ---
                        (rw.hypbox-atblp box atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.eqtrace-list-bldr)))
            (equal (logic.proof-listp (rw.eqtrace-list-bldr x box) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))



(defund rw.eqtrace-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.eqtrace-bldr)
         (tuplep 2 extras)
         (let ((trace (first extras))
               (box   (second extras)))
           (and (rw.eqtracep trace)
                (rw.hypboxp box)
                (rw.fast-hypbox-atblp box atbl)
                (rw.eqtrace-okp trace box)
                (equal conclusion (rw.eqtrace-formula trace box))
                (not subproofs))))))

(defund rw.eqtrace-bldr-high (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box))))
  (logic.appeal 'rw.eqtrace-bldr
                (rw.eqtrace-formula x box)
                nil
                (list x box)))

(defobligations rw.eqtrace-bldr-okp
  (rw.eqtrace-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-bldr-okp)))

 (defthm booleanp-of-rw.eqtrace-bldr-okp
   (equal (booleanp (rw.eqtrace-bldr-okp x atbl))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm rw.eqtrace-bldr-okp-of-logic.appeal-identity
   (equal (rw.eqtrace-bldr-okp (logic.appeal-identity x) atbl)
          (rw.eqtrace-bldr-okp x atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (local (in-theory (enable backtracking-logic.formula-atblp-rules)))
 (local (in-theory (disable forcing-logic.formula-atblp-rules
                            forcing-lookup-of-logic.function-name-free
                            forcing-logic.term-list-atblp-of-logic.function-args)))

 (defthm lemma-1-for-soundness-of-rw.eqtrace-bldr-okp
   (implies (and (rw.eqtrace-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (rw.eqtrace-bldr (first (logic.extras x))
                                     (second (logic.extras x))))
                   (logic.conclusion x)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm@ lemma-2-for-soundness-of-rw.eqtrace-bldr-okp
   (implies (and (rw.eqtrace-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 ;; ---
                 (@obligations rw.eqtrace-bldr-okp)
                 (mapp atbl)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'equal atbl)) 2))
            (equal (logic.proofp
                    (rw.eqtrace-bldr (first (logic.extras x))
                                     (second (logic.extras x)))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.eqtrace-bldr-okp
   (implies (and (rw.eqtrace-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)))
                 ;; ---
                 (force (mapp atbl))
                 (force (@obligations rw.eqtrace-bldr-okp))
                 (force (equal (cdr (lookup 'not atbl)) 1))
                 (force (equal (cdr (lookup 'iff atbl)) 2))
                 (force (equal (cdr (lookup 'equal atbl)) 2)))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-rw.eqtrace-bldr-okp
                               lemma-2-for-soundness-of-rw.eqtrace-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (rw.eqtrace-bldr (first (logic.extras x))
                                                 (second (logic.extras x))))))))))


