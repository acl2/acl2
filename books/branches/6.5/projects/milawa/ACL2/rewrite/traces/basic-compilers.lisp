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
(include-book "trace-okp")
(include-book "basic-if-lemmas")
(include-book "../evaluator-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthmd equal-of-2-and-len
  (equal (equal 2 (len x))
         (and (consp x)
              (consp (cdr x))
              (not (consp (cdr (cdr x)))))))

(local (in-theory (enable rw.trace-conclusion-formula
                          rw.trace-formula
                          equal-of-2-and-len)))

;; (defthmd forcing-equal-when-equal-of-logic.function-name-and-logic.function-args
;;   (implies (and (equal (logic.function-name x) (logic.function-name y))
;;                 (equal (logic.function-args x) (logic.function-args y))
;;                 (force (logic.functionp x))
;;                 (force (logic.functionp y)))
;;            (equal (equal x y)
;;                   t))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable logic.function-name logic.function-args))))


;; (defthmd forcing-logic.lambda-formals-when-not-logic.lambda-actuals
;;   (implies (and (not (logic.lambda-actuals x))
;;                 (force (logic.termp x))
;;                 (force (logic.lambdap x)))
;;            (equal (logic.lambda-formals x)
;;                   nil))
;;   :hints(("Goal"
;;           :in-theory (disable forcing-equal-lens-of-logic.lambda-formals-and-logic.lambda-actuals)
;;           :use ((:instance forcing-equal-lens-of-logic.lambda-formals-and-logic.lambda-actuals)))))

;; (defthmd forcing-logic.term-vars-of-logic.lambda-body-when-not-logic.lambda-actuals
;;   (implies (and (not (logic.lambda-actuals x))
;;                 (force (logic.termp x))
;;                 (force (logic.lambdap x)))
;;            (equal (logic.term-vars (logic.lambda-body x))
;;                   nil))
;;   :hints(("Goal"
;;           :in-theory (e/d (forcing-logic.lambda-formals-when-not-logic.lambda-actuals)
;;                           (forcing-subsetp-of-logic.term-vars-of-logic.lambda-body-with-logic.lambda-formals))
;;           :use ((:instance forcing-subsetp-of-logic.term-vars-of-logic.lambda-body-with-logic.lambda-formals)))))

;; (defthmd forcing-equal-of-logic.lambda-rewrite
;;   (implies (force (logic.termp x))
;;            (equal (equal (logic.lambda formals body actuals) x)
;;                   (and (logic.lambdap x)
;;                        (equal (logic.lambda-formals x) formals)
;;                        (equal (logic.lambda-body x) body)
;;                        (equal (logic.lambda-actuals x) actuals)))))

;; (local (in-theory (enable forcing-equal-when-equal-of-logic.function-name-and-logic.function-args
;;                           forcing-equal-when-equal-of-logic.lambda-parts
;;                           forcing-logic.lambda-formals-when-not-logic.lambda-actuals
;;                           forcing-logic.term-vars-of-logic.lambda-body-when-not-logic.lambda-actuals
;;                           forcing-equal-of-logic.lambda-rewrite
;;                           len-2-when-not-cdr-of-cdr
;;                           )))

;; (defthmd len-2-when-not-cdr-of-cdr
;;   (implies (not (cdr (cdr x)))
;;            (equal (equal (len x) 2)
;;                   (consp (cdr x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))




(defund rw.compile-fail-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.fail-tracep x))))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (lhs    (rw.trace->lhs x)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (build.iff-reflexivity lhs)
          (build.equal-reflexivity lhs))
      (if iffp
          (build.expansion (rw.hypbox-formula hypbox) (build.iff-reflexivity lhs))
        (build.expansion (rw.hypbox-formula hypbox) (build.equal-reflexivity lhs))))))

(defobligations rw.compile-fail-trace
  (build.expansion build.iff-reflexivity build.equal-reflexivity))

(encapsulate
 ()
 (local (in-theory (enable rw.fail-tracep rw.compile-fail-trace)))

 (defthm rw.compile-fail-trace-under-iff
   (iff (rw.compile-fail-trace x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-fail-trace
   (implies (force (and (rw.fail-tracep x)
                        (rw.tracep x)))
            (equal (logic.appealp (rw.compile-fail-trace x))
                   t)))

 (defthm logic.conclusion-of-rw.compile-fail-trace
   (implies (force (and (rw.fail-tracep x)
                        (rw.tracep x)))
            (equal (logic.conclusion (rw.compile-fail-trace x))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-fail-trace
   (implies (force (and (rw.fail-tracep x)
                        (rw.tracep x)
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-fail-trace)))
            (equal (logic.proofp (rw.compile-fail-trace x) axioms thms atbl)
                   t))))




(defund rw.compile-transitivity-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.transitivity-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (proof1 (first proofs))
         (proof2 (second proofs)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (build.transitivity-of-iff proof1 proof2)
          (build.transitivity-of-equal proof1 proof2))
      (if iffp
          (build.disjoined-transitivity-of-iff proof1 proof2)
        (build.disjoined-transitivity-of-equal proof1 proof2)))))

(defobligations rw.compile-transitivity-trace
  (build.disjoined-transitivity-of-iff
   build.disjoined-transitivity-of-pequal
   build.transitivity-of-iff
   build.transitivity-of-equal))

(encapsulate
 ()
 (local (in-theory (enable rw.transitivity-tracep rw.compile-transitivity-trace)))

 (verify-guards rw.compile-transitivity-trace)

 (defthm rw.compile-transitivity-trace-under-iff
   (iff (rw.compile-transitivity-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))


 (defthm logic.appealp-of-rw.compile-transitivity-trace
   (implies (force (and (rw.transitivity-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-transitivity-trace x proofs))
                   t))
   :hints(("Goal"
           :expand ((logic.strip-conclusions x)
                    (logic.strip-conclusions (cdr x))
                    (rw.trace-list-formulas (rw.trace->subtraces x))
                    (rw.trace-list-formulas (cdr (rw.trace->subtraces x)))))))

 (defthm logic.conclusion-of-rw.compile-transitivity-trace
   (implies (force (and (rw.transitivity-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-transitivity-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal"
           :expand ((logic.strip-conclusions x)
                    (logic.strip-conclusions (cdr x))
                    (rw.trace-list-formulas (rw.trace->subtraces x))
                    (rw.trace-list-formulas (cdr (rw.trace->subtraces x)))))))


 (defthm@ logic.proofp-of-rw.compile-transitivity-trace
   (implies (force (and (rw.transitivity-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-transitivity-trace)))
            (equal (logic.proofp (rw.compile-transitivity-trace x proofs) axioms thms atbl)
                   t))
   :hints(("Goal"
           :expand ((logic.strip-conclusions x)
                    (logic.strip-conclusions (cdr x))
                    (rw.trace-list-formulas (rw.trace->subtraces x))
                    (rw.trace-list-formulas (cdr (rw.trace->subtraces x))))))))




(defund rw.compile-equiv-by-args-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.equiv-by-args-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (name   (logic.function-name (rw.trace->lhs x))))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (build.iff-from-equal (build.equal-by-args name proofs))
          (build.equal-by-args name proofs))
      ;; Optimization: we can usually avoid rebuilding the rw.hypbox-formula
      (let ((assms-formula (if (consp proofs)
                               (logic.vlhs (logic.conclusion (car proofs)))
                             (rw.hypbox-formula hypbox))))
        (if iffp
            (build.disjoined-iff-from-equal (build.disjoined-equal-by-args name assms-formula proofs))
          (build.disjoined-equal-by-args name assms-formula proofs))))))

(defobligations rw.compile-equiv-by-args-trace
  (build.disjoined-iff-from-equal
   build.disjoined-equal-by-args
   build.iff-from-equal
   build.equal-by-args))

(encapsulate
 ()
 (local (in-theory (enable rw.equiv-by-args-tracep rw.compile-equiv-by-args-trace)))

 (verify-guards rw.compile-equiv-by-args-trace)

 (defthm rw.compile-equiv-by-args-trace-under-iff
   (iff (rw.compile-equiv-by-args-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-equiv-by-args-trace
   (implies (force (and (rw.equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-equiv-by-args-trace x proofs))
                   t)))

 (defthmd lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace
   (implies (and (equal (logic.function-name lhs) (logic.function-name rhs))
                 (logic.functionp lhs)
                 (logic.functionp rhs)
                 (force (logic.termp lhs))
                 (force (logic.termp rhs)))
            (equal (equal lhs rhs)
                   (equal (logic.function-args lhs)
                          (logic.function-args rhs))))
   :hints(("Goal" :in-theory (enable logic.function-name logic.function-args))))

 (local (in-theory (enable lemma-for-logic.conclusion-of-rw.compile-equiv-by-args-trace)))

 (defthm logic.conclusion-of-rw.compile-equiv-by-args-trace
   (implies (force (and (rw.equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-equiv-by-args-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))


 (defthmd lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
   (implies (equal (rw.trace-list-conclusion-formulas (rw.trace->subtraces x))
                   (logic.strip-conclusions proofs))
            (equal (len (rw.trace->subtraces x))
                   (len proofs)))
   :hints(("Goal"
           :in-theory (disable len-of-rw.trace-list-conclusion-formulas)
           :use ((:instance len-of-rw.trace-list-conclusion-formulas
                            (x (rw.trace->subtraces x)))))))

 (defthmd lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
   (implies (equal (rw.trace-list-conclusion-formulas (rw.trace->subtraces x))
                   (logic.vrhses (logic.strip-conclusions proofs)))
            (equal (len (rw.trace->subtraces x))
                   (len proofs)))
   :hints(("Goal"
           :in-theory (disable len-of-rw.trace-list-conclusion-formulas)
           :use ((:instance len-of-rw.trace-list-conclusion-formulas
                            (x (rw.trace->subtraces x)))))))

 (defthmd lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace
   (implies (equal (rw.trace-list-rhses (rw.trace->subtraces x)) free)
            (equal (len free)
                   (len (rw.trace->subtraces x)))))

 (local (in-theory (enable lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                           lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                           lemma-3-for-logic.proofp-of-rw.compile-equiv-by-args-trace)))

 (defthm@ logic.proofp-of-rw.compile-equiv-by-args-trace
   (implies (force (and (rw.equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.compile-equiv-by-args-trace)))
            (equal (logic.proofp (rw.compile-equiv-by-args-trace x proofs) axioms thms atbl)
                   t))))










(defund rw.compile-lambda-equiv-by-args-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.lambda-equiv-by-args-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox  (rw.trace->hypbox x))
         (iffp    (rw.trace->iffp x))
         (lhs     (rw.trace->lhs x))
         (formals (logic.lambda-formals lhs))
         (body    (logic.lambda-body lhs)))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (build.iff-from-equal (build.lambda-equal-by-args formals body proofs))
          (build.lambda-equal-by-args formals body proofs))
      ;; Optimization: we can usually avoid rebuilding the rw.assms-formula
      (let ((assms-formula (if (consp proofs)
                               (logic.vlhs (logic.conclusion (car proofs)))
                             (rw.hypbox-formula hypbox))))
        (if iffp
            (build.disjoined-iff-from-equal (build.disjoined-lambda-equal-by-args formals body assms-formula proofs))
          (build.disjoined-lambda-equal-by-args formals body assms-formula proofs))))))

(defobligations rw.compile-lambda-equiv-by-args-trace
  (build.disjoined-iff-from-equal
   build.disjoined-lambda-equal-by-args
   build.iff-from-equal
   build.lambda-equal-by-args))

(encapsulate
 ()
 (local (in-theory (enable rw.lambda-equiv-by-args-tracep
                           rw.compile-lambda-equiv-by-args-trace)))

 (defthmd lemma-for-rw.compile-lambda-equiv-by-args-trace
   ;; BOZO we changed the normal form to (len (lambda-actuals x)).  Do we still
   ;; want to target lambda-formals?  Do we still even need this rule?
   (implies (and (logic.termp x)
                 (logic.lambdap x))
            (implies (equal (logic.lambda-actuals x) (rw.trace-list-lhses y))
                     (equal (len (logic.lambda-formals x))
                            (len y))))
   :hints(("Goal"
           :in-theory (disable len-of-rw.trace-list-lhses)
           :use ((:instance len-of-rw.trace-list-lhses (x y))))))

 (local (in-theory (enable lemma-for-rw.compile-lambda-equiv-by-args-trace
                           lemma-1-for-logic.proofp-of-rw.compile-equiv-by-args-trace
                           lemma-2-for-logic.proofp-of-rw.compile-equiv-by-args-trace)))
 (local (in-theory (disable forcing-logic.vrhses-of-logic.por-list-free)))

 (verify-guards rw.compile-lambda-equiv-by-args-trace)

 (defthm rw.compile-lambda-equiv-by-args-trace-under-iff
   (iff (rw.compile-lambda-equiv-by-args-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-lambda-equiv-by-args-trace
   (implies (force (and (rw.lambda-equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-lambda-equiv-by-args-trace x proofs))
                   t)))

 (defthmd forcing-equal-when-equal-of-logic.lambda-parts
   (implies (and (equal (logic.lambda-formals x) (logic.lambda-formals y))
                 (equal (logic.lambda-body x) (logic.lambda-body y))
                 (equal (logic.lambda-actuals x) (logic.lambda-actuals y))
                 (force (logic.lambdap x))
                 (force (logic.lambdap y))
                 (force (logic.termp x))
                 (force (logic.termp y)))
            (equal (equal x y)
                   t))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable logic.lambda-formals
                                     logic.lambda-body
                                     logic.lambda-actuals
                                     logic.lambdap
                                     definition-of-logic.termp))))

 (local (in-theory (enable forcing-equal-when-equal-of-logic.lambda-parts)))

 (defthm logic.conclusion-of-rw.compile-lambda-equiv-by-args-trace
   (implies (force (and (rw.lambda-equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-lambda-equiv-by-args-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-lambda-equiv-by-args-trace
   (implies (force (and (rw.lambda-equiv-by-args-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.compile-lambda-equiv-by-args-trace)))
            (equal (logic.proofp (rw.compile-lambda-equiv-by-args-trace x proofs) axioms thms atbl)
                   t))))



(defund rw.compile-beta-reduction-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.beta-reduction-tracep x))
                  :guard-hints (("Goal" :in-theory (enable rw.beta-reduction-tracep)))))
  (let* ((hypbox  (rw.trace->hypbox x))
         (iffp    (rw.trace->iffp x))
         (lhs     (rw.trace->lhs x))
         (formals (logic.lambda-formals lhs))
         (body    (logic.lambda-body lhs))
         (actuals (logic.lambda-actuals lhs)))
    (let ((main-proof (if iffp
                          (build.iff-from-pequal (build.beta-reduction formals body actuals))
                        (build.equal-from-pequal (build.beta-reduction formals body actuals)))))
      (if (and (not (rw.hypbox->left hypbox))
               (not (rw.hypbox->right hypbox)))
          main-proof
        (build.expansion (rw.hypbox-formula hypbox) main-proof)))))

(defobligations rw.compile-beta-reduction-trace
  (build.iff-from-pequal
   build.equal-from-pequal
   build.expansion
   build.beta-reduction))

(encapsulate
 ()
 (local (in-theory (enable rw.beta-reduction-tracep
                           rw.compile-beta-reduction-trace)))

 (defthm rw.compile-beta-reduction-trace-under-iff
   (iff (rw.compile-beta-reduction-trace x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-beta-reduction-trace
   (implies (force (and (rw.beta-reduction-tracep x)
                        (rw.tracep x)))
            (equal (logic.appealp (rw.compile-beta-reduction-trace x))
                   t)))

 (defthm logic.conclusion-of-rw.compile-beta-reduction-trace
   (implies (force (and (rw.beta-reduction-tracep x)
                        (rw.tracep x)))
            (equal (logic.conclusion (rw.compile-beta-reduction-trace x))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-beta-reduction-trace
   (implies (force (and (rw.beta-reduction-tracep x)
                        (rw.tracep x)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.compile-beta-reduction-trace)))
            (equal (logic.proofp (rw.compile-beta-reduction-trace x) axioms thms atbl)
                   t))))



(defund@ rw.compile-ground-trace (x defs)
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs)
                              (rw.ground-tracep x defs))
                  :verify-guards nil))
  (let* ((hypbox    (rw.trace->hypbox x))
         (iffp      (rw.trace->iffp x))
         (lhs       (rw.trace->lhs x))
         (depth     (rw.trace->extras x))
         (proof     (generic-evaluator-bldr lhs defs depth)) ;; lhs = lhs'
         (lhs-prime (logic.=rhs (logic.conclusion proof))))
    (let ((main-proof (cond ((not iffp)
                             ;; Already canonical under equal
                             (build.equal-from-pequal proof))
                            ((or (equal lhs-prime ''t)
                                 (equal lhs-prime ''nil))
                             ;; Already canonical under iff
                             (build.iff-from-pequal proof))
                            (t
                             ;; Not canonical under iff
                             (@derive
                              ((= lhs lhs-prime)                  (@given proof))
                              ((!= lhs-prime nil)                 (build.not-pequal-constants lhs-prime ''nil))
                              ((!= lhs nil)                       (build.substitute-into-not-pequal @- @--)   *1)
                              ((v (= x nil) (= (iff x t) t))      (build.theorem (theorem-iff-t-when-not-nil)))
                              ((v (= lhs nil) (= (iff lhs t) t))  (build.instantiation @- (list (cons 'x lhs))))
                              ((= (iff lhs t) t)                  (build.modus-ponens-2 *1 @-)))))))
      (if (and (not (rw.hypbox->left hypbox))
               (not (rw.hypbox->right hypbox)))
          main-proof
        (build.expansion (rw.hypbox-formula hypbox) main-proof)))))

(defobligations rw.compile-ground-trace
  (generic-evaluator-bldr
   build.equal-from-pequal
   build.iff-from-pequal
   build.not-pequal-constants
   build.substitute-into-not-pequal
   build.instantiation
   build.modus-ponens-2)
  :extra-thms ((theorem-iff-t-when-not-nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.ground-tracep
                           rw.compile-ground-trace
                           theorem-iff-t-when-not-nil)))

 (defthmd lemma-for-rw.compile-ground-trace
   (implies (and (equal (generic-evaluator term defs depth) x)
                 (logic.termp x)
                 (force (definition-listp defs))
                 (force (logic.termp term))
                 (force (generic-evaluator term defs depth)))
            (equal (logic.constantp x)
                   t)))

 (local (in-theory (enable lemma-for-rw.compile-ground-trace)))

 (verify-guards rw.compile-ground-trace)

 (defthm rw.compile-ground-trace-under-iff
   (iff (rw.compile-ground-trace x defs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm forcing-logic.appealp-of-rw.compile-ground-trace
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.ground-tracep x defs)))
            (equal (logic.appealp (rw.compile-ground-trace x defs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.compile-ground-trace
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.ground-tracep x defs)))
            (equal (logic.conclusion (rw.compile-ground-trace x defs))
                   (rw.trace-formula x))))

 (defthm@ forcing-logic.proofp-of-rw.compile-ground-trace
   ;; Wait -- we don't really need all the axioms, just the defs.  So, if we
   ;; just take the defs instead of the axioms, we could require that they are
   ;; all ok; would that be better?
   (implies (force (and (rw.tracep x)
                        (definition-listp defs)
                        (rw.ground-tracep x defs)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (subsetp defs axioms)
                        (logic.formula-list-atblp defs atbl)
                        (@obligations rw.compile-ground-trace)))
            (equal (logic.proofp (rw.compile-ground-trace x defs) axioms thms atbl)
                   t))))




(defund rw.compile-if-specialcase-nil-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.if-specialcase-nil-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox (rw.trace->hypbox x))
         (iffp   (rw.trace->iffp x))
         (lhs    (rw.trace->lhs x)) ;; (if a1 b1 c1)
         (b1     (second (logic.function-args lhs))))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (rw.iff-implies-iff-if-specialcase-nil-bldr (first proofs) (second proofs) b1)
          (rw.iff-implies-equal-if-specialcase-nil-bldr (first proofs) (second proofs) b1))
      (if iffp
          (rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr (first proofs) (second proofs) b1)
        (rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr (first proofs) (second proofs) b1)))))

(defobligations rw.compile-if-specialcase-nil-trace
  (rw.iff-implies-iff-if-specialcase-nil-bldr
   rw.iff-implies-equal-if-specialcase-nil-bldr
   rw.disjoined-iff-implies-iff-if-specialcase-nil-bldr
   rw.disjoined-iff-implies-equal-if-specialcase-nil-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.if-specialcase-nil-tracep
                           rw.compile-if-specialcase-nil-trace)))

 (local (defthm lemma
          ;; We normally don't break up constants, but this one gets in the way if we don't.
          (equal (equal x '('nil))
                 (and (consp x)
                      (equal (car x) ''nil)
                      (not (cdr x))))))

 (verify-guards rw.compile-if-specialcase-nil-trace)

 (defthm rw.compile-if-specialcase-nil-trace-under-iff
   (iff (rw.compile-if-specialcase-nil-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))


 (defthm logic.appealp-of-rw.compile-if-specialcase-nil-trace
   (implies (force (and (rw.tracep x)
                        (rw.if-specialcase-nil-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-if-specialcase-nil-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-if-specialcase-nil-trace
   (implies (force (and (rw.tracep x)
                        (rw.if-specialcase-nil-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-if-specialcase-nil-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-if-specialcase-nil-trace
   (implies (force (and (rw.tracep x)
                        (rw.if-specialcase-nil-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-if-specialcase-nil-trace)))
            (equal (logic.proofp (rw.compile-if-specialcase-nil-trace x proofs) axioms thms atbl)
                   t))))



(defund rw.compile-if-specialcase-t-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.if-specialcase-t-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox      (rw.trace->hypbox x))
         (iffp        (rw.trace->iffp x))
         (subtraces   (rw.trace->subtraces x))
         (subtrace1   (first subtraces))                          ;; [hyps ->] (iff a1 const) = t
         (const       (rw.trace->rhs subtrace1))
         (const-proof (build.not-pequal-constants const ''nil))   ;; const != nil
         (lhs         (rw.trace->lhs x))                          ;; (if a1 b1 c1)
         (c1          (third (logic.function-args lhs))))
    (if (and (not (rw.hypbox->left hypbox))
             (not (rw.hypbox->right hypbox)))
        (if iffp
            (rw.iff-implies-iff-if-specialcase-t-bldr (first proofs) const-proof (second proofs) c1)
          (rw.iff-implies-equal-if-specialcase-t-bldr (first proofs) const-proof (second proofs) c1))
      ;; We need to expand const-proof with assms-formula.  But we can just
      ;; grab the formula out of the first proof instead of reconstructing it.
      (let* ((assms-formula   (logic.vlhs (logic.conclusion (first proofs))))
             (new-const-proof (build.expansion assms-formula const-proof)))
        (if iffp
            (rw.disjoined-iff-implies-iff-if-specialcase-t-bldr (first proofs) new-const-proof (second proofs) c1)
          (rw.disjoined-iff-implies-equal-if-specialcase-t-bldr (first proofs) new-const-proof (second proofs) c1))))))

(defobligations rw.compile-if-specialcase-t-trace
  (build.not-pequal-constants
   rw.iff-implies-iff-if-specialcase-t-bldr
   rw.iff-implies-equal-if-specialcase-t-bldr
   rw.disjoined-iff-implies-iff-if-specialcase-t-bldr
   rw.disjoined-iff-implies-equal-if-specialcase-t-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.if-specialcase-t-tracep
                           rw.compile-if-specialcase-t-trace)))

 (verify-guards rw.compile-if-specialcase-t-trace)

 (defthm rw.compile-if-specialcase-t-trace-under-iff
   (iff (rw.compile-if-specialcase-t-trace x proofs)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm logic.appealp-of-rw.compile-if-specialcase-t-trace
   (implies (force (and (rw.if-specialcase-t-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-if-specialcase-t-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-if-specialcase-t-trace
   (implies (force (and (rw.if-specialcase-t-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-if-specialcase-t-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-if-specialcase-t-trace
   (implies (force (and (rw.if-specialcase-t-tracep x)
                        (rw.tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; --
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-if-specialcase-t-trace)))
            (equal (logic.proofp (rw.compile-if-specialcase-t-trace x proofs) axioms thms atbl)
                   t))))

