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
(include-book "pequal-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "lambda-rules.tex")

(dd.section "$\\lambda$ reduction rules")


(defderiv build.dual-substitution-lemma-1
  :from   ((proof x (= (? a) (? b)))
           (proof y (= (? b) (? d)))
           (proof z (= (? c) (? d))))
  :derive (= (? a) (? c))
  :proof  (@derive
           ((= (? a) (? b))         (@given x))
           ((= (? b) (? d))         (@given y))
           ((= (? a) (? d))         (build.transitivity-of-pequal @-- @-)  *1)
           ((= (? c) (? d))         (@given z))
           ((= (? d) (? c))         (build.commute-pequal @-))
           ((= (? a) (? c))         (build.transitivity-of-pequal *1 @-))))

(defun build.flag-dual-substitution (flag x vars proofs)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (and (equal flag 'list)
                                     (logic.term-listp x)))
                              (logic.variable-listp vars)
                              (uniquep vars)
                              (logic.appeal-listp proofs)
                              (same-lengthp vars proofs)
                              (logic.all-atomicp (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             ;; If x is a constant, then x/[Vi<-Ti] = x and x/[Vi<-Si] = x, so our goal
             ;; is to prove x = x, which is trivial by reflexivity.
             (build.reflexivity x))
            ((logic.variablep x)
             ;; If x is a variable, then either it is some vi or not.
             (let ((index (first-index x vars)))
               (if (equal index (len vars))
                   ;; If it wasn't found among the vi, then as in the constant case we
                   ;; have x/[Vi<-Ti] = x and x/[Vi<-Si] = x, so our goal is to prove x
                   ;; = x, which is again trivial by reflexivity.
                   (build.reflexivity x)
                 ;; Else x is exactly some vi, and we have x/[Vi<-Ti] = ti and
                 ;; x/[Vi<-Si] = si, so our goal is to prove ti = si, which is trivial
                 ;; by the ith proof.
                 (logic.appeal-identity (nth index proofs)))))
            ((logic.functionp x)
             ;; If x is (f a1 ... an), then
             ;;   x/[Vi<-Ti] = (f a1/[Vi<-Ti] ... an/[Vi<-Ti]), and
             ;;   x/[Vi<-Si] = (f a1/[Vi<-Si] ... an/[Vi<-Si]).
             ;;
             ;; For each ai, we can recursively prove ai/[Vi<-Ti] = ai/[Vi<-Si], then
             ;; by pequal-by-args we can prove our goal.
             (build.pequal-by-args (logic.function-name x)
                                   (build.flag-dual-substitution 'list (logic.function-args x) vars proofs)))
            ((logic.lambdap x)
             ;; If x is ((lambda (x1...xn) B) a1...an), then by beta reduction we have
             ;;
             ;; To begin, we recursively construct proofs of:
             ;;   ai/[Vi<-Ti] = ai/[Vi<-Si]                                 (*1)
             ;;
             ;; To make our next steps more clear, let
             ;;   ci = ai/[Vi<-Ti], and
             ;;   di = ai/[Vi<-Si]
             ;;
             ;; In other words, the proofs in *1 establish:
             ;;   ci = di
             ;;
             ;; Using these proofs, we can recursively prove B/[Xi<-Ci] = B/[Xi<-Di].
             ;; This is well-founded because we are recurring over only the structure
             ;; of x, and B is contained in x and hence is smaller than x.  If we now
             ;; expand away the definitions of Ci and Di, we have proven:
             ;;
             ;;   B/[Xi<-(Ai/[Vi<-Ti])] = B/[Xi<-(Ai/[Vi<-Si])]
             ;;
             ;; But since x is a lambda, all of the variables in B must be among the
             ;; Xi, so the substitutions can be teased apart.  We find that the proof
             ;; above is exactly a proof of:
             ;;
             ;;   (B/[Xi<-Ai])/[Vi<-Ti] = (B/[Xi<-Ai])/[Vi<-Si]             (*2)
             ;;
             ;; We can now derive our goal, x/[Vi<-Ti] = x/[Vi<-Si], as follows:
             ;;
             ;;    1. x = B/[Xi<-Ai]                                  Beta Reduction
             ;;    2. x/[Vi<-Ti] = (B/[Xi<-Ai])/[Vi<-Ti]              Instantiation; 1   a=b
             ;;    3. (B/[Xi<-Ai])/[Vi<-Ti] = (B/[Xi<-Ai])/[Vi<-Si]   By *2              b=d
             ;;    4. x/[Vi<-Si] = (B/[Xi<-Ai])/[Vi<-Si]              Instantiation; 1   c=d
             ;;    5. x/[Vi<-Ti] = x/[Vi<-Si]                         Lemma; 2,3,4
             (let* ((ti=si*   (logic.strip-conclusions proofs))
                    (line-1   (build.beta-reduction (logic.lambda-formals x)
                                                    (logic.lambda-body x)
                                                    (logic.lambda-actuals x))))
               (build.dual-substitution-lemma-1
                (build.instantiation line-1 (pair-lists vars (logic.=lhses ti=si*)))
                (build.flag-dual-substitution 'term (logic.lambda-body x) (logic.lambda-formals x)
                                              (build.flag-dual-substitution 'list (logic.lambda-actuals x) vars proofs))
                (build.instantiation line-1 (pair-lists vars (logic.=rhses ti=si*))))))

            (t
             ;; sneaky hack so that it's always iff to t.
             t))
    ;; List case.
    (if (consp x)
        (cons (build.flag-dual-substitution 'term (car x) vars proofs)
              (build.flag-dual-substitution 'list (cdr x) vars proofs))
      nil)))

(definlined build.dual-substitution (x vars proofs)
  (declare (xargs :guard (and (logic.termp x)
                               (logic.variable-listp vars)
                               (uniquep vars)
                               (logic.appeal-listp proofs)
                               (same-lengthp vars proofs)
                               (logic.all-atomicp (logic.strip-conclusions proofs)))
                   :verify-guards nil))
  (build.flag-dual-substitution 'term x vars proofs))

(definlined build.dual-substitution-list (x vars proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.variable-listp vars)
                              (uniquep vars)
                              (logic.appeal-listp proofs)
                              (same-lengthp vars proofs)
                              (logic.all-atomicp (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (build.flag-dual-substitution 'list x vars proofs))


(defthmd definition-of-build.dual-substitution
  (equal (build.dual-substitution x vars proofs)
         (cond ((logic.constantp x)
                (build.reflexivity x))
               ((logic.variablep x)
                (let ((index (first-index x vars)))
                  (if (equal index (len vars))
                      (build.reflexivity x)
                    (logic.appeal-identity (nth index proofs)))))
               ((logic.functionp x)
                (build.pequal-by-args (logic.function-name x)
                                      (build.dual-substitution-list (logic.function-args x) vars proofs)))
               ((logic.lambdap x)
                (let* ((ti=si*   (logic.strip-conclusions proofs))
                       (line-1   (build.beta-reduction (logic.lambda-formals x)
                                                       (logic.lambda-body x)
                                                       (logic.lambda-actuals x))))
                  (build.dual-substitution-lemma-1
                   (build.instantiation line-1 (pair-lists vars (logic.=lhses ti=si*)))
                   (build.flag-dual-substitution 'term (logic.lambda-body x) (logic.lambda-formals x)
                                                 (build.flag-dual-substitution 'list (logic.lambda-actuals x) vars proofs))
                   (build.instantiation line-1 (pair-lists vars (logic.=rhses ti=si*))))))
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.dual-substitution
                                    build.dual-substitution-list))))

(defthmd definition-of-build.dual-substitution-list
  (equal (build.dual-substitution-list x vars proofs)
         (if (consp x)
             (cons (build.dual-substitution (car x) vars proofs)
                   (build.dual-substitution-list (cdr x) vars proofs))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.dual-substitution
                                    build.dual-substitution-list))))

(defobligations build.dual-substitution
  (build.reflexivity
   build.pequal-by-args
   build.beta-reduction
   build.instantiation
   build.dual-substitution-lemma-1))

(defobligations build.dual-substitution-list
  (build.dual-substitution))

(defthm build.flag-dual-substitution-of-term-removal
  (equal (build.flag-dual-substitution 'term x vars proofs)
         (build.dual-substitution x vars proofs))
  :hints(("Goal" :in-theory (enable build.dual-substitution))))

(defthm build.flag-dual-substitution-of-list-removal
  (equal (build.flag-dual-substitution 'list x vars proofs)
         (build.dual-substitution-list x vars proofs))
  :hints(("Goal" :in-theory (enable build.dual-substitution-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.dual-substitution))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.dual-substitution-list))))




(defthm build.dual-substitution-under-iff
  (iff (build.dual-substitution x vars proofs)
       t)
  :hints(("Goal" :use ((:instance definition-of-build.dual-substitution)))))

(defthm build.dual-substitution-list-when-not-consp
  (implies (not (consp x))
           (equal (build.dual-substitution-list x vars proofs)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-build.dual-substitution-list))))

(defthm build.dual-substitution-list-of-cons
  (equal (build.dual-substitution-list (cons a x) vars proofs)
         (cons (build.dual-substitution a vars proofs)
               (build.dual-substitution-list x vars proofs)))
  :hints(("Goal" :in-theory (enable definition-of-build.dual-substitution-list))))

(defthm len-of-build.dual-substitution-list
  (equal (len (build.dual-substitution-list x vars proofs))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :shared-hyp (force (and (logic.variable-listp vars)
                          (uniquep vars)
                          (logic.appeal-listp proofs)
                          (equal (len vars) (len proofs))
                          (logic.all-atomicp (logic.strip-conclusions proofs))))
  :thms ((term forcing-logic.appealp-of-build.dual-substitution
               (implies (force (logic.termp x))
                        (equal (logic.appealp (build.dual-substitution x vars proofs))
                               t)))
         (term forcing-logic.conclusion-of-build.dual-substitution
               (implies (force (logic.termp x))
                        (equal (logic.conclusion (build.dual-substitution x vars proofs))
                               (logic.pequal
                                (logic.substitute x (pair-lists vars (logic.=lhses (logic.strip-conclusions proofs))))
                                (logic.substitute x (pair-lists vars (logic.=rhses (logic.strip-conclusions proofs))))))))
         (t forcing-logic.appealp-listp-of-build.dual-substitution-list
            (implies (force (logic.term-listp x))
                     (equal (logic.appeal-listp (build.dual-substitution-list x vars proofs))
                            t)))
         (t forcing-logic.strip-conclusions-of-build.dual-substitution-list
            (implies (force (logic.term-listp x))
                     (equal (logic.strip-conclusions (build.dual-substitution-list x vars proofs))
                            (logic.pequal-list
                             (logic.substitute-list x (pair-lists vars (logic.=lhses (logic.strip-conclusions proofs))))
                             (logic.substitute-list x (pair-lists vars (logic.=rhses (logic.strip-conclusions proofs)))))))))
  :hints (("Goal"
           :restrict ((definition-of-build.dual-substitution ((x x))))
           :in-theory (e/d (definition-of-build.dual-substitution)
                           (forcing-lookup-of-logic.function-name))
           :induct (build.flag-dual-substitution flag x vars proofs))))

(verify-guards build.flag-dual-substitution
               :hints(("Goal" :in-theory (disable forcing-lookup-of-logic.function-name))))
(verify-guards build.dual-substitution)
(verify-guards build.dual-substitution-list)

(defthms-flag
  :@contextp t
  :shared-hyp (force (and (logic.variable-listp vars)
                          (uniquep vars)
                          (logic.appeal-listp proofs)
                          (logic.proof-listp proofs axioms thms atbl)
                          (equal (len vars) (len proofs))
                          (logic.all-atomicp (logic.strip-conclusions proofs))))
  :thms ((term forcing-logic.proofp-of-build.dual-substitution
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (@obligations build.dual-substitution)))
                        (equal (logic.proofp (build.dual-substitution x vars proofs) axioms thms atbl)
                               t)))
         (t forcing-logic.proof-listp-of-build.dual-substitution-list
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)
                                 (@obligations build.dual-substitution-list)))
                     (equal (logic.proof-listp (build.dual-substitution-list x vars proofs) axioms thms atbl)
                            t))))
  :hints (("Goal"
           :restrict ((definition-of-build.dual-substitution ((x x))))
           :in-theory (enable definition-of-build.dual-substitution)
           :induct (build.flag-dual-substitution flag x vars proofs))))




(defund build.lambda-pequal-by-args (formals body proofs)
  ;; Derive ((lambda (x1...xn) B) t1...tn) = ((lambda (x1...xn) B) s1...sn) from t1 = s1, ..., tn = sn
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.appeal-listp proofs)
                              (same-lengthp proofs formals)
                              (logic.all-atomicp (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((conclusions (logic.strip-conclusions proofs)) ;; (t1 = s1, ..., tn = sn)
         (t*          (logic.=lhses conclusions))       ;; (t1, ..., tn)
         (s*          (logic.=rhses conclusions)))      ;; (s1, ..., sn)
    (if (equal t* s*)
        ;; Optimization. As with build.pequal-by-args, if all of the arguments
        ;; are identical, we will just use reflexivity to build the proof.
        (build.reflexivity (logic.lambda formals body t*))

      ;; Otherwise, we use the following derivation.
      ;;
      ;;   1. ((lambda (x1...xn) B) t1...tn) = B/[Xi<-Ti]                       Beta reduction
      ;;   2. B/[Xi<-Ti] = B/[Xi<-Si]                                           Dual substitution
      ;;   3. ((lambda (x1...xn) B) t1...tn) = B/[Xi<-Si]                       Trans =; 1,2
      ;;   4. ((lambda (x1...xn) B) s1...sn) = B/[Xi<-Si]                       Beta reduction
      ;;   5. B/[Xi<-Si] = ((lambda (x1...xn) B) s1...sn)                       Commute =; 4
      ;;   6. ((lambda (x1...xn) B) t1...tn) = ((lambda (x1...xn) B) s1...sn)   Trans =; 3,5
      ;;
      ;; Q.E.D.
      (let* ((line-1 (build.beta-reduction formals body t*))
             (line-2 (build.dual-substitution body formals proofs))
             (line-3 (build.transitivity-of-pequal line-1 line-2))
             (line-4 (build.beta-reduction formals body s*))
             (line-5 (build.commute-pequal line-4))
             (line-6 (build.transitivity-of-pequal line-3 line-5)))
        line-6))))

(defobligations build.lambda-pequal-by-args
  (build.reflexivity
   build.beta-reduction
   build.dual-substitution
   build.transitivity-of-pequal
   build.commute-pequal
   build.transitivity-of-pequal))

(encapsulate
 ()
 (local (in-theory (enable build.lambda-pequal-by-args)))

 (defthm build.lambda-pequal-by-args-under-iff
   (iff (build.lambda-pequal-by-args formals body proofs)
        t))

 (defthm forcing-logic.appealp-of-build.lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (equal (len proofs) (len formals))
                        (logic.all-atomicp (logic.strip-conclusions proofs))))
            (equal (logic.appealp (build.lambda-pequal-by-args formals body proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-build.lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (equal (len proofs) (len formals))
                        (logic.all-atomicp (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (build.lambda-pequal-by-args formals body proofs))
                   (logic.pequal (logic.lambda formals body (logic.=lhses (logic.strip-conclusions proofs)))
                                 (logic.lambda formals body (logic.=rhses (logic.strip-conclusions proofs))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (logic.term-atblp body atbl)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (len proofs) (len formals))
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (@obligations build.lambda-pequal-by-args)))
            (equal (logic.proofp (build.lambda-pequal-by-args formals body proofs) axioms thms atbl)
                   t)))

 (verify-guards build.lambda-pequal-by-args))



(defund build.lambda-pequal-by-args-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.lambda-pequal-by-args)
         (tuplep 2 extras)
         (let ((formals (first extras))
               (body    (second extras)))
           (and (true-listp formals)
                (logic.variable-listp formals)
                (uniquep formals)
                (logic.termp body)
                (logic.term-atblp body atbl)
                (subsetp (logic.term-vars body) formals)
                (same-lengthp subproofs formals)
                (logic.all-atomicp-of-strip-conclusions subproofs)
                (equal conclusion
                       (logic.pequal (logic.lambda formals body (logic.=lhses-of-strip-conclusions subproofs))
                                     (logic.lambda formals body (logic.=rhses-of-strip-conclusions subproofs)))))))))

(defund build.lambda-pequal-by-args-high (formals body proofs)
  ;; BOZO we could add a true-listp restriction to proofs to avoid the list-fix
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.appeal-listp proofs)
                              (same-lengthp proofs formals)
                              (logic.all-atomicp (logic.strip-conclusions proofs)))))
  (logic.appeal 'build.lambda-pequal-by-args
                (logic.pequal (logic.lambda formals body (logic.=lhses-of-strip-conclusions proofs))
                              (logic.lambda formals body (logic.=rhses-of-strip-conclusions proofs)))
                (list-fix proofs)
                (list formals body)))

(encapsulate
 ()
 (local (in-theory (enable build.lambda-pequal-by-args-okp)))

 (defthm booleanp-of-build.lambda-pequal-by-args-okp
   (equal (booleanp (build.lambda-pequal-by-args-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm build.lambda-pequal-by-args-okp-of-logic.appeal-identity
   (equal (build.lambda-pequal-by-args-okp (logic.appeal-identity x) atbl)
          (build.lambda-pequal-by-args-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthm lemma-1-for-soundness-of-build.lambda-pequal-by-args-okp
   (implies (and (build.lambda-pequal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (build.lambda-pequal-by-args
                                      (first (logic.extras x))
                                      (second (logic.extras x))
                                      (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                   axioms thms atbl)))
                   (logic.conclusion x))))

 (defthm@ lemma-2-for-soundness-of-build.lambda-pequal-by-args-okp
   (implies (and (build.lambda-pequal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations build.lambda-pequal-by-args))
            (equal (logic.proofp (build.lambda-pequal-by-args
                                  (first (logic.extras x))
                                  (second (logic.extras x))
                                  (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                               axioms thms atbl))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-build.lambda-pequal-by-args-okp
   (implies (and (build.lambda-pequal-by-args-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations build.lambda-pequal-by-args))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.lambda-pequal-by-args-okp
                               lemma-2-for-soundness-of-build.lambda-pequal-by-args-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.lambda-pequal-by-args
                                 (first (logic.extras x))
                                 (second (logic.extras x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl)))))))))








(defderiv build.disjoined-dual-substitution-lemma-1
  :from   ((proof x (v P (= (? a) (? b))))
           (proof y (v P (= (? b) (? d))))
           (proof z (v P (= (? c) (? d)))))
  :derive (v P (= (? a) (? c)))
  :proof  (@derive
           ((v P (= (? a) (? b)))    (@given x))
           ((v P (= (? b) (? d)))    (@given y))
           ((v P (= (? a) (? d)))    (build.disjoined-transitivity-of-pequal @-- @-)  *1)
           ((v P (= (? c) (? d)))    (@given z))
           ((v P (= (? d) (? c)))    (build.disjoined-commute-pequal @-))
           ((v P (= (? a) (? c)))    (build.disjoined-transitivity-of-pequal *1 @-))))


(defun build.flag-disjoined-dual-substitution (flag x vars p proofs)
   ;;
   ;;     P v t1 = s1
   ;;     ...
   ;;     P v tn = sn
   ;;   -----------------------------------------------------
   ;;     P v x/[v1<-t1, ..., vn<-tn] = x/[v1<-s1, ..., vn<-sn]
   ;;
   ;; - x is the term we are instantiating
   ;; - vars are the list of variables (v1 ... vn) from above
   ;; - p is explicitly given; we can't extract it if proofs is empty
   ;; - proofs are the givens, i.e., proofs of (t1 = s1, ..., tn = sn)
   ;;
   ;; Note: we don't comment this proof since it's almost identical to the one
   ;; in build.flag-dual-substitution.  So see the comments there instead.
   (declare (xargs :guard (and (if (equal flag 'term)
                                   (logic.termp x)
                                 (and (equal flag 'list)
                                      (logic.term-listp x)))
                               (logic.variable-listp vars)
                               (uniquep vars)
                               (logic.formulap p)
                               (logic.appeal-listp proofs)
                               (equal (len vars) (len proofs))
                               (let ((conclusions (logic.strip-conclusions proofs)))
                                 (and (logic.all-disjunctionsp conclusions)
                                      (all-equalp p (logic.vlhses conclusions))
                                      (logic.all-atomicp (logic.vrhses conclusions)))))
                   :verify-guards nil))
   (if (equal flag 'term)
       (cond ((logic.constantp x)
              (build.expansion p (build.reflexivity x)))
             ((logic.variablep x)
              (let ((index (first-index x vars)))
                (if (equal index (len vars))
                    (build.expansion p (build.reflexivity x))
                  (logic.appeal-identity (nth index proofs)))))
             ((logic.functionp x)
              (let ((name (logic.function-name x))
                    (args (logic.function-args x)))
                (build.disjoined-pequal-by-args name p (build.flag-disjoined-dual-substitution 'list args vars p proofs))))
             ((logic.lambdap x)
              (let* ((ti=si*   (logic.vrhses (logic.strip-conclusions proofs)))
                     (line-1   (build.beta-reduction (logic.lambda-formals x)
                                                     (logic.lambda-body x)
                                                     (logic.lambda-actuals x))))
              (build.disjoined-dual-substitution-lemma-1
               (build.expansion p (build.instantiation line-1 (pair-lists vars (logic.=lhses ti=si*))))
               (build.flag-disjoined-dual-substitution 'term
                                                           (logic.lambda-body x)
                                                           (logic.lambda-formals x)
                                                           p
                                                           (build.flag-disjoined-dual-substitution 'list
                                                                                                       (logic.lambda-actuals x)
                                                                                                       vars
                                                                                                       p
                                                                                                       proofs))
               (build.expansion p (build.instantiation line-1 (pair-lists vars (logic.=rhses ti=si*)))))))
             (t t))
     (if (consp x)
         (cons (build.flag-disjoined-dual-substitution 'term (car x) vars p proofs)
               (build.flag-disjoined-dual-substitution 'list (cdr x) vars p proofs))
       nil)))

(definlined build.disjoined-dual-substitution (x vars p proofs)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.variable-listp vars)
                              (uniquep vars)
                              (logic.formulap p)
                              (logic.appeal-listp proofs)
                              (equal (len vars) (len proofs))
                              (let ((conclusions (logic.strip-conclusions proofs)))
                                (and (logic.all-disjunctionsp conclusions)
                                     (all-equalp p (logic.vlhses conclusions))
                                     (logic.all-atomicp (logic.vrhses conclusions)))))
                  :verify-guards nil))
  (build.flag-disjoined-dual-substitution 'term x vars p proofs))

(definlined build.disjoined-dual-substitution-list (x vars p proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (logic.variable-listp vars)
                              (uniquep vars)
                              (logic.formulap p)
                              (logic.appeal-listp proofs)
                              (equal (len vars) (len proofs))
                              (let ((conclusions (logic.strip-conclusions proofs)))
                                (and (logic.all-disjunctionsp conclusions)
                                     (all-equalp p (logic.vlhses conclusions))
                                     (logic.all-atomicp (logic.vrhses conclusions)))))
                  :verify-guards nil))
  (build.flag-disjoined-dual-substitution 'list x vars p proofs))

(defthmd definition-of-build.disjoined-dual-substitution
  (equal (build.disjoined-dual-substitution x vars p proofs)
         (cond ((logic.constantp x)
                (build.expansion p (build.reflexivity x)))
               ((logic.variablep x)
                (let ((index (first-index x vars)))
                  (if (equal index (len vars))
                      (build.expansion p (build.reflexivity x))
                    (logic.appeal-identity (nth index proofs)))))
               ((logic.functionp x)
                (let ((name (logic.function-name x))
                      (args (logic.function-args x)))
                  (build.disjoined-pequal-by-args name p (build.disjoined-dual-substitution-list args vars p proofs))))
               ((logic.lambdap x)
                (let* ((ti=si*   (logic.vrhses (logic.strip-conclusions proofs)))
                       (line-1   (build.beta-reduction (logic.lambda-formals x)
                                                       (logic.lambda-body x)
                                                       (logic.lambda-actuals x))))
                  (build.disjoined-dual-substitution-lemma-1
                   (build.expansion p (build.instantiation line-1 (pair-lists vars (logic.=lhses ti=si*))))
                   (build.disjoined-dual-substitution (logic.lambda-body x) (logic.lambda-formals x) p
                                                          (build.disjoined-dual-substitution-list (logic.lambda-actuals x) vars p proofs))
                   (build.expansion p (build.instantiation line-1 (pair-lists vars (logic.=rhses ti=si*)))))))
               (t t)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.disjoined-dual-substitution
                                    build.disjoined-dual-substitution-list))))

(defthmd definition-of-build.disjoined-dual-substitution-list
  (equal (build.disjoined-dual-substitution-list x vars p proofs)
         (if (consp x)
             (cons (build.disjoined-dual-substitution (car x) vars p proofs)
                   (build.disjoined-dual-substitution-list (cdr x) vars p proofs))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable build.disjoined-dual-substitution
                                    build.disjoined-dual-substitution-list))))


(defobligations build.disjoined-dual-substitution
  (build.expansion
   build.reflexivity
   build.disjoined-pequal-by-args
   build.beta-reduction
   build.instantiation
   build.disjoined-transitivity-of-pequal
   build.commute-pequal))

(defobligations build.disjoined-dual-substitution-list
  (build.disjoined-dual-substitution))

(defthm build.flag-disjoined-dual-substitution-of-term-removal
  (equal (build.flag-disjoined-dual-substitution 'term x vars p proofs)
         (build.disjoined-dual-substitution x vars p proofs))
  :hints(("Goal" :in-theory (enable build.disjoined-dual-substitution))))

(defthm build.flag-disjoined-dual-substitution-of-list-removal
  (equal (build.flag-disjoined-dual-substitution 'list x vars p proofs)
         (build.disjoined-dual-substitution-list x vars p proofs))
  :hints(("Goal" :in-theory (enable build.disjoined-dual-substitution-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.disjoined-dual-substitution))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition build.disjoined-dual-substitution-list))))

(defthm forcing-build.disjoined-dual-substitution-under-iff
  (iff (build.disjoined-dual-substitution x vars p proofs)
       t)
  :hints(("Goal" :use ((:instance definition-of-build.disjoined-dual-substitution)))))

(defthm build.disjoined-dual-substitution-list-when-not-consp
  (implies (not (consp x))
           (equal (build.disjoined-dual-substitution-list x vars p proofs)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-build.disjoined-dual-substitution-list))))

(defthm build.disjoined-dual-substitution-list-of-cons
  (equal (build.disjoined-dual-substitution-list (cons a x) vars p proofs)
         (cons (build.disjoined-dual-substitution a vars p proofs)
               (build.disjoined-dual-substitution-list x vars p proofs)))
  :hints(("Goal" :in-theory (enable definition-of-build.disjoined-dual-substitution-list))))

(defthm len-of-build.disjoined-dual-substitution-list
  (equal (len (build.disjoined-dual-substitution-list x vars p proofs))
         (len x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthms-flag
  :shared-hyp (force (and (logic.variable-listp vars)
                          (uniquep vars)
                          (logic.formulap p)
                          (logic.appeal-listp proofs)
                          (equal (len vars) (len proofs))
                          (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                          (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                          (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))))
  :thms ((term forcing-logic.appealp-of-build.disjoined-dual-substitution
               (implies (force (logic.termp x))
                        (equal (logic.appealp (build.disjoined-dual-substitution x vars p proofs))
                               t)))
         (term forcing-logic.conclusion-of-build.disjoined-dual-substitution
               (implies (force (logic.termp x))
                        (equal (logic.conclusion (build.disjoined-dual-substitution x vars p proofs))
                               (logic.por p (logic.pequal (logic.substitute x (pair-lists vars (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                                                          (logic.substitute x (pair-lists vars (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))))))))
         (t forcing-logic.appeal-listp-of-build.disjoined-dual-substitution
            (implies (force (logic.term-listp x))
                     (equal (logic.appeal-listp (build.disjoined-dual-substitution-list x vars p proofs))
                            t)))
         (t forcing-logic.strip-conclusions-of-build.disjoined-dual-substitution
            (implies (force (logic.term-listp x))
                     (equal (logic.strip-conclusions (build.disjoined-dual-substitution-list x vars p proofs))
                            (logic.por-list (repeat p (len x))
                                            (logic.pequal-list
                                             (logic.substitute-list x (pair-lists vars (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                                             (logic.substitute-list x (pair-lists vars (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs)))))))))))
  :hints (("Goal"
           :in-theory (enable definition-of-build.disjoined-dual-substitution)
           :induct (build.flag-disjoined-dual-substitution flag x vars p proofs))))

(verify-guards build.flag-disjoined-dual-substitution)
(verify-guards build.disjoined-dual-substitution)
(verify-guards build.disjoined-dual-substitution-list)

(defthms-flag
  :@contextp t
  :shared-hyp (force (and (logic.variable-listp vars)
                          (uniquep vars)
                          (logic.formulap p)
                          (logic.formula-atblp p atbl)
                          (logic.appeal-listp proofs)
                          (equal (len vars) (len proofs))
                          (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                          (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                          (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                          (logic.proof-listp proofs axioms thms atbl)))
  :thms ((term forcing-logic.proofp-of-build.disjoined-dual-substitution
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)
                                    (logic.proof-listp proofs axioms thms atbl)
                                    (@obligations build.disjoined-dual-substitution)))
                        (equal (logic.proofp (build.disjoined-dual-substitution x vars p proofs) axioms thms atbl)
                               t)))
         (t forcing-logic.proof-listp-of-build.disjoined-dual-substitution
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)
                                 (logic.proof-listp proofs axioms thms atbl)
                                 (@obligations build.disjoined-dual-substitution-list)))
                     (equal (logic.proof-listp (build.disjoined-dual-substitution-list x vars p proofs) axioms thms atbl)
                            t))))
  :hints (("Goal"
           :in-theory (enable definition-of-build.disjoined-dual-substitution)
           :induct (build.flag-disjoined-dual-substitution flag x vars p proofs))))



(defund build.disjoined-lambda-pequal-by-args (formals body p proofs)
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.formulap p)
                              (logic.appeal-listp proofs)
                              (equal (len proofs) (len formals))
                              (let ((conclusions (logic.strip-conclusions proofs)))
                                (and (logic.all-disjunctionsp conclusions)
                                     (all-equalp p (logic.vlhses conclusions))
                                     (logic.all-atomicp (logic.vrhses conclusions)))))))
  (let* ((ti=si* (logic.vrhses (logic.strip-conclusions proofs)))
         (ti*    (logic.=lhses ti=si*))
         (si*    (logic.=rhses ti=si*)))
    (if (equal ti* si*)
        ;; Optimization.  If all the args are identical, we can just use
        ;; reflexivity and expansion to build the proof.
        (build.expansion p (build.reflexivity (logic.lambda formals body ti*)))

      ;; Otherwise, we use the following derivation:
      ;;
      ;;   1. P v ((lambda (x1...xn) B) t1...tn) = B/[Xi<-Ti]                       Beta reduction, expansion
      ;;   2. P v B/[Xi<-Ti] = B/[Xi<-Si]                                           DJ Dual Substitution
      ;;   3. P v ((lambda (x1...xn) B) t1...tn) = B/[Xi<-Si]                       DJ Trans =; 1,2
      ;;   4. P v B/[Xi<-Si] = ((lambda (x1...xn) B) s1...sn)                       Beta, commute =, expansion
      ;;   5. P v ((lambda (x1...xn) B) t1...tn) = ((lambda (x1...xn) B) s1...sn)   DJ Trans =; 3,4
      ;;
      ;; Q.E.D.
      (let* ((line-1 (build.expansion p (build.beta-reduction formals body ti*)))
             (line-2 (build.disjoined-dual-substitution body formals p proofs))
             (line-3 (build.disjoined-transitivity-of-pequal line-1 line-2))
             (line-4 (build.expansion p (build.commute-pequal (build.beta-reduction formals body si*))))
             (line-5 (build.disjoined-transitivity-of-pequal line-3 line-4)))
        line-5))))

(defobligations build.disjoined-lambda-pequal-by-args
  (build.expansion
   build.reflexivity
   build.disjoined-dual-substitution
   build.disjoined-transitivity-of-pequal
   build.commute-pequal
   build.beta-reduction))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-lambda-pequal-by-args)))

 (defthm forcing-build.disjoined-lambda-pequal-by-args-under-iff
   (iff (build.disjoined-lambda-pequal-by-args formals body p proofs)
        t))

 (defthm forcing-logic.appealp-of-build.disjoined-lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap p)
                        (logic.appeal-listp proofs)
                        (equal (len proofs) (len formals))
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))))
            (equal (logic.appealp (build.disjoined-lambda-pequal-by-args formals body p proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap p)
                        (logic.appeal-listp proofs)
                        (equal (len proofs) (len formals))
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))))
            (equal (logic.conclusion (build.disjoined-lambda-pequal-by-args formals body p proofs))
                   (logic.por p (logic.pequal
                                 (logic.lambda formals body (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                                 (logic.lambda formals body (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.disjoined-lambda-pequal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap p)
                        (logic.appeal-listp proofs)
                        (equal (len proofs) (len formals))
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        ;; ---
                        (logic.term-atblp body atbl)
                        (logic.formula-atblp p atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations build.disjoined-lambda-pequal-by-args)))
            (equal (logic.proofp (build.disjoined-lambda-pequal-by-args formals body p proofs) axioms thms atbl)
                   t))))



(defund build.disjoined-lambda-pequal-by-args-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.disjoined-lambda-pequal-by-args)
         (tuplep 2 extras)
         (let ((formals (first extras))
               (body    (second extras)))
           (and (true-listp formals)
                (logic.variable-listp formals)
                (uniquep formals)
                (logic.termp body)
                (logic.term-atblp body atbl)
                (subsetp (logic.term-vars body) formals)
                (same-lengthp subproofs formals)
                (logic.all-disjunctionsp-of-strip-conclusions subproofs)
                (logic.all-atomicp-of-vrhses-of-strip-conclusions subproofs)
                (equal (logic.fmtype conclusion) 'por*)
                (logic.formula-atblp (logic.vlhs conclusion) atbl)
                ;; BOZO efficiency -- add an all-equalp-of-vlhses-of-strip-conclusions
                (all-equalp (logic.vlhs conclusion) (logic.vlhses-of-strip-conclusions subproofs))
                (equal (logic.vrhs conclusion)
                       (logic.pequal (logic.lambda formals body (logic.=lhses-of-vrhses-of-strip-conclusions subproofs))
                                     (logic.lambda formals body (logic.=rhses-of-vrhses-of-strip-conclusions subproofs)))))))))

(defund build.disjoined-lambda-pequal-by-args-high (formals body p proofs)
  ;; BOZO we could add a true-listp restriction to proofs to avoid the list-fix
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.formulap p)
                              (logic.appeal-listp proofs)
                              (equal (len proofs) (len formals))
                              (let ((conclusions (logic.strip-conclusions proofs)))
                                (and (logic.all-disjunctionsp conclusions)
                                     (all-equalp p (logic.vlhses conclusions))
                                     (logic.all-atomicp (logic.vrhses conclusions)))))))
  (logic.appeal 'build.disjoined-lambda-pequal-by-args
                (logic.por p (logic.pequal (logic.lambda formals body (logic.=lhses-of-vrhses-of-strip-conclusions proofs))
                                           (logic.lambda formals body (logic.=rhses-of-vrhses-of-strip-conclusions proofs))))
                (list-fix proofs)
                (list formals body)))


(encapsulate
 ()
 (local (in-theory (enable build.disjoined-lambda-pequal-by-args-okp)))

 (defthm booleanp-of-build.disjoined-lambda-pequal-by-args-okp
   (equal (booleanp (build.disjoined-lambda-pequal-by-args-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm build.disjoined-lambda-pequal-by-args-okp-of-logic.appeal-identity
   (equal (build.disjoined-lambda-pequal-by-args-okp (logic.appeal-identity x) atbl)
          (build.disjoined-lambda-pequal-by-args-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthm lemma-1-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
   (implies (and (build.disjoined-lambda-pequal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (build.disjoined-lambda-pequal-by-args
                                      (first (logic.extras x))
                                      (second (logic.extras x))
                                      (logic.vlhs (logic.conclusion x))
                                      (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                   axioms thms atbl)))
                   (logic.conclusion x))))

 (defthm@ lemma-2-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
   (implies (and (build.disjoined-lambda-pequal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations build.disjoined-lambda-pequal-by-args))
            (equal (logic.proofp (build.disjoined-lambda-pequal-by-args
                                  (first (logic.extras x))
                                  (second (logic.extras x))
                                  (logic.vlhs (logic.conclusion x))
                                  (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                               axioms thms atbl))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-build.disjoined-lambda-pequal-by-args-okp
   (implies (and (build.disjoined-lambda-pequal-by-args-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations build.disjoined-lambda-pequal-by-args))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp
                               lemma-2-for-soundness-of-build.disjoined-lambda-pequal-by-args-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.disjoined-lambda-pequal-by-args
                                 (first (logic.extras x))
                                 (second (logic.extras x))
                                 (logic.vlhs (logic.conclusion x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl)))))))))





(dd.close)
