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
(include-book "lift")
(include-book "casesplit-bldr")
(include-book "../update-clause-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund clause.lift-term1-bldr (x)
  (declare (xargs :guard (logic.termp x)
                  :verify-guards nil))
  (cond ((logic.constantp x)
         (build.reflexivity x))
        ((logic.variablep x)
         (build.reflexivity x))
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (if (and (equal name 'if)
                    (equal (len args) 3))
               (build.pequal-by-args 'if
                                     (list (clause.lift-term1-bldr (first args))
                                           (clause.lift-term1-bldr (second args))
                                           (clause.lift-term1-bldr (third args))))
             (if (clause.simple-term-listp args)
                 (build.reflexivity x)
               (clause.cases-bldr x (clause.simple-tests x) nil)))))
        ((logic.lambdap x)
         (let ((actuals (logic.lambda-actuals x)))
           (if (clause.simple-term-listp actuals)
               (build.reflexivity x)
             (clause.cases-bldr x (clause.simple-tests x) nil))))
        (t nil)))

(defobligations clause.lift-term1-bldr
  (build.reflexivity build.pequal-by-args clause.cases-bldr))

(encapsulate
 ()
 (defthm lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr
   (implies (logic.termp x)
            (and (logic.appealp (clause.lift-term1-bldr x))
                 (equal (logic.conclusion (clause.lift-term1-bldr x))
                        (logic.pequal x (clause.lift-term1 x)))))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (enable clause.lift-term1-bldr clause.lift-term1)
           :induct (clause.lift-term1-bldr x))))

 (defthm forcing-logic.appealp-of-clause.lift-term1-bldr
   (implies (force (logic.termp x))
            (equal (logic.appealp (clause.lift-term1-bldr x))
                   t))
   :hints (("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr)))))

 (defthm forcing-logic.conclusion-of-clause.lift-term1-bldr
   (implies (force (logic.termp x))
            (equal (logic.conclusion (clause.lift-term1-bldr x))
                   (logic.pequal x (clause.lift-term1 x))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints (("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr))))))

(verify-guards clause.lift-term1-bldr)

(defthm@ forcing-logic.proofp-of-clause.lift-term1-bldr
  (implies (force (and (logic.termp x)
                       ;; ---
                       (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.lift-term1-bldr)))
           (equal (logic.proofp (clause.lift-term1-bldr x) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (enable clause.lift-term1-bldr)
          :induct (clause.lift-term1-bldr x))))




(defund clause.lift-term-bldr (x)
  (declare (xargs :guard (logic.termp x)
                  :measure (clause.depth-list (clause.unlifted-subterms x))
                  :verify-guards nil))
  (if (and (logic.termp x)
           (not (clause.lifted-termp x)))
      (let* ((step-proof (clause.lift-term1-bldr x))             ;; x = x'
             (x-prime (logic.=rhs (logic.conclusion step-proof))))
        (if (clause.lifted-termp x-prime)
            ;; Optimization: don't bother to do the transitivity step if x' is
            ;; lifted, since lifting x' will just give us x'
            step-proof
          (build.transitivity-of-pequal step-proof (clause.lift-term-bldr x-prime))))
    (build.reflexivity x)))

(defobligations clause.lift-term-bldr
  (clause.lift-term1-bldr build.transitivity-of-pequal build.reflexivity))

(encapsulate
 ()
 (defthm lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr
   (implies (logic.termp x)
            (and (logic.appealp (clause.lift-term-bldr x))
                 (equal (logic.conclusion (clause.lift-term-bldr x))
                        (logic.pequal x (clause.lift-term x)))))
   :rule-classes nil
   :hints(("Goal" :in-theory (enable clause.lift-term-bldr clause.lift-term))))

 (defthm forcing-logic.appealp-of-clause.lift-term-bldr
   (implies (force (logic.termp x))
            (equal (logic.appealp (clause.lift-term-bldr x))
                   t))
   :hints (("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr)))))

 (defthm forcing-logic.conclusion-of-clause.lift-term-bldr
   (implies (force (logic.termp x))
            (equal (logic.conclusion (clause.lift-term-bldr x))
                   (logic.pequal x (clause.lift-term x))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints (("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr))))))

(verify-guards clause.lift-term-bldr)

(defthm@ forcing-logic.proofp-of-clause.lift-term-bldr
  (implies (force (and (logic.termp x)
                       ;; ---
                       (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.lift-term-bldr)))
           (equal (logic.proofp (clause.lift-term-bldr x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term-bldr))))





(defprojection :list (clause.lift-term-list-bldr x)
               :element (clause.lift-term-bldr x)
               :guard (logic.term-listp x))

(defobligations clause.lift-term-list-bldr
  (clause.lift-term-bldr))

(defthm forcing-logic.appeal-listp-of-clause.lift-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.appeal-listp (clause.lift-term-list-bldr x))
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term-list-bldr))))

(defthm forcing-logic.strip-conclusions-of-clause.lift-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.strip-conclusions (clause.lift-term-list-bldr x))
                  (logic.pequal-list x (clause.lift-term-list x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable clause.lift-term-list-bldr))))

(defthm@ forcing-logic.proof-listp-of-clause.lift-term-list-bldr
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.lift-term-list-bldr)))
           (equal (logic.proof-listp (clause.lift-term-list-bldr x) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term-list-bldr))))




(defun clause.lift-clauses-bldr (x proofs)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (clause.lift-term-list-list x))))))
  (if (consp x)
      (let* ((lift-proofs  (clause.lift-term-list-bldr (car x)))
             (lift-terms   (clause.lift-term-list (car x)))
             (update-proof (clause.update-clause-bldr lift-terms (car proofs) lift-proofs)))
        (ACL2::prog2$
         (ACL2::cw! ";; Lift step: ~s0~|"
                    (STR::ncat "Input " (unbounded-rank (car proofs))
                               "; Lift " (unbounded-rank lift-proofs)
                               "; Update " (- (unbounded-rank update-proof)
                                              (ACL2::+ (unbounded-rank lift-proofs)
                                                       (unbounded-rank (car proofs))))
                               "; Output " (unbounded-rank update-proof)))
         (cons update-proof
               (clause.lift-clauses-bldr (cdr x) (cdr proofs)))))
    nil))

(defobligations clause.lift-clauses-bldr
  (clause.update-clause-bldr
   clause.lift-term-list-bldr))

(encapsulate
 ()
 (assume (force (and (logic.term-list-listp x)
                     (cons-listp x)
                     (logic.appeal-listp proofs)
                     (equal (logic.strip-conclusions proofs)
                            (clause.clause-list-formulas (clause.lift-term-list-list x))))))

 (conclude forcing-logic.appeal-listp-of-clause.lift-clauses-bldr
           (equal (logic.appeal-listp (clause.lift-clauses-bldr x proofs))
                  t))

 (conclude forcing-logic.strip-conclusions-of-clause.lift-clauses-bldr
           (equal (logic.strip-conclusions (clause.lift-clauses-bldr x proofs))
                  (clause.clause-list-formulas x))
           :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-clause.lift-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.lift-term-list-list x)))
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.term-list-list-atblp x atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.lift-clauses-bldr)))
            (equal (logic.proof-listp (clause.lift-clauses-bldr x proofs) axioms thms atbl)
                   t))))