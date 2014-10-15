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
(include-book "tautologies")
(include-book "../build/lambda")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Let X' (a term) be obtained from X (another term) by replacing some
;; occurrences of terms A1,...,An by A1',...,An', respectively.  If
;;   |- A1 = A1', |- A2 = A2', ..., |- An = An'
;; Then
;;   |- X = X'
;;
;; Furthermore, if Y' (a formula) is obtained from Y (another formula)
;; by similar replacements, then
;;   |- Y <-> Y'



;; We introduce the function equals-for-equalsp, which takes as inputs the
;; terms x and y, and the list of formulas [A1, A2, ..., An].  We return true
;; if and only if y is obtainable from x by replacing some terms ti with other
;; terms si, where ti=si or si=ti is some Ai.
;;
;; This function is sort of like tautologyp1, in that it does not build a
;; proof, but is rather just an algorithm to decide if a proof can be
;; generated.

(mutual-recursion
 (defund equal-substitutible-logic.termp (x y as)
   (declare (xargs :guard (and (logic.termp x)
                               (logic.termp y)
                               (logic.formula-listp as))))
   (or (equal x y)
       (memberp (logic.pequal x y) as)
       (memberp (logic.pequal y x) as)
       (cond ((logic.constantp x)
              nil)
             ((logic.variablep x)
              nil)
             ((logic.functionp x)
              (and (logic.functionp y)
                   (equal (logic.function-name x) (logic.function-name y))
                   (equal-substitutible-logic.term-listp (logic.function-args x) (logic.function-args y) as)))
             ((logic.lambdap x)
              (and (logic.lambdap y)
                   (equal (logic.lambda-formals x) (logic.lambda-formals y))
                   (equal (logic.lambda-body x) (logic.lambda-body y))
                   (equal-substitutible-logic.term-listp (logic.lambda-actuals x)
                                                         (logic.lambda-actuals y)
                                                         as)))
             (t nil))))

 (defund equal-substitutible-logic.term-listp (x y as)
   (declare (xargs :guard (and (logic.term-listp x)
                               (logic.term-listp y)
                               (logic.formula-listp as))))
   (if (consp x)
       (and (consp y)
            (equal-substitutible-logic.termp (car x) (car y) as)
            (equal-substitutible-logic.term-listp (cdr x) (cdr y) as))
     (not (consp y)))))

(defthm equal-substitutible-logic.term-listp-of-cdrs-when-equal-substitutible-logic.term-listp
  (implies (and (equal-substitutible-logic.term-listp x y as)
                (consp x)
                (consp y))
           (equal-substitutible-logic.term-listp (cdr x) (cdr y) as))
  :hints(("Goal" :in-theory (enable equal-substitutible-logic.term-listp))))

(defthm equal-substitutible-logic.termp-of-cars-when-equal-substitutible-logic.term-listp
  (implies (and (equal-substitutible-logic.term-listp x y as)
                (consp x)
                (consp y))
           (equal-substitutible-logic.termp (car x) (car y) as))
  :hints(("Goal" :in-theory (enable equal-substitutible-logic.term-listp))))

(defthm equal-of-lengths-when-equal-substitutible-logic.term-listp
  (implies (equal-substitutible-logic.term-listp x y as)
           (equal (equal (len x) (len y))
                  t))
  :hints(("Goal"
          :induct (cdr-cdr-induction x y)
          :in-theory (enable equal-substitutible-logic.term-listp))))

(defthm equal-substitutible-logic.term-listp-of-logic.lambda-actuals-when-logic.lambdaps
  (implies (and (equal-substitutible-logic.termp x y as)
                (logic.lambdap x)
                (logic.lambdap y)
                (not (equal x y))
                (not (memberp (logic.pequal x y) as))
                (not (memberp (logic.pequal y x) as)))
           (equal-substitutible-logic.term-listp (logic.lambda-actuals x)
                                           (logic.lambda-actuals y)
                                           as))
  :hints(("Goal"
          :in-theory (enable equal-substitutible-logic.termp)
          :expand (equal-substitutible-logic.termp x y as))))

(defthm equal-substitutible-logic.term-listp-of-logic.function-args-when-logic.functionps
  (implies (and (equal-substitutible-logic.termp x y as)
                (logic.functionp x)
                (logic.functionp y)
                (not (equal x y))
                (not (memberp (logic.pequal x y) as))
                (not (memberp (logic.pequal y x) as)))
           (equal-substitutible-logic.term-listp (logic.function-args x) (logic.function-args y) as))
  :hints(("Goal"
          :in-theory (enable equal-substitutible-logic.termp)
          :expand (equal-substitutible-logic.termp x y as))))



;; Below we introduce equals-for-equals-bldr, which takes as inputs the terms x
;; and y, and the list of proofs [A1, A2, ..., An].  It should be the case that
;; these inputs satisfy equal-substitutible-logic.termp (i.e., using the conclusions
;; of the proofs A1...An).  Our goal is to build a proof that x = y, by
;; utilizing the provided proofs as necessary.
;;
;; This function is sort of like tautologyp-bldr1, which builds a proof
;; whenever tautologyp1 says that some inputs are ok.  In this case, we build a
;; proof when equal-substitutible-logic.termp says that the inputs are ok.

(mutual-recursion
 (defund equal-substitutible-term-bldr (x y as)
   (declare (xargs :guard (and (logic.termp x)
                               (logic.termp y)
                               (logic.appeal-listp as)
                               (equal-substitutible-logic.termp
                                x y (logic.strip-conclusions as)))
                   :verify-guards nil))
   (cond ((equal x y)
          (build.reflexivity x))
         ((memberp (logic.pequal x y) (logic.strip-conclusions as))
          (logic.find-proof (logic.pequal x y) as))
         ((memberp (logic.pequal y x) (logic.strip-conclusions as))
          (build.commute-pequal (logic.find-proof (logic.pequal y x) as)))
         ((logic.functionp x)
          (if (and (logic.functionp y)
                   (equal (logic.function-name x) (logic.function-name y)))
              (build.pequal-by-args
               (logic.function-name x)
               (equal-substitutible-term-list-bldr (logic.function-args x) (logic.function-args y) as))
            nil))
         ((logic.lambdap x)
          (if (and (logic.lambdap y)
                   (equal (logic.lambda-formals x) (logic.lambda-formals y))
                   (equal (logic.lambda-body x) (logic.lambda-body y)))
              (build.lambda-pequal-by-args
               (logic.lambda-formals x)
               (logic.lambda-body x)
               (equal-substitutible-term-list-bldr (logic.lambda-actuals x)
                                                   (logic.lambda-actuals y)
                                                   as))
              nil))
         (t nil)))
 (defund equal-substitutible-term-list-bldr (x y as)
   (declare (xargs :guard (and (logic.term-listp x)
                               (logic.term-listp y)
                               (logic.appeal-listp as)
                               (equal-substitutible-logic.term-listp
                                x y (logic.strip-conclusions as)))))
   (if (consp x)
       (if (consp y)
           (cons (equal-substitutible-term-bldr (car x) (car y) as)
                 (equal-substitutible-term-list-bldr (cdr x) (cdr y) as))
         nil)
     nil)))

(defthm len-of-equal-substitutible-term-list-bldr
  (implies (force (equal (len x) (len y)))
           (equal (len (equal-substitutible-term-list-bldr x y as))
                  (len x)))
  :hints(("Goal"
          :in-theory (enable equal-substitutible-term-list-bldr)
          :induct (cdr-cdr-induction x y))))

(defthm true-listp-of-equal-substitutible-term-list-bldr
  (equal (true-listp (equal-substitutible-term-list-bldr x y as))
         t)
  :hints(("Goal"
          :in-theory (enable equal-substitutible-term-list-bldr)
          :induct (cdr-cdr-induction x y))))


(encapsulate
  ()
  (local
   (defun my-induction (flag x y as)
     (declare (xargs :verify-guards nil))
     (if (equal flag 'term)
         (cond ((equal x y)
                nil)
               ((memberp (logic.pequal x y) (logic.strip-conclusions as))
                nil)
               ((memberp (logic.pequal y x) (logic.strip-conclusions as))
                nil)
               ((logic.constantp x)
                nil)
               ((logic.variablep x)
                nil)
               ((logic.functionp x)
                (my-induction 'list (logic.function-args x) (logic.function-args y) as))
               ((logic.lambdap x)
                (my-induction 'list
                              (logic.lambda-actuals x)
                              (logic.lambda-actuals y)
                              as))
               (t nil))
       (if (and (consp x)
                (consp y))
           (list (my-induction 'term (car x) (car y) as)
                 (my-induction 'list (cdr x) (cdr y) as))
         nil))))

  (local
   (defthm lemma
     (if (equal flag 'term)
         (implies (and (logic.termp x)
                       (logic.termp y)
                       (logic.appeal-listp as)
                       (equal-substitutible-logic.termp x y (logic.strip-conclusions as)))
                  (and (logic.appealp
                        (equal-substitutible-term-bldr x y as))
                       (equal (logic.conclusion
                               (equal-substitutible-term-bldr x y as))
                              (logic.pequal x y))))
       (implies (and (logic.term-listp x)
                     (logic.term-listp y)
                     (logic.appeal-listp as)
                     (equal-substitutible-logic.term-listp x y (logic.strip-conclusions as)))
                (and (logic.appeal-listp
                      (equal-substitutible-term-list-bldr x y as))
                     (equal (logic.strip-conclusions
                             (equal-substitutible-term-list-bldr x y as))
                            (logic.pequal-list x y)))))
     :rule-classes nil
     :hints(("Goal"
             :induct (my-induction flag x y as)
             :in-theory (e/d (equal-substitutible-term-bldr
                              equal-substitutible-term-list-bldr
                              equal-substitutible-logic.termp
                              equal-substitutible-logic.term-listp))))))

  (defthm forcing-logic.appealp-of-equal-substitutible-term-bldr
    (implies (and (force (logic.termp x))
                  (force (logic.termp y))
                  (force (logic.appeal-listp as))
                  (force (equal-substitutible-logic.termp x y (logic.strip-conclusions as))))
             (logic.appealp (equal-substitutible-term-bldr x y as)))
    :hints(("Goal" :use ((:instance lemma (flag 'term))))))

  (defthm forcing-logic.appeal-listp-of-equal-substitutible-term-list-bldr
    (implies (and (force (logic.term-listp x))
                  (force (logic.term-listp y))
                  (force (logic.appeal-listp as))
                  (force (equal-substitutible-logic.term-listp x y (logic.strip-conclusions as))))
             (logic.appeal-listp (equal-substitutible-term-list-bldr x y as)))
    :hints(("Goal" :use ((:instance lemma (flag 'list))))))

  (defthm forcing-logic.conclusion-of-equal-substitutible-term-bldr
    (implies (and (force (logic.termp x))
                  (force (logic.termp y))
                  (force (logic.appeal-listp as))
                  (force (equal-substitutible-logic.termp x y (logic.strip-conclusions as))))
             (equal (logic.conclusion (equal-substitutible-term-bldr x y as))
                    (logic.pequal x y)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))
    :hints(("Goal" :use ((:instance lemma (flag 'term))))))

  (defthm forcing-logic.strip-conclusions-of-equal-substitutible-term-list-bldr
    (implies (and (force (logic.term-listp x))
                  (force (logic.term-listp y))
                  (force (logic.appeal-listp as))
                  (force (equal-substitutible-logic.term-listp x y (logic.strip-conclusions as))))
             (equal (logic.strip-conclusions (equal-substitutible-term-list-bldr x y as))
                    (logic.pequal-list x y)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))
    :hints(("Goal" :use ((:instance lemma (flag 'list))))))

  (local (defthm crock
           (implies (and (equal (logic.lambda-formals x)
                                (logic.lambda-formals y))
                         (logic.termp x)
                         (logic.termp y)
                         (logic.lambdap x)
                         (logic.lambdap y))
                    (equal (equal (len (logic.lambda-actuals x))
                                  (len (logic.lambda-actuals y)))
                           t))
           :hints(("Goal"
                   :in-theory (disable FORCING-EQUAL-LENS-OF-LOGIC.LAMBDA-FORMALS-AND-LOGIC.LAMBDA-ACTUALS)
                   :use ((:instance FORCING-EQUAL-LENS-OF-LOGIC.LAMBDA-FORMALS-AND-LOGIC.LAMBDA-ACTUALS)
                         (:instance FORCING-EQUAL-LENS-OF-LOGIC.LAMBDA-FORMALS-AND-LOGIC.LAMBDA-ACTUALS (x y)))))))

  (verify-guards equal-substitutible-term-bldr)


  (local (defthm lemma3
           (if (equal flag 'term)
               (implies (and (logic.termp x)
                             (logic.termp y)
                             (logic.appeal-listp as)
                             (equal-substitutible-logic.termp x y (logic.strip-conclusions as))
                             ;; ---
                             (logic.term-atblp x atbl)
                             (logic.term-atblp y atbl)
                             (logic.proof-listp as axioms thms atbl)
                             (memberp (axiom-reflexivity) axioms)
                             (memberp (axiom-equality) axioms)
                             (memberp (theorem-transitivity-of-pequal) thms)
                             (memberp (theorem-commutativity-of-pequal) thms))
                        (logic.proofp (equal-substitutible-term-bldr x y as) axioms thms atbl))
             (implies (and (logic.term-listp x)
                           (logic.term-listp y)
                           (logic.appeal-listp as)
                           (equal-substitutible-logic.term-listp x y (logic.strip-conclusions as))
                           ;; ---
                           (logic.term-list-atblp x atbl)
                           (logic.term-list-atblp y atbl)
                           (logic.proof-listp as axioms thms atbl)
                           (memberp (axiom-reflexivity) axioms)
                           (memberp (axiom-equality) axioms)
                           (memberp (theorem-transitivity-of-pequal) thms)
                           (memberp (theorem-commutativity-of-pequal) thms))
                      (logic.proof-listp (equal-substitutible-term-list-bldr x y as) axioms thms atbl)))
           :rule-classes nil
           :hints(("Goal"
                   :induct (my-induction flag x y as)
                   :in-theory (enable equal-substitutible-term-bldr
                                      equal-substitutible-term-list-bldr
                                      equal-substitutible-logic.termp
                                      equal-substitutible-logic.term-listp)))))

  (defthm forcing-logic.proofp-of-equal-substitutible-term-bldr
    (implies (force (and (logic.termp x)
                         (logic.termp y)
                         (logic.appeal-listp as)
                         (equal-substitutible-logic.termp x y (logic.strip-conclusions as))
                         ;; ---
                         (logic.term-atblp x atbl)
                         (logic.term-atblp y atbl)
                         (logic.proof-listp as axioms thms atbl)
                         (memberp (axiom-reflexivity) axioms)
                         (memberp (axiom-equality) axioms)
                         (memberp (theorem-transitivity-of-pequal) thms)
                         (memberp (theorem-commutativity-of-pequal) thms)))
             (logic.proofp (equal-substitutible-term-bldr x y as)
                           axioms thms atbl))
    :hints(("Goal" :use ((:instance lemma3 (flag 'term))))))

  (defthm forcing-logic.proof-listp-of-equal-substitutible-term-list-bldr
    (implies (force (and (logic.term-listp x)
                         (logic.term-listp y)
                         (logic.appeal-listp as)
                         (equal-substitutible-logic.term-listp x y (logic.strip-conclusions as))
                         ;; ---
                         (logic.term-list-atblp x atbl)
                         (logic.term-list-atblp y atbl)
                         (logic.proof-listp as axioms thms atbl)
                         (memberp (axiom-reflexivity) axioms)
                         (memberp (axiom-equality) axioms)
                         (memberp (theorem-transitivity-of-pequal) thms)
                         (memberp (theorem-commutativity-of-pequal) thms)))
             (logic.proof-listp (equal-substitutible-term-list-bldr x y as)
                                axioms thms atbl))
    :hints(("Goal" :use ((:instance lemma3 (flag 'list)))))))




;; The second part of equals for equals is that, if a formula Y' is obtained
;; from some formula Y through replacements of equals for equals, then we
;; should be able to prove Y <-> Y'.

(defund equal-substitutiblep (x y as)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formulap y)
                              (logic.formula-listp as))))
  (cond ((equal (logic.fmtype x) 'por*)
         (and (equal (logic.fmtype y) 'por*)
              (equal-substitutiblep (logic.vlhs x) (logic.vlhs y) as)
              (equal-substitutiblep (logic.vrhs x) (logic.vrhs y) as)))
        ((equal (logic.fmtype x) 'pnot*)
         (and (equal (logic.fmtype y) 'pnot*)
              (equal-substitutiblep (logic.~arg x) (logic.~arg y) as)))
        ((equal (logic.fmtype x) 'pequal*)
         (and (equal (logic.fmtype x) 'pequal*)
              (equal (logic.fmtype y) 'pequal*)
              (equal-substitutible-logic.termp (logic.=lhs x) (logic.=lhs y) as)
              (equal-substitutible-logic.termp (logic.=rhs x) (logic.=rhs y) as)))
        (t nil)))

(defthm logic.fmtype-when-equal-substitutiblep-with-logic.por
  (implies (and (equal-substitutiblep x y as)
                (equal (logic.fmtype x) 'por*))
           (equal (logic.fmtype y) 'por*))
   :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm logic.fmtype-when-equal-substitutiblep-with-logic.pnot
  (implies (and (equal-substitutiblep x y as)
                (equal (logic.fmtype x) 'pnot*))
           (equal (logic.fmtype y) 'pnot*))
   :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm logic.fmtype-when-equal-substitutiblep-with-pequal
  (implies (and (equal-substitutiblep x y as)
                (equal (logic.fmtype x) 'pequal*))
           (equal (logic.fmtype y) 'pequal*))
   :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm equal-substitutiblep-of-recursive-calls-in-logic.por-case
  (implies (and (equal-substitutiblep x y as)
                (force (equal (logic.fmtype x) 'por*)))
           (and (equal-substitutiblep (logic.vlhs x) (logic.vlhs y) as)
                (equal-substitutiblep (logic.vrhs x) (logic.vrhs y) as)))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm equal-substitutiblep-of-recursive-calls-in-logic.pnot-case
  (implies (and (equal-substitutiblep x y as)
                (force (equal (logic.fmtype x) 'pnot*)))
           (equal-substitutiblep (logic.~arg x) (logic.~arg y) as))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm equal-substitutible-logic.termp-of-recursive-calls-in-pequal-case
  (implies (and (equal-substitutiblep x y as)
                (force (equal (logic.fmtype x) 'pequal*)))
           (and (equal-substitutible-logic.termp (logic.=lhs x) (logic.=lhs y) as)
                (equal-substitutible-logic.termp (logic.=rhs x) (logic.=rhs y) as)))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))




;; Note: This is like Shankar's function FORM-EQUAL-PROOF
;;
;; BOZO consider not using tautologies and building the proofs separately?

(defund equal-substitutible-bldr (x y as)
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.formulap y)
                              (logic.appeal-listp as)
                              (equal-substitutiblep
                               x y (logic.strip-conclusions as)))
                  :verify-guards nil))
  (cond ((equal (logic.fmtype x) 'por*)
         (tautological-consequence-bldr
          (logic.piff x y)
          (list (equal-substitutible-bldr (logic.vlhs x) (logic.vlhs y) as)
                (equal-substitutible-bldr (logic.vrhs x) (logic.vrhs y) as))))
        ((equal (logic.fmtype x) 'pnot*)
         (tautological-consequence-bldr
          (logic.piff x y)
          (list (equal-substitutible-bldr (logic.~arg x) (logic.~arg y) as))))
        ((equal (logic.fmtype x) 'pequal*)
         (let ((T1       (logic.=lhs x))
               (T1-Prime (logic.=lhs y))
               (T2       (logic.=rhs x))
               (T2-Prime (logic.=rhs y)))
           (let* ((T1=T1-Prime (equal-substitutible-term-bldr T1 T1-Prime as))
                  (T2=T2-Prime (equal-substitutible-term-bldr T2 T2-Prime as))
                  (T1-Prime=T1 (build.commute-pequal T1=T1-Prime))
                  (T2-Prime=T2 (build.commute-pequal T2=T2-Prime)))
             (tautological-consequence-bldr
              (logic.piff x y)
              (list T1=T1-Prime
                    T2=T2-Prime
                    T1-Prime=T1
                    T2-Prime=T2
                    (build.equality T1 T1-Prime T2 T2-Prime)
                    (build.equality T1-Prime T1 T2-Prime T2))))))
        (t nil)))



;; Explanation of the Base Case
;;
;; In the base case above, we assume that we have two formulas, T1=T1' and
;; T2=T2', which are provable by the use of equals-for-equals.  We now need
;; to show that T1=T2 <-> T1'=T2'.
;;
;; Shoenfield explains the proof as follows.
;;
;; 1. Use equals-for-equals to prove T1=T1', T2=T2'.
;; 2. Use commute-equal to prove T1'=T1, T2'=T2.
;; 3. Use the equality axiom to prove T1=T1' -> T2=T2' -> T1=T2' -> T1'=T2'
;; 4. Use the equality axiom to prove T1'=T1 -> T2'=T2 -> T1'=T2' -> T1=T2
;;
;; Now, our goal T1=T2 <-> T1'=T2' is a tautological consequence of the
;; formulas produced in steps 1-4.
;;
;; We can "test this out" on some example formulas as below.  You can run
;; this example to see that we do indeed have a tautological consequence.
;;
;; (tautological-consequencep
;;  (logic.piff (logic.pequal 'T1 'T2)
;;        (logic.pequal 'T1-Prime 'T2-Prime))
;;  (logic.strip-conclusions
;;   (list
;;    (build.axiom (logic.pequal 'T1 'T1-Prime))
;;    (build.axiom (logic.pequal 'T2 'T2-Prime))
;;    (build.axiom (logic.pequal 'T1-Prime 'T1))
;;    (build.axiom (logic.pequal 'T2-Prime 'T2))
;;    (build.equality 'T1 'T1-Prime 'T2 'T2-Prime)
;;    (build.equality 'T1-Prime 'T1 'T2-Prime 'T2))))
;;
;; But what we need to do is show this for arbitrary T1,T2,T1',T2' instead
;; of just for the above examples.

(encapsulate
 ()

;; BOZO i still don't like how we use logic.=lhs and logic.=rhs explicitly here.  i'd
;; rather it used explicit variables instead.

 (local (defthm lemma
          (implies (and (force (logic.formulap x))
                        (force (logic.formulap y))
                        (force (equal (logic.fmtype x) 'pequal*))
                        (force (equal (logic.fmtype y) 'pequal*)))
                   (tautological-consequencep
                    (logic.piff x y)
                    (list (logic.pequal (logic.=lhs x) (logic.=lhs y))
                          (logic.pequal (logic.=rhs x) (logic.=rhs y))
                          (logic.pequal (logic.=lhs y) (logic.=lhs x))
                          (logic.pequal (logic.=rhs y) (logic.=rhs x))
                          (logic.por (logic.pnot (logic.pequal (logic.=lhs x) (logic.=lhs y)))
                               (logic.por (logic.pnot (logic.pequal (logic.=rhs x) (logic.=rhs y)))
                                    (logic.por (logic.pnot x) y)))
                          (logic.por (logic.pnot (logic.pequal (logic.=lhs y) (logic.=lhs x)))
                               (logic.por (logic.pnot (logic.pequal (logic.=rhs y) (logic.=rhs x)))
                                    (logic.por (logic.pnot y) x))))))
          :hints(("Goal" :in-theory (e/d (tautological-consequencep)
                                         ;; This is a yucky looking hint, but
                                         ;; it's just for speed.
                                         (in-superset-when-in-subset-two
                                          in-superset-when-in-subset-one
                                          not-in-subset-when-not-in-superset-one
                                          not-in-subset-when-not-in-superset-two
                                          memberp-when-memberp-of-cdr
                                          memberp-when-not-consp
                                          subsetp-when-not-consp-two
                                          subsetp-of-cdr
                                          subsetp-when-not-consp))))))


 (local (defthm lemma2
          (implies (and (logic.formulap x)
                        (logic.formulap y)
                        (logic.appeal-listp as)
                        (equal-substitutiblep x y (logic.strip-conclusions as)))
                   (and (logic.appealp (equal-substitutible-bldr x y as))
                        (equal (logic.conclusion (equal-substitutible-bldr x y as))
                               (logic.piff x y))))
          :hints(("Goal" :in-theory (enable equal-substitutible-bldr)))))

 (defthm forcing-logic.appealp-of-equal-substitutible-bldr
   (implies (and (force (logic.formulap x))
                 (force (logic.formulap y))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep x y (logic.strip-conclusions as))))
            (logic.appealp (equal-substitutible-bldr x y as))))

 (defthm forcing-logic.conclusion-of-equal-substitutible-bldr
   (implies (and (force (logic.formulap x))
                 (force (logic.formulap y))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep x y (logic.strip-conclusions as))))
            (equal (logic.conclusion (equal-substitutible-bldr x y as))
                   (logic.piff x y)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (verify-guards equal-substitutible-bldr)

 (defthm forcing-logic.proofp-of-equal-substitutible-bldr
   (implies (and (force (logic.formulap x))
                 (force (logic.formulap y))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep x y (logic.strip-conclusions as)))
                 ;; ---
                 (force (logic.formula-atblp x atbl))
                 (force (logic.formula-atblp y atbl))
                 (force (logic.proof-listp as axioms thms atbl))
                 (force (memberp (axiom-reflexivity) axioms))
                 (force (memberp (axiom-equality) axioms))
                 (force (memberp (theorem-transitivity-of-pequal) thms))
                 (force (memberp (theorem-commutativity-of-pequal) thms)))
            (logic.proofp (equal-substitutible-bldr x y as) axioms thms atbl))
   :hints(("Goal" :in-theory (enable equal-substitutible-bldr)))))



;; As with the tautology and equivalence theorems, the equality theorem is
;; perhaps most often useful in the form below.  Suppose that G is a formula
;; which is obtained from F by equality substitution of A1=A1' ... An=An'.
;; Then, if we have proofs of A1=A1' ... An=An' and F, we should be able to
;; prove G.  This is the equal-consequence-bldr.

(defund equal-consequence-bldr (g f as)
  (declare (xargs :guard (and (logic.formulap g)
                              (logic.appealp f)
                              (logic.appeal-listp as)
                              (equal-substitutiblep
                               (logic.conclusion f) g (logic.strip-conclusions as)))
                  :verify-guards nil))
  (let ((iff-f-g (equal-substitutible-bldr (logic.conclusion f) g as)))
    (tautological-consequence-bldr g (list iff-f-g f))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (logic.formulap f)
                        (logic.formulap g))
                   (tautological-consequencep g (list (logic.piff f g) f)))
          :hints(("Goal" :in-theory (enable tautological-consequencep)))))

 (verify-guards equal-consequence-bldr)

 (defthm forcing-logic.conclusion-of-equal-consequence-bldr
   (implies (and (force (logic.formulap g))
                 (force (logic.appealp f))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as))))
            (equal (logic.conclusion (equal-consequence-bldr g f as))
                   g))
   :hints(("Goal" :in-theory (enable equal-consequence-bldr))))

 (defthm forcing-logic.appealp-of-equal-consequence-bldr
   (implies (and (force (logic.formulap g))
                 (force (logic.appealp f))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as))))
            (logic.appealp (equal-consequence-bldr g f as)))
   :hints(("Goal" :in-theory (enable equal-consequence-bldr))))

 (defthm forcing-logic.proofp-of-equal-consequence-bldr
   (implies (and (force (logic.formulap g))
                 (force (logic.appealp f))
                 (force (logic.appeal-listp as))
                 (force (equal-substitutiblep (logic.conclusion f) g (logic.strip-conclusions as)))
                 ;; ---
                 (force (logic.formula-atblp g atbl))
                 (force (logic.proofp f axioms thms atbl))
                 (force (logic.proof-listp as axioms thms atbl))
                 (force (memberp (axiom-reflexivity) axioms))
                 (force (memberp (axiom-equality) axioms))
                 (force (memberp (theorem-transitivity-of-pequal) thms))
                 (force (memberp (theorem-commutativity-of-pequal) thms)))
            (logic.proofp (equal-consequence-bldr g f as) axioms thms atbl))
   :hints(("Goal" :in-theory (enable equal-consequence-bldr)))))





(defthm forcing-equal-substitutiblep-of-logic.pors
  (implies (and (force (logic.formulap a))
                (force (logic.formulap b))
                (force (logic.formulap c))
                (force (logic.formulap d)))
           (equal (equal-substitutiblep (logic.por a b) (logic.por c d) proofs)
                  (and (equal-substitutiblep a c proofs)
                       (equal-substitutiblep b d proofs))))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm forcing-equal-substitutiblep-of-logic.pnots
  (implies (and (force (logic.formulap a))
                (force (logic.formulap b)))
           (equal (equal-substitutiblep (logic.pnot a) (logic.pnot b) proofs)
                  (equal-substitutiblep a b proofs)))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm forcing-equal-substitutiblep-of-pequals
  (implies (and (force (logic.termp a))
                (force (logic.termp b))
                (force (logic.termp c))
                (force (logic.termp d)))
           (equal (equal-substitutiblep (logic.pequal a b) (logic.pequal c d) proofs)
                  (and (equal-substitutible-logic.termp a c proofs)
                       (equal-substitutible-logic.termp b d proofs))))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm reflexivity-of-equal-substitutible-logic.termp
  (equal-substitutible-logic.termp x x proofs)
  :hints(("Goal" :in-theory (enable equal-substitutible-logic.termp))))

(defthm reflexivity-of-equal-substitutiblep
  (implies (force (logic.formulap x))
           (equal-substitutiblep x x proofs))
  :hints(("Goal" :in-theory (enable equal-substitutiblep))))

(defthm equal-substitutible-logic.termp-of-lhs-and-rhs-when-in-proofs
  (implies (and (memberp proof proofs)
                (force (logic.formulap proof))
                ;; jcd:2006-04-05 added this hyp
                (force (equal (logic.fmtype proof) 'pequal*)))
           (equal-substitutible-logic.termp (logic.=lhs proof) (logic.=rhs proof) proofs))
  :hints(("Goal" :in-theory (enable equal-substitutible-logic.termp))))

(defthm forcing-equal-substitutible-logic.termp-of-logic.functions
  (implies (and (force (logic.function-namep fn))
                (force (true-listp args1))
                (force (logic.term-listp args1))
                (force (true-listp args2))
                (force (logic.term-listp args2)))
           (equal (equal-substitutible-logic.termp (logic.function fn args1)
                                             (logic.function fn args2)
                                             proofs)
                  (or (equal args1 args2)
                      (memberp (logic.pequal (logic.function fn args1)
                                       (logic.function fn args2))
                               proofs)
                      (memberp (logic.pequal (logic.function fn args2)
                                       (logic.function fn args1))
                               proofs)
                      (equal-substitutible-logic.term-listp args1 args2 proofs))))
  :hints(("Goal" :in-theory (enable equal-substitutible-logic.termp))))

