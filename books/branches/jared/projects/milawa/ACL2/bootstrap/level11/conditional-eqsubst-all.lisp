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
(include-book "conditional-eqsubst")
(%interactive)


(%autoadmit tactic.conditional-eqsubst-all-okp)
(%autoadmit tactic.conditional-eqsubst-all-env-okp)

(%autoprove booleanp-of-tactic.conditional-eqsubst-all-okp
            (%enable default tactic.conditional-eqsubst-all-okp))

(%autoprove booleanp-of-tactic.conditional-eqsubst-all-env-okp
            (%enable default tactic.conditional-eqsubst-all-env-okp))

(defthm forcing-logic.term-list-list-atblp-of-multicons
  ;; BOZO unlocalize
  (implies (force (and (logic.term-atblp a atbl)
                       (logic.term-list-list-atblp x atbl)))
           (equal (logic.term-list-list-atblp (multicons a x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(%autoprove forcing-logic.term-list-list-atblp-of-multicons
            (%cdr-induction x))


(%autoadmit tactic.conditional-eqsubst-all-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.conditional-eqsubst-all-tac
            (%enable default tactic.conditional-eqsubst-all-tac))

(%autoprove forcing-tactic.conditional-eqsubst-all-okp-of-tactic.conditional-eqsubst-all-tac
            (%enable default
                     tactic.conditional-eqsubst-all-tac
                     tactic.conditional-eqsubst-all-okp))

(%autoprove forcing-tactic.conditional-eqsubst-all-env-okp-of-tactic.conditional-eqsubst-all-tac
            (%enable default
                     tactic.conditional-eqsubst-all-tac
                     tactic.conditional-eqsubst-all-env-okp))


(%autoadmit tactic.conditional-eqsubst-list-bldr)

(encapsulate
 ()
 (defthmd lemma-1-for-tactic.conditional-eqsubst-list-bldr
   (implies (not (consp orig-goals))
            (equal (TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR P ORIG-GOALS PROOF1 PROOFS2 PROOFS3 LHS RHS)
                   nil))
   :hints(("Goal" :in-theory (enable TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR))))

 (defthmd lemma-2-for-tactic.conditional-eqsubst-list-bldr
   (equal (TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR P (cons a ORIG-GOALS) PROOF1 PROOFS2 PROOFS3 LHS RHS)
          (CONS (TACTIC.CONDITIONAL-EQSUBST-BLDR P a
                                                 PROOF1 (CAR PROOFS2)
                                                 (CAR PROOFS3)
                                                 LHS RHS)
                (TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR P ORIG-GOALS
                                                      PROOF1 (CDR PROOFS2)
                                                      (CDR PROOFS3)
                                                      LHS RHS)))
   :hints(("Goal" :in-theory (enable tactic.conditional-eqsubst-list-bldr))))

 (%autoprove lemma-1-for-tactic.conditional-eqsubst-list-bldr
             (%restrict default TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR (equal orig-goals 'orig-goals)))

 (%autoprove lemma-2-for-tactic.conditional-eqsubst-list-bldr
             (%restrict default TACTIC.CONDITIONAL-EQSUBST-LIST-BLDR (equal orig-goals '(cons a orig-goals))))

 (local (%enable default
                 lemma-1-for-tactic.conditional-eqsubst-list-bldr
                 lemma-2-for-tactic.conditional-eqsubst-list-bldr))

 (%autoprove forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-list-bldr
             (%autoinduct tactic.conditional-eqsubst-list-bldr))

 (%autoprove forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-list-bldr
             (%autoinduct tactic.conditional-eqsubst-list-bldr))

 (%autoprove forcing-logic.proof-listp-of-tactic.conditional-eqsubst-list-bldr
             (%autoinduct tactic.conditional-eqsubst-list-bldr)))





(encapsulate
 ()
 (set-well-founded-relation ord<)
 (set-measure-function rank)
 (defun firstn-firstn-induct (n x y)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       nil
     (if (not (consp x))
         nil
       (if (not (consp y))
           nil
         (firstn-firstn-induct (- n 1) (cdr x) (cdr y)))))))

(defthm lemma-0-for-tactic.conditional-eqsubst-all-compile
  ;; NOTE: switched order of 1/len x, inc blimit to 1
  (implies (not (cdr x))
           (equal (equal 1 (len x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm lemma-1-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (logic.conclusion (first proofs))
                  (logic.disjoin-formulas (logic.term-list-formulas (car goals))))))

(defthm lemma-2-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (logic.strip-conclusions (firstn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas (firstn n goals)))))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm lemma-3-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (logic.strip-conclusions (restn n proofs))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas (restn n goals)))))
  :hints(("Goal" :in-theory (enable restn))))

(defthm lemma-4-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (logic.strip-conclusions (firstn n (cdr proofs)))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas (firstn n (cdr goals)))))))

(defthm lemma-5-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (logic.strip-conclusions (restn n (cdr proofs)))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas (restn n (cdr goals)))))))

(defthm lemma-6-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (app a b) x)
           (equal (firstn (len a) x)
                  (list-fix a))))

(defthm lemma-7-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (app a b) x)
           (equal (restn (len a) x)
                  (list-fix b))))

(defthm lemma-8-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (app a (app b c)) x)
           (equal (firstn (len b) (restn (len a) x))
                  (list-fix b))))

(defthm lemma-9-for-tactic.conditional-eqsubst-all-compile
  (implies (equal (logic.disjoin-each-formula-list (logic.term-list-list-formulas goals))
                  (logic.strip-conclusions proofs))
           (equal (consp proofs)
                  (consp goals))))

(defthm lemma-10-for-tactic.conditional-eqsubst-all-compile
  (implies (EQUAL (APP (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))) Y)
                  (CDR (TACTIC.SKELETON->GOALS X)))
           (EQUAL (FIRSTN (LEN (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))
                          (CDR (TACTIC.SKELETON->GOALS X)))
                  (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X))
                             (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))))
  :hints(("Goal" :use ((:instance lemma-6-for-tactic.conditional-eqsubst-all-compile
                                  (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                                  (b y)
                                  (x (CDR (TACTIC.SKELETON->GOALS X))))))))

(defthm lemma-11-for-tactic.conditional-eqsubst-all-compile
  (implies (EQUAL (APP (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))) Y)
                  (CDR (TACTIC.SKELETON->GOALS X)))
           (EQUAL (RESTN (LEN (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X)))
                         (CDR (TACTIC.SKELETON->GOALS X)))
                  (list-fix Y)))
  :hints(("Goal" :use ((:instance lemma-7-for-tactic.conditional-eqsubst-all-compile
                                  (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                                  (b y)
                                  (x (CDR (TACTIC.SKELETON->GOALS X))))))))

(defthm lemma-12-for-tactic.conditional-eqsubst-all-compile
  (implies (cons-listp x)
           (LOGIC.ALL-DISJUNCTIONSP (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x)))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm lemma-13-for-tactic.conditional-eqsubst-all-compile
  (implies (cons-listp x)
           (equal (LOGIC.VLHSES (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x))))
                  (repeat (logic.term-formula a) (len x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm lemma-14-for-tactic.conditional-eqsubst-all-compile
  (implies (cons-listp x)
           (equal (LOGIC.VRHSES (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (MULTICONS a x))))
                  (logic.disjoin-each-formula-list (logic.term-list-list-formulas x))))
  :hints(("Goal" :induct (cdr-induction x))))







(%autoprove lemma-0-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-1-for-tactic.conditional-eqsubst-all-compile)


(%autoprove lemma-2-for-tactic.conditional-eqsubst-all-compile
            (%autoinduct firstn-firstn-induct n proofs goals)
            (%forcingp nil)
            (%restrict default firstn (equal n 'n)))

(%autoprove lemma-3-for-tactic.conditional-eqsubst-all-compile
            (%autoinduct firstn-firstn-induct n proofs goals)
            (%forcingp nil)
            (%restrict default restn (equal n 'n)))

(%autoprove lemma-4-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-5-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-6-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-7-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-8-for-tactic.conditional-eqsubst-all-compile)
(%autoprove lemma-9-for-tactic.conditional-eqsubst-all-compile)

(%autoprove lemma-10-for-tactic.conditional-eqsubst-all-compile
            (%use (%instance (%thm lemma-6-for-tactic.conditional-eqsubst-all-compile)
                             (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                             (b y)
                             (x (CDR (TACTIC.SKELETON->GOALS X))))))

(%autoprove lemma-11-for-tactic.conditional-eqsubst-all-compile
            (%use (%instance (%thm lemma-7-for-tactic.conditional-eqsubst-all-compile)
                             (a (MULTICONS (FIRST (TACTIC.SKELETON->EXTRAS X)) (TACTIC.SKELETON->GOALS (TACTIC.SKELETON->HISTORY X))))
                             (b y)
                             (x (CDR (TACTIC.SKELETON->GOALS X))))))

(%autoprove lemma-12-for-tactic.conditional-eqsubst-all-compile
            (%cdr-induction x))

(%autoprove lemma-13-for-tactic.conditional-eqsubst-all-compile
            (%cdr-induction x))

(%autoprove lemma-14-for-tactic.conditional-eqsubst-all-compile
            (%cdr-induction x)
            (%forcingp nil))


(%autoadmit tactic.conditional-eqsubst-all-compile)

(local (%enable default
                tactic.conditional-eqsubst-all-okp
                tactic.conditional-eqsubst-all-env-okp
                tactic.conditional-eqsubst-all-compile
                logic.term-formula))

(local (%disable default
                 expensive-arithmetic-rules
                 expensive-arithmetic-rules-two
                 unusual-memberp-rules
                 unusual-subsetp-rules
                 type-set-like-rules))

(%autoprove forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-all-compile

            (%forcingp nil)
            (%auto :strategy (cleanup split urewrite))

            (%car-cdr-elim proofs)
            (%crewrite default first)
            (%generalize (car proofs) proof1)
            (%generalize (cdr proofs) proofs2)
            (%auto :strategy (cleanup split urewrite crewrite dist))

            (%disable default
                      expensive-term/formula-inference
                      formula-decomposition)

            (%forcingp t)
            (%waterfall default 40))

(%autoprove forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-all-compile

            (%forcingp nil)
            (%auto :strategy (cleanup split urewrite))

            (%car-cdr-elim proofs)
            (%crewrite default first)
            (%generalize (car proofs) proof1)
            (%generalize (cdr proofs) proofs2)
            (%auto :strategy (cleanup split urewrite crewrite dist))

            (%disable default
                      expensive-term/formula-inference
                      formula-decomposition)

            (%forcingp t)
            (%waterfall default 40))


(%autoprove forcing-logic.proof-listp-of-tactic.conditional-eqsubst-all-compile

            (%forcingp nil)
            (%auto :strategy (cleanup split urewrite))

            (%car-cdr-elim proofs)
            (%crewrite default first)
            (%generalize (car proofs) proof1)
            (%generalize (cdr proofs) proofs2)
            (%auto :strategy (cleanup split urewrite crewrite dist))

            (%disable default
                      expensive-term/formula-inference
                      formula-decomposition)

            (%forcingp t)
            (%waterfall default 40))


(in-theory (disable lemma-0-for-tactic.conditional-eqsubst-all-compile
                    lemma-1-for-tactic.conditional-eqsubst-all-compile
                    lemma-2-for-tactic.conditional-eqsubst-all-compile
                    lemma-3-for-tactic.conditional-eqsubst-all-compile
                    lemma-4-for-tactic.conditional-eqsubst-all-compile
                    lemma-5-for-tactic.conditional-eqsubst-all-compile
                    lemma-6-for-tactic.conditional-eqsubst-all-compile
                    lemma-7-for-tactic.conditional-eqsubst-all-compile
                    lemma-8-for-tactic.conditional-eqsubst-all-compile
                    lemma-9-for-tactic.conditional-eqsubst-all-compile
                    lemma-10-for-tactic.conditional-eqsubst-all-compile
                    lemma-11-for-tactic.conditional-eqsubst-all-compile
                    lemma-12-for-tactic.conditional-eqsubst-all-compile
                    lemma-13-for-tactic.conditional-eqsubst-all-compile
                    lemma-14-for-tactic.conditional-eqsubst-all-compile))

(%disable default
          lemma-0-for-tactic.conditional-eqsubst-all-compile
          lemma-1-for-tactic.conditional-eqsubst-all-compile
          lemma-2-for-tactic.conditional-eqsubst-all-compile
          lemma-3-for-tactic.conditional-eqsubst-all-compile
          lemma-4-for-tactic.conditional-eqsubst-all-compile
          lemma-5-for-tactic.conditional-eqsubst-all-compile
          lemma-6-for-tactic.conditional-eqsubst-all-compile
          lemma-7-for-tactic.conditional-eqsubst-all-compile
          lemma-8-for-tactic.conditional-eqsubst-all-compile
          lemma-9-for-tactic.conditional-eqsubst-all-compile
          lemma-10-for-tactic.conditional-eqsubst-all-compile
          lemma-11-for-tactic.conditional-eqsubst-all-compile
          lemma-12-for-tactic.conditional-eqsubst-all-compile
          lemma-13-for-tactic.conditional-eqsubst-all-compile
          lemma-14-for-tactic.conditional-eqsubst-all-compile)

(%ensure-exactly-these-rules-are-missing "../../tactics/conditional-eqsubst-all")