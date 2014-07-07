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
(include-book "equal")
(include-book "if")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "formula-compiler.tex")

;; Formula Compiler.
;;
;; We introduce a compiler which translates formulas into terms.  This is very
;; useful because it means we can focus on term manipulation rather than trying
;; to deal with formulas and terms.  The compliation is done by recursively
;; applying the following transformations everywhere throughout the formula:
;;
;;   compile(x = y) == (equal x y)
;;   compile(~F)    == (if compile(F) nil t)
;;   compile(F v G) == (if compile(F) t compile(G))
;;
;; Now, if we want to prove some formula, A-formula, it suffices to compile it
;; into A-term, and then prove A-term != nil.  Then, we can just use the
;; following derivation:
;;
;;  1. A-formula v A-term = nil        Compile-Formula Builder, Property #3
;;  2. A-term = nil v A-formula        Commute Or
;;  3. A-term != nil                   Given
;;  4. A-formula                       Modus Ponens 2; 3,2
;;
;; Q.E.D.

(defund logic.compile-formula (x)
  (declare (xargs :guard (logic.formulap x)
                  :verify-guards nil))
  (cond ((equal (logic.fmtype x) 'por*)
         (logic.function 'if
                (list (logic.compile-formula (logic.vlhs x))
                      ''t
                      (logic.compile-formula (logic.vrhs x)))))
        ((equal (logic.fmtype x) 'pnot*)
         (logic.function 'if
                (list (logic.compile-formula (logic.~arg x))
                      ''nil
                      ''t)))
        ((equal (logic.fmtype x) 'pequal*)
         (logic.function 'equal (list (logic.=lhs x) (logic.=rhs x))))
        (t nil)))

(defthm forcing-logic.termp-of-logic.compile-formula
  (implies (force (logic.formulap x))
           (equal (logic.termp (logic.compile-formula x))
                  t))
  :hints(("Goal" :in-theory (enable logic.compile-formula))))

(defthm forcing-logic.term-atblp-of-logic.compile-formula
  (implies (force (and (logic.formulap x)
                       (logic.formula-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.term-atblp (logic.compile-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.compile-formula))))

(verify-guards logic.compile-formula)




(defderiv build.compile-formula-lemma-1
  :derive (v (v B C) (= (if (? p) t (? q)) nil))
  :from ((proof x (v B (= (? p) nil)))
         (proof y (v C (= (? q) nil))))
  :proof (@derive
          ((v B (= (? p) nil))                          (@given x))
          ((v B (= (if (? p) t (? q)) (? q)))           (build.disjoined-if-when-nil @- (@term t) (@term (? q))))
          ((v (v B C) (= (if (? p) t (? q)) (? q)))     (build.multi-assoc-expansion @- (@formulas B C)) *1)
          ((v C (= (? q) nil))                          (@given y))
          ((v (v B C) (= (? q) nil))                    (build.multi-assoc-expansion @- (@formulas B C)))
          ((v (v B C) (= (if (? p) t (? q)) nil))       (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)))

(defderiv build.compile-formula-lemma-2
  :derive (v (! (v B C)) (= (if (? p) t (? q)) t))
  :from ((proof x (v (! B) (= (? p) t)))
         (proof y (v (! C) (= (? q) t))))
  :proof (@derive
          ((v (! B) (= (? p) t))                     (@given x))
          ((v (! B) (!= (? p) nil))                  (build.disjoined-not-nil-from-t @-))
          ((v (! B) (= (if (? p) t (? q)) t))        (build.disjoined-if-when-not-nil @- (@term t) (@term (? q))) *1)
          ((v (! C) (= (? q) t))                     (@given y))
          ((v (! C) (= t (? q)))                     (build.disjoined-commute-pequal @-))
          ((v (! C) (= (if (? p) t (? q)) t))        (build.disjoined-if-when-same @- (@term (? p))))
          ((v (! (v B C)) (= (if (? p) t (? q)) t))  (build.merge-implications *1 @-)))
  :minatbl ((if . 3)))

(defund@ build.compile-formula (a)
  (declare (xargs :guard (logic.formulap a)
                  :verify-guards nil))
  ;; We simultaneously derive the following four formulas.
  ;;
  ;;   1. ~A v (logic.compile-formula A) = t
  ;;   2. A v (logic.compile-formula A) = nil
  ;;
  ;; The resulting proofs are returned in a list.
  (cond ((equal (logic.fmtype a) 'por*)
         ;; Let A = B v C.
         ;; Let D = (logic.compile-formula B).
         ;; Let E = (logic.compile-formula C).
         ;; Now (logic.compile-formula A) is (if D t E).
         (let* ((subproofs-b (build.compile-formula (logic.vlhs a)))
                (subproofs-c (build.compile-formula (logic.vrhs a)))
                ;; Sub-B1: ~B v D = t
                (sub-b1      (first subproofs-b))
                ;; Sub-B2: B v D = nil
                (sub-b2      (second subproofs-b))
                ;; Sub-C1: ~C v E = t
                (sub-c1      (first subproofs-c))
                ;; Sub-C2: ~C v E = nil
                (sub-c2      (second subproofs-c))
                ;; Goal1: ~(B v C) v (if D t E) = t
                (goal-1 (@derive ((v (! B) (= (? d) t))                        (@given sub-b1))
                                 ((v (! C) (= (? e) t))                        (@given sub-c1))
                                 ((v (! (v B C)) (= (if (? d) t (? e)) t))     (build.compile-formula-lemma-2 @-- @-))))
                ;; Goal2: (B v C) v (if D t E) = nil
                (goal-2 (@derive ((v B (= (? d) nil))                          (@given sub-b2))
                                 ((v C (= (? e) nil))                          (@given sub-c2))
                                 ((v (v B C) (= (if (? d) t (? e)) nil))       (build.compile-formula-lemma-1 @-- @-)))))

           (list goal-1 goal-2)))

        ((equal (logic.fmtype a) 'pnot*)
         ;; Let A = ~B.
         ;; Let C = (logic.compile-formula B).
         ;; Now (logic.compile-formula A) is (if C nil t).
         (let* ((subproofs (build.compile-formula (logic.~arg a)))
                ;; Sub1: ~B v C = t
                (sub1      (first subproofs))
                ;; Sub2: B v C = nil
                (sub2      (second subproofs))
                ;; Goal1: ~~B v (if C nil t) = t
                (goal-1 (@derive ((v B (= (? c) nil))                          (@given sub2))
                                 ((v B (= (if (? c) nil t) t))                 (build.disjoined-if-when-nil @- (@term nil) (@term t)))
                                 ((v (! (! B)) (= (if (? c) nil t) t))         (build.lhs-insert-neg-neg @-))))
                ;; Goal2: ~B v (if C nil t) = nil
                (goal-2 (@derive ((v (! B) (= (? c) t))                        (@given sub1))
                                 ((v (! B) (!= (? c) nil))                     (build.disjoined-not-nil-from-t @-))
                                 ((v (! B) (= (if (? c) nil t) nil))           (build.disjoined-if-when-not-nil @- (@term nil) (@term t))))))
           (list goal-1 goal-2)))


        ((equal (logic.fmtype a) 'pequal*)
         ;; Now (logic.compile-formula A) is (equal lhs rhs).
         (let* ((left   (logic.=lhs a))
                (right  (logic.=rhs a))
                (goal-1 (@derive ((v (!= x y) (= (equal x y) t))                     (build.axiom (axiom-equal-when-same)))
                                 ((v (!= (? l) (? r)) (= (equal (? l) (? r)) t))     (build.instantiation @- (list (cons 'x left) (cons 'y right))))))
                (goal-2 (@derive ((v (= x y) (= (equal x y) nil))                    (build.axiom (axiom-equal-when-diff)))
                                 ((v (= (? l) (? r)) (= (equal (? l) (? r)) nil))    (build.instantiation @- (list (cons 'x left) (cons 'y right)))))))
           (list goal-1 goal-2)))

        (t nil)))



(defobligations build.compile-formula
  (build.instantiation
   build.lhs-insert-neg-neg
   build.disjoined-if-when-nil
   build.disjoined-if-when-not-nil
   build.compile-formula-lemma-1
   build.compile-formula-lemma-2
   build.disjoined-not-nil-from-t
   build.disjoined-not-t-from-nil
   build.disjoined-not-nil-from-t
   build.disjoined-t-from-not-nil)
  :extra-axioms ((axiom-equal-when-same)
                 (axiom-equal-when-diff)))


(encapsulate
 ()
 (local (defthm lemma
          (implies (logic.formulap x)
                   (let ((result (logic.compile-formula x))
                         (proofs (build.compile-formula x)))
                     (and (logic.appealp (first proofs))
                          (logic.appealp (second proofs))
                          (equal (logic.conclusion (first proofs)) (logic.por (logic.pnot x) (logic.pequal result ''t)))
                          (equal (logic.conclusion (second proofs)) (logic.por x (logic.pequal result ''nil)))
                          )))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.compile-formula x)
                  :in-theory (enable logic.compile-formula
                                     build.compile-formula
                                     axiom-equal-when-same
                                     axiom-equal-when-diff)))))

 (defthm forcing-logic.appealp-of-first-of-build.compile-formula
   (implies (force (logic.formulap x))
            (equal (logic.appealp (first (build.compile-formula x)))
                   t))
   :hints(("Goal" :use ((:instance lemma)))))

 (defthm forcing-logic.appealp-of-second-of-build.compile-formula
   (implies (force (logic.formulap x))
            (equal (logic.appealp (second (build.compile-formula x)))
                   t))
   :hints(("Goal" :use ((:instance lemma)))))

 (defthm forcing-logic.conclusion-of-first-of-build.compile-formula
   (implies (force (logic.formulap x))
            (equal (logic.conclusion (first (build.compile-formula x)))
                   (logic.por (logic.pnot x) (logic.pequal (logic.compile-formula x) ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma)))))

 (defthm forcing-logic.conclusion-of-second-of-build.compile-formula
   (implies (force (logic.formulap x))
            (equal (logic.conclusion (second (build.compile-formula x)))
                   (logic.por x (logic.pequal (logic.compile-formula x) ''nil))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma))))))



(encapsulate
 ()
 (local (defthm@ lemma
          (implies (and (logic.formulap x)
                        (logic.formula-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations build.compile-formula))
                   (and (logic.proofp (first (build.compile-formula x)) axioms thms atbl)
                        (logic.proofp (second (build.compile-formula x)) axioms thms atbl)))
          :hints(("Goal" :in-theory (enable build.compile-formula
                                            logic.compile-formula
                                            axiom-equal-when-same
                                            axiom-equal-when-diff)))))

 (defthm@ forcing-logic.proofp-of-first-of-build.compile-formula
   (implies (force (and (logic.formulap x)
                        (logic.formula-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations build.compile-formula)))
            (equal (logic.proofp (first (build.compile-formula x)) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma)))))

 (defthm@ forcing-logic.proofp-of-second-of-build.compile-formula
   (implies (force (and (logic.formulap x)
                        (logic.formula-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations build.compile-formula)))
            (equal (logic.proofp (second (build.compile-formula x)) axioms thms atbl)
                   t))
   :hints(("Goal" :use ((:instance lemma))))))


(verify-guards build.compile-formula
               :hints(("Goal" :in-theory (enable axiom-equal-when-same
                                                 axiom-equal-when-diff))))


(defprojection
  :list (logic.compile-formula-list x)
  :element (logic.compile-formula x)
  :guard (logic.formula-listp x)
  :nil-preservingp t)

(defthm forcing-logic.term-listp-of-logic.compile-formula-list
  (implies (force (logic.formula-listp x))
           (equal (logic.term-listp (logic.compile-formula-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-logic.compile-formula-list
  (implies (force (and (logic.formula-listp x)
                       (logic.formula-list-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (equal (cdr (lookup 'equal atbl)) 2)))
           (equal (logic.term-list-atblp (logic.compile-formula-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund build.compile-formula-list-comm-2 (x)
  (declare (xargs :guard (logic.formula-listp x)))
  (if (consp x)
      (cons (build.commute-or (second (build.compile-formula (car x))))
            (build.compile-formula-list-comm-2 (cdr x)))
    nil))

(defobligations build.compile-formula-list-comm-2
  (build.commute-or
   build.compile-formula))

(encapsulate
 ()
 (local (in-theory (enable build.compile-formula-list-comm-2)))

 (defthm len-of-build.compile-formula-list-comm-2
   (equal (len (build.compile-formula-list-comm-2 x))
          (len x)))

 (defthm logic.appeal-listp-of-build.compile-formula-list-comm-2
   (implies (force (logic.formula-listp x))
            (equal (logic.appeal-listp (build.compile-formula-list-comm-2 x))
                   t)))

 (defthm logic.strip-conclusions-of-logic.compile-formula-list-bldr3
   (implies (force (logic.formula-listp x))
            (equal (logic.strip-conclusions (build.compile-formula-list-comm-2 x))
                   (logic.por-list
                    (logic.pequal-list (logic.compile-formula-list x)
                                       (repeat ''nil (len x)))
                    x))))

 (defthm@ logic.proof-listp-of-build.compile-formula-list-comm-2
   (implies (force (and (logic.formula-listp x)
                        ;; ---
                        (logic.formula-list-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations build.compile-formula-list-comm-2)
                        ))
            (equal (logic.proof-listp (build.compile-formula-list-comm-2 x) axioms thms atbl)
                   t))))

(dd.close)
