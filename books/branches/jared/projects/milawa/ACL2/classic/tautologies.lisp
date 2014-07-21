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
(include-book "../logic/formula-size")
(include-book "../logic/piff")  ;; Yuck!
(include-book "../build/disjoined-subset")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; This is a port of Shankar's tautology checker from his work formalizing
;; Godel's incompleteness theorem in NQTHM, which in turn was based on
;; Shoenfield's proof of the tautology theorem.
;;
;;  - We introduce a tautology checker (see tautologyp1/tautologyp) that
;;    operates on formulas, returning t if the formula is a tautology and nil
;;    otherwise.
;;
;;  - We show that whenever tautologyp accepts a formula, its truth value is
;;    true for every truth valuation
;;
;;  - We show that whenever tautologyp rejects a formula, there is some truth
;;    valuation which makes that formula's truth value false.
;;
;;  - We introduce a tautology builder (see tautology-bldr1/tautology-bldr)
;;    which can construct a proof of an arbitrary tautology, and show that it
;;    does in fact construct a proof for any formula that our tautologyp
;;    function accepts.
;;
;;
;; We adopt Shoenfield's definition of tautologies: a tautology is a formula
;; whose truth value is true under every possible truth valuation.
;;
;; Definition.  A truth valuation is a mapping from every atomic formula
;; (formulas of the form t1 = t2) to truth values (true or false).  Given a
;; truth valuation V, we assign a truth value to each formula as follows:
;;
;;    1. Val(t1 = t2) is true iff Val maps t1=t2 to true
;;    2. Val(~F) is not(Val(F))
;;    3. Val(F v G) is or(Val(F),Val(G))
;;
;; We represent truth valuations as simple lists of atomic formulas.  We assign
;; true to formulas in the list, and false to formulas not in the list.
;;
;; Why is this a legitimate representation?  After all, we said that a truth
;; valuation maps *every* atomic formula to true or false.  But surely there
;; are infinitely many atomic formulas, and yet our lists are finite.  Haven't
;; we failed to cover those truth valuations which map all formulas to true, or
;; even those which simply map some infinite number of formulas to true?
;;
;; Although we cannot represent such valuations as lists, we really don't need
;; to do so if our goal is only to determine if a formula is a tautology or
;; not.  After all, any formula is itself finite, and hence contains at most
;; some finite number of atomic formulas.  Hence, to determine if a formula F
;; is a tautology or not, we only need to consider the bindings of the atomic
;; formulas within F, all of which can be represented finitely.
;;
;; We begin by introducing the function truth-value below, which evaluates a
;; formula with respect to a truth valuation.

(defund truth-value (f valuation)
  (declare (xargs :guard (logic.formulap f)))
  (cond ((equal (logic.fmtype f) 'por*)
         (or (truth-value (logic.vlhs f) valuation)
             (truth-value (logic.vrhs f) valuation)))
        ((equal (logic.fmtype f) 'pnot*)
         (not (truth-value (logic.~arg f) valuation)))
        ((equal (logic.fmtype f) 'pequal*)
         (memberp f valuation))
        (t nil)))

(defthm booleanp-of-truth-value
  (equal (booleanp (truth-value f valuation))
         t)
  :hints(("Goal" :in-theory (e/d (truth-value)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm truth-value-of-list-fix
  (equal (truth-value f (list-fix valuation))
         (truth-value f valuation))
  :hints(("Goal" :in-theory (e/d (truth-value)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm truth-value-when-logic.por
  (implies (equal (logic.fmtype f) 'por*)
           (equal (truth-value f valuation)
                  (or (truth-value (logic.vlhs f) valuation)
                      (truth-value (logic.vrhs f) valuation))))
  :hints(("Goal" :in-theory (enable truth-value))))

(defthm truth-value-when-logic.pnot
  (implies (equal (logic.fmtype f) 'pnot*)
           (equal (truth-value f valuation)
                  (not (truth-value (logic.~arg f) valuation))))
  :hints(("Goal" :in-theory (enable truth-value))))

(defthm truth-value-when-pequal
  (implies (equal (logic.fmtype f) 'pequal*)
           (equal (truth-value f valuation)
                  (memberp f valuation)))
  :hints(("Goal" :in-theory (enable truth-value))))

(defthm truth-value-when-degenerate
  (implies (and (not (equal (logic.fmtype f) 'por*))
                (not (equal (logic.fmtype f) 'pnot*))
                (not (equal (logic.fmtype f) 'pequal*)))
           (equal (truth-value f valuation)
                  nil))
  :hints(("Goal" :in-theory (e/d (truth-value)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm forcing-truth-value-of-logic.por
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (truth-value (logic.por x y) valuation)
                  (or (truth-value x valuation)
                      (truth-value y valuation))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm forcing-truth-value-of-logic.pnot
  (implies (force (logic.formulap x))
           (equal (truth-value (logic.pnot x) valuation)
                  (not (truth-value x valuation))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm forcing-truth-value-of-pequal
  (implies (and (force (logic.termp x))
                (force (logic.termp y)))
           (equal (truth-value (logic.pequal x y) valuation)
                  (memberp (logic.pequal x y) valuation)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm forcing-truth-value-of-logic.pand
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (truth-value (logic.pand x y) valuation)
                  (and (truth-value x valuation)
                       (truth-value y valuation))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.pand))))

(defthm forcing-truth-value-of-logic.piff
  (implies (and (force (logic.formulap x))
                (force (logic.formulap y)))
           (equal (truth-value (logic.piff x y) valuation)
                  (iff (truth-value x valuation)
                       (truth-value y valuation))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.piff))))


(deftheory slow-truth-value-theory
  '(truth-value-when-logic.por
    truth-value-when-logic.pnot
    truth-value-when-pequal
    truth-value-when-degenerate))

(in-theory (disable slow-truth-value-theory))




;; Suppose we want to reason about the truth value of logic.disjoin-formulas
;; under some valuation.  Then the value will be true iff one of the formulas
;; we are about to disjoin happens to be true under the valuation.  The
;; function find-positive searches for a formula that has a true truth-value
;; under a valuation, returning the first such formula found, or nil if no such
;; formula exists.

(defund find-positive (x valuation)
  (declare (xargs :guard (logic.formula-listp x)))
  (if (consp x)
      (if (truth-value (car x) valuation)
          (car x)
        (find-positive (cdr x) valuation))
    nil))

(defthm find-positive-when-not-consp
  (implies (not (consp x))
           (equal (find-positive x valuation)
                  nil))
  :hints(("Goal" :in-theory (enable find-positive))))

(defthm find-positive-of-cons
  (equal (find-positive (cons a x) valuation)
         (if (truth-value a valuation)
             a
           (find-positive x valuation)))
  :hints(("Goal" :in-theory (enable find-positive))))

(defthm find-positive-of-list-fix-one
  (equal (find-positive (list-fix x) valuation)
         (find-positive x valuation))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-positive-of-list-fix-two
  (equal (find-positive x (list-fix valuation))
         (find-positive x valuation))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-positive-of-app
  (equal (find-positive (app x y) valuation)
         (or (find-positive x valuation)
             (find-positive y valuation)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable slow-truth-value-theory))))

(defthm find-positive-when-memberp-with-true-value
  (implies (and (memberp a x)
                (truth-value a valuation))
           (iff (find-positive x valuation)
                t))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable slow-truth-value-theory))))

(defthm memberp-of-find-positive-when-find-positive
  (implies (find-positive x valuation)
           (equal (memberp (find-positive x valuation) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm truth-value-of-find-positive-when-find-positive
  (implies (find-positive x valuation)
           (equal (truth-value (find-positive x valuation) valuation)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-positive-when-subsetp
  (implies (and (find-positive x valuation)
                (subsetp x y))
           (iff (find-positive y valuation)
                t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-positive-when-find-positive-of-cdr
  (implies (find-positive (cdr x) valuation)
           (find-positive x valuation)))

(defthm find-positive-when-not-find-positive-of-cdr
  (implies (not (find-positive (cdr x) valuation))
           (equal (find-positive x valuation)
                  (if (truth-value (car x) valuation)
                      (car x)
                    nil))))

(defthm find-positive-when-complementary-members
  (implies (and (memberp (logic.pnot a) x)
                (memberp a x)
                (logic.formula-listp x))
           (iff (find-positive x valuation)
                t))
  :hints(("Goal" :cases ((truth-value a valuation)))))

(defthm find-positive-when-complementary-members-alt
  (implies (and (memberp (logic.~arg a) x)
                (memberp a x)
                (equal (logic.fmtype a) 'pnot*)
                (logic.formula-listp x))
           (iff (find-positive x valuation)
                t))
  :hints(("Goal"
          :in-theory (enable slow-truth-value-theory)
          :cases ((truth-value a valuation)))))

(defthm find-positive-when-complementary-members-app-one
  (implies (and (memberp (logic.pnot a) x)
                (memberp a (app x y))
                (logic.formula-listp x)
                (logic.formula-listp y))
           (iff (find-positive (app x y) valuation)
                t))
  :hints(("Goal"
          :in-theory (disable find-positive-when-complementary-members)
          :use ((:instance find-positive-when-complementary-members
                           (x (app x y)))))))

(defthm find-positive-when-complementary-members-app-two
  (implies (and (memberp (logic.pnot a) y)
                (memberp a (app x y))
                (logic.formula-listp x)
                (logic.formula-listp y))
           (iff (find-positive (app x y) valuation)
                t))
  :hints(("Goal"
          :in-theory (disable find-positive-when-complementary-members)
          :use ((:instance find-positive-when-complementary-members
                           (x (app x y)))))))

(defthm find-positive-when-complementary-members-app-alt-one
  (implies (and (memberp (logic.~arg a) x)
                (memberp a (app x y))
                (equal (logic.fmtype a) 'pnot*)
                (logic.formula-listp x)
                (logic.formula-listp y))
           (iff (find-positive (app x y) valuation)
                t))
  :hints(("Goal"
          :in-theory (disable find-positive-when-complementary-members-alt)
          :use ((:instance find-positive-when-complementary-members-alt
                           (x (app x y)))))))

(defthm find-positive-when-complementary-members-app-alt-two
  (implies (and (memberp (logic.~arg a) y)
                (memberp a (app x y))
                (equal (logic.fmtype a) 'pnot*)
                (logic.formula-listp x)
                (logic.formula-listp y))
           (iff (find-positive (app x y) valuation)
                t))
  :hints(("Goal"
          :in-theory (disable find-positive-when-complementary-members-alt)
          :use ((:instance find-positive-when-complementary-members-alt
                           (x (app x y)))))))

(defthm forcing-truth-valuation-of-disjoin-formula-under-iff
  (implies (force (logic.formula-listp x))
           (iff (truth-value (logic.disjoin-formulas x) valuation)
                (find-positive x valuation)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable slow-truth-value-theory logic.disjoin-formulas))))






;; "Basic formulas" play a particularly important role in our tautology
;; checker.  And, for guards and for certain theorems, we need to be able to
;; talk about lists of basic formulas.  (Shoenfield calls these "lists of
;; elementary formulas and their negations").  We now introduce the function
;; basic-logic.formula-listp, which checks to see if every formula in a list is
;; basic.

;; BOZO my god this is crying out for deflist.

(defund basic-logic.formula-listp (x)
  (declare (xargs :guard (logic.formula-listp x)))
  (if (consp x)
      (and (or (equal (logic.fmtype (car x)) 'pequal*)
               (and (equal (logic.fmtype (car x)) 'pnot*)
                    (equal (logic.fmtype (logic.~arg (car x))) 'pequal*)))
           (basic-logic.formula-listp (cdr x)))
    t))

(defthm basic-logic.formula-listp-when-not-consp
  (implies (not (consp x))
           (equal (basic-logic.formula-listp x)
                  t))
  :hints(("Goal" :in-theory (enable basic-logic.formula-listp))))

(defthm basic-logic.formula-listp-of-cons
  (equal (basic-logic.formula-listp (cons a x))
         (and (or (equal (logic.fmtype a) 'pequal*)
                  (and (equal (logic.fmtype a) 'pnot*)
                       (equal (logic.fmtype (logic.~arg a)) 'pequal*)))
              (basic-logic.formula-listp x)))
  :hints(("Goal" :in-theory (enable basic-logic.formula-listp))))

(defthm all-listeralsp-of-list-fix
  (equal (basic-logic.formula-listp (list-fix x))
         (basic-logic.formula-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm booleanp-of-basic-logic.formula-listp
  (equal (booleanp (basic-logic.formula-listp x))
         t)
  :hints(("Goal" :induct (cdr-induction x))))

(defthm basic-logic.formula-listp-of-cdr-when-basic-logic.formula-listp
  (implies (basic-logic.formula-listp x)
           (equal (basic-logic.formula-listp (cdr x))
                  t)))

(defthm logic.fmtype-logic.pnot-when-non-pequal-memberp-of-basic-logic.formula-listp
  (implies (and (memberp a x)
                (basic-logic.formula-listp x)
                (not (equal (logic.fmtype a) 'pequal*)))
           (equal (logic.fmtype a) 'pnot*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-of-logic.~arg-when-non-pequal-memberp-of-basic-logic.formula-listp
  (implies (and (memberp a x)
                (basic-logic.formula-listp x)
                (not (equal (logic.fmtype a) 'pequal*)))
           (equal (logic.fmtype (logic.~arg a)) 'pequal*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-of-logic.~arg-when-logic.pnot-memberp-of-basic-logic.formula-listp
  (implies (and (memberp a x)
                (basic-logic.formula-listp x)
                (equal (logic.fmtype a) 'pnot*))
           (equal (logic.fmtype (logic.~arg a)) 'pequal*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-pequal-when-non-logic.pnot-memberp-of-basic-logic.formula-listp
  (implies (and (memberp a x)
                (basic-logic.formula-listp x)
                (not (equal (logic.fmtype a) 'pnot*)))
           (equal (logic.fmtype a) 'pequal*))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-logic.pnot-when-non-pequal-car-of-basic-logic.formula-listp
  (implies (and (basic-logic.formula-listp x)
                (force (consp x))
                (not (equal (logic.fmtype (car x)) 'pequal*)))
           (equal (logic.fmtype (car x)) 'pnot*)))

(defthm logic.fmtype-of-logic.~arg-when-non-pequal-car-of-basic-logic.formula-listp
  (implies (and (basic-logic.formula-listp x)
                (force (consp x))
                (not (equal (logic.fmtype (car x)) 'pequal*)))
           (equal (logic.fmtype (logic.~arg (car x))) 'pequal*)))

(defthm logic.fmtype-of-logic.~arg-when-logic.pnot-car-of-basic-logic.formula-listp
  (implies (and (basic-logic.formula-listp x)
                (force (consp x))
                (equal (logic.fmtype (car x)) 'pnot*))
           (equal (logic.fmtype (logic.~arg (car x))) 'pequal*)))

(defthm logic.fmtype-pequal-when-non-logic.pnot-car-of-basic-logic.formula-listp
  (implies (and (basic-logic.formula-listp x)
                (force (consp x))
                (not (equal (logic.fmtype (car x)) 'pnot*)))
           (equal (logic.fmtype (car x)) 'pequal*)))

(defthm logic.fmtype-when-memberp-and-basic-logic.formula-listp
  (implies (and (basic-logic.formula-listp x)
                (memberp a x))
           (or (equal (logic.fmtype a) 'pequal*)
               (and (equal (logic.fmtype a) 'pnot*)
                    (equal (logic.fmtype (logic.~arg a)) 'pequal*))))
  :rule-classes nil)

(defthm basic-logic.formula-listp-of-app
  (equal (basic-logic.formula-listp (app x y))
         (and (basic-logic.formula-listp x)
              (basic-logic.formula-listp y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm basic-logic.formula-listp-when-subset-one
  (implies (and (basic-logic.formula-listp y)
                (subsetp x y))
           (basic-logic.formula-listp x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable basic-logic.formula-listp))))

(defthm basic-logic.formula-listp-when-subset-two
  (implies (and (subsetp x y)
                (basic-logic.formula-listp y))
           (basic-logic.formula-listp x)))




;; Another important idea that we will introduce before discussing the
;; tautology checker itself is the following.  Suppose that the basic formulas
;; t1 = t2 and t1 != t2 both occur within some list of basic formulas.  Then,
;; we say that the list contains complementary formulas.  We write the function
;; find-complements to search for complementary formulas.

(defund find-complements (x)
  (declare (xargs :guard (and (logic.formula-listp x)
                              (basic-logic.formula-listp x))))
  (if (consp x)
      (if (if (equal (logic.fmtype (car x)) 'pnot*)
              (memberp (logic.~arg (car x)) (cdr x))
            (memberp (logic.pnot (car x)) (cdr x)))
          (car x)
        (find-complements (cdr x)))
    nil))

(defthm find-complements-when-not-consp
  (implies (not (consp x))
           (not (find-complements x)))
  :hints(("Goal" :in-theory (enable find-complements))))

(defthm find-complements-of-cons
  (equal (find-complements (cons a x))
         (if (if (equal (logic.fmtype a) 'pnot*)
                 (memberp (logic.~arg a) x)
               (memberp (logic.pnot a) x))
             a
           (find-complements x)))
  :hints(("Goal" :in-theory (enable find-complements))))

(defthm find-complements-of-list-fix
  (equal (find-complements (list-fix x))
         (find-complements x))
  :hints(("Goal" :induct (cdr-induction x))))


(defthm not-find-complements-of-cdr-when-not-find-complements
  (implies (and (not (find-complements x))
                (force (logic.formula-listp x)))
           (not (find-complements (cdr x)))))

(defthm find-complements-when-not-find-complements-of-cdr
  (implies (not (find-complements (cdr x)))
           (equal (find-complements x)
                  (if (if (equal (logic.fmtype (car x)) 'pnot*)
                          (memberp (logic.~arg (car x)) (cdr x))
                        (memberp (logic.pnot (car x)) (cdr x)))
                      (car x)
                    nil))))

(defthm memberp-of-find-complements
  (implies (find-complements x)
           (memberp (find-complements x) x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.pnot-of-find-complements
  (implies (and (find-complements x)
                (equal (logic.fmtype (find-complements x)) 'pequal*))
           (memberp (logic.pnot (find-complements x)) x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.~arg-of-find-complements
  (implies (and (find-complements x)
                (equal (logic.fmtype (find-complements x)) 'pnot*))
           (memberp (logic.~arg (find-complements x)) x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-complements-when-complementary-members-one
  (implies (and (memberp (logic.pnot a) x)
                (memberp a x)
                (equal (logic.fmtype a) 'pequal*)
                (force (logic.formula-listp x)))
           (find-complements x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm find-complements-when-complementary-members-two
  (implies (and (memberp (logic.~arg a) x)
                (memberp a x)
                (equal (logic.fmtype a) 'pnot*)
                (equal (logic.fmtype (logic.~arg a)) 'pequal*)
                (force (logic.formula-listp x)))
           (find-complements x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-of-find-complements-when-not-pequal
  (implies (and (force (logic.formula-listp x))
                (force (basic-logic.formula-listp x))
                (find-complements x)
                (not (equal (logic.fmtype (find-complements x)) 'pequal*)))
           (equal (logic.fmtype (find-complements x))
                  'pnot*))
  :hints(("Goal" :in-theory (enable find-complements))))

(defthm logic.fmtype-of-find-complements-when-not-logic.pnot
  (implies (and (force (logic.formula-listp x))
                (force (basic-logic.formula-listp x))
                (find-complements x)
                (not (equal (logic.fmtype (find-complements x)) 'pnot*)))
           (equal (logic.fmtype (find-complements x))
                  'pequal*))
  :hints(("Goal" :in-theory (enable find-complements))))

(encapsulate
 ()
 (local (defthm lemma1
          (implies (and (force (logic.formula-listp y))
                        (force (basic-logic.formula-listp y))
                        (find-complements x)
                        (equal (logic.fmtype (find-complements x)) 'pequal*)
                        (subsetp x y))
                   (find-complements y))
          :hints(("Goal"
                  :in-theory (disable in-superset-when-in-subset-one
                                      in-superset-when-in-subset-two)
                  :use ((:instance in-superset-when-in-subset-one
                                   (a (find-complements x))
                                   (x x)
                                   (y y))
                        (:instance in-superset-when-in-subset-one
                                   (a (logic.pnot (find-complements x)))
                                   (x x)
                                   (y y)))))))

 (local (defthm lemma2
          (implies (and (force (logic.formula-listp y))
                        (force (basic-logic.formula-listp y))
                        (find-complements x)
                        (equal (logic.fmtype (find-complements x)) 'pnot*)
                        (subsetp x y))
                   (find-complements y))
          :hints(("Goal"
                  :in-theory (disable in-superset-when-in-subset-one
                                      in-superset-when-in-subset-two)
                  :use ((:instance in-superset-when-in-subset-one
                                   (a (find-complements x))
                                   (x x)
                                   (y y))
                        (:instance in-superset-when-in-subset-one
                                   (a (logic.~arg (find-complements x)))
                                   (x x)
                                   (y y)))))))

 (defthm find-complements-when-find-complements-of-subset-one
   (implies (and (find-complements x)
                 (subsetp x y)
                 (force (logic.formula-listp y))
                 (force (basic-logic.formula-listp y)))
            (find-complements y))
   :hints(("Goal"
           :cases ((equal (logic.fmtype (find-complements x)) 'pequal*)
                   (equal (logic.fmtype (find-complements x)) 'pnot*)))))

 (defthm find-complements-when-find-complements-of-subset-two
   (implies (and (subsetp x y)
                 (find-complements x)
                 (force (logic.formula-listp y))
                 (force (basic-logic.formula-listp y)))
            (find-complements y)))

 (defthm not-find-complements-when-not-find-complements-of-superset-one
   (implies (and (not (find-complements y))
                 (subsetp x y)
                 (force (logic.formula-listp y))
                 (force (basic-logic.formula-listp y)))
            (not (find-complements x))))

 (defthm not-find-complements-when-not-find-complements-of-superset-two
   (implies (and (subsetp x y)
                 (not (find-complements y))
                 (force (logic.formula-listp y))
                 (force (basic-logic.formula-listp y)))
            (not (find-complements x)))))



;; One of the key theorems about basic formula lists is the following.  Suppose
;; that the list contains complementary formulas.  Then, we can always find at
;; least some formula which evaluates to true under any arbitrary truth
;; valuation.

(defthm find-positive-when-find-complements
  (implies (and (logic.formula-listp x)
                (basic-logic.formula-listp x)
                (find-complements x))
           (find-positive x valuation))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable slow-truth-value-theory))))



;; Finally, suppose that we are given a list of basic formulas.  If there are
;; no complementary formulas in the list, then it is possible to construct a
;; valuation which will render the disjunction false.  (See Shoenfield, at the
;; top of page 27.)  Essentially, we construct a valuation V as follows.  Let
;; V(t1 = t2) be true iff t1 != t2 is a member of the list.  In Shankar's
;; implementation, this is the function "falsify".

(defund falsify-formulas (x)
  (declare (xargs :guard (and (logic.formula-listp x)
                              (basic-logic.formula-listp x)
                              (not (find-complements x)))))
  (if (consp x)
      (if (equal (logic.fmtype (car x)) 'pnot*)
          (cons (logic.~arg (car x))
                (falsify-formulas (cdr x)))
        (falsify-formulas (cdr x)))
    nil))

(defthm falsify-formulas-when-not-consp
  (implies (not (consp x))
           (equal (falsify-formulas x)
                  nil))
  :hints(("Goal" :in-theory (enable falsify-formulas))))

(defthm true-listp-of-falsify-formulas
  (equal (true-listp (falsify-formulas x))
         t)
  :hints(("Goal" :in-theory (enable falsify-formulas))))

(defthm memberp-of-falsify-formulas
  (implies (and (force (logic.formula-listp x))
                (force (logic.formulap a)))
           (equal (memberp a (falsify-formulas x))
                  (memberp (logic.pnot a) x)))
  :hints(("Goal" :in-theory (enable falsify-formulas))))

(encapsulate
 ()
 (local (defthm lemma1
          ;; If L \in X is of the form t1 = t2, then it evaluates to true under
          ;; the falsifying valuation only when its complement t1 != t2 is also
          ;; a member of the list.
          (implies (and (force (logic.formula-listp x))
                        (force (basic-logic.formula-listp x))
                        (memberp a x)
                        (equal (logic.fmtype a) 'pequal*))
                   (equal (truth-value a (falsify-formulas x))
                          (memberp (logic.pnot a) x)))
          :hints(("Goal" :in-theory (enable slow-truth-value-theory)))))

 (local (defthm lemma2
          ;; We can conclude from Lemma 1 that if find-positive is able to find
          ;; a positive formula L (i.e., L is of the form t1 = t2) which
          ;; evaluates to true under the falsifying valuation, then X must have
          ;; some complementary formula.  After all, since L evaluates to true,
          ;; t1 != t2 must be in X.
          (implies (and (force (logic.formula-listp x))
                        (force (basic-logic.formula-listp x))
                        (find-positive x (falsify-formulas x))
                        (equal (logic.fmtype (find-positive x (falsify-formulas x)))
                               'pequal*))
                   (find-complements x))
          :hints(("Goal" :in-theory (disable lemma1)
                  :use ((:instance lemma1
                                   (a (find-positive x (falsify-formulas x)))
                                   (x x)))))))

 (local (defthm lemma3
          ;; Alternately, if L \in X is of the form t1 != t2, then it surely
          ;; does not evaluate to true under the falsifying valuation, because
          ;; the falsifying valuation will bind t1 = t2 to true, and hence t1
          ;; != t2 is false.
          (implies (and (force (logic.formula-listp x))
                        (force (basic-logic.formula-listp x))
                        (memberp a x)
                        (equal (logic.fmtype a) 'pnot*)
                        (equal (logic.fmtype (logic.~arg a)) 'pequal*))
                   (not (truth-value a (falsify-formulas x))))
          :hints(("Goal" :in-theory (enable slow-truth-value-theory)))))

 (local (defthm lemma4
          ;; And as a result of Lemma 3, we see that the if find positive is
          ;; able to find some formulas L which evaluates to true under the
          ;; falsifying valuation, then surely L must be positive.
          (implies (and (force (logic.formula-listp x))
                        (force (basic-logic.formula-listp x))
                        (find-positive x (falsify-formulas x)))
                   (equal (logic.fmtype (find-positive x (falsify-formulas x))) 'pequal*))
          :hints(("Goal"
                  :in-theory (disable lemma3)
                  :use ((:instance logic.fmtype-when-memberp-and-basic-logic.formula-listp
                                   (a (find-positive x (falsify-formulas x)))
                                   (x x))
                        (:instance lemma3
                                   (a (find-positive x (falsify-formulas x)))
                                   (x x)))))))

 (local (defthm lemma5
          ;; Chaining together Lemmas 2 and 4, we see that whenever
          ;; find-positive returns true, it must be the case that
          ;; find-complements is successful.
          (implies (and (force (logic.formula-listp x))
                        (force (basic-logic.formula-listp x))
                        (find-positive x (falsify-formulas x)))
                   (find-complements x))))

 (defthm find-positive-of-falsify-formulas
   ;; We have already proven the other half of the implication in Lemma 5 in a
   ;; more general setting, in the theorem find-positive-when-find-complements.
   ;; So, we can now provide an iff-rewrite and say that find-positive finds an
   ;; acceptable formula only when complementary formulas exist.
   (implies (and (force (logic.formula-listp x))
                 (force (basic-logic.formula-listp x)))
            (iff (find-positive x (falsify-formulas x))
                 (find-complements x)))))






;; We now introduce our main tautology checking function, tautologyp1.  We take
;; as inputs two lists of formulas, As and Acc.  We assume that acc is a list
;; of basic formulas with no complementary members, and we return true only
;; when the disjunction of (app as acc) is a tautology.  This function is like
;; Shankar's function of the same name.  We prove that the function is "sound
;; and complete" in the sense that it only accepts tautologies, and anything it
;; rejects is not a tautology.

(local (defthm termination-crock-1
         (implies (and (equal (logic.fmtype as1) 'pnot*)
                       (equal (logic.fmtype (logic.~arg as1)) 'por*))
                  (< (+ 1 (logic.formula-size (logic.vrhs (logic.~arg as1))))
                          (logic.formula-size as1)))
         :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vrhs logic.~arg)))))

(local (defthm termination-crock-2
         (implies (and (equal (logic.fmtype x) 'pnot*)
                       (equal (logic.fmtype (logic.~arg x)) 'pnot*))
                  (< (logic.formula-size (logic.~arg (logic.~arg x)))
                     (logic.formula-size x)))
         :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.~arg)))))

(local (defthm termination-crock-3
         (implies (and (equal (logic.fmtype x) 'pnot*)
                       (equal (logic.fmtype (logic.~arg x)) 'por*))
                  (< (+ 1 (logic.formula-size (logic.vlhs (logic.~arg x))))
                     (logic.formula-size x)))
         :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vlhs logic.~arg)))))

(local (defthm termination-crock-4
         (implies (equal (logic.fmtype as1) 'por*)
                  (< (+ (logic.formula-size (logic.vlhs as1))
                                      (logic.formula-size (logic.vrhs as1)))
                     (logic.formula-size as1)))
         :hints(("Goal" :in-theory (enable logic.formula-size logic.fmtype logic.vlhs logic.vrhs)))))

(defund tautologyp1 (as acc)
  (declare (xargs :guard (and (logic.formula-listp as)
                              (logic.formula-listp acc))
                  :measure (logic.formula-list-size as)
                  :hints(("Goal" :in-theory (disable logic.fmtype-normalizer-cheap)))))
  (if (consp as)
      (let ((A1 (car as)))
        (cond

         ;; TC([B v C,...], acc) = TC([B,C,...], acc)
         ((equal (logic.fmtype A1) 'por*)
          (tautologyp1 (list* (logic.vlhs A1) (logic.vrhs A1) (cdr as)) acc))

         ;; TC([~(B v C),...], acc) = TC([~B,...], acc) andalso
         ;;                           TC([~C,...], acc)
         ((and (equal (logic.fmtype A1) 'pnot*)
               (equal (logic.fmtype (logic.~arg A1)) 'por*))
          (and (tautologyp1 (cons (logic.pnot (logic.vlhs (logic.~arg A1)))
                                  (cdr as))
                            acc)
               (tautologyp1 (cons (logic.pnot (logic.vrhs (logic.~arg A1)))
                                  (cdr as))
                            acc)))

          ;; TC([~~B,...], acc) = TC([B,...], acc)
         ((and (equal (logic.fmtype A1) 'pnot*)
               (equal (logic.fmtype (logic.~arg A1)) 'pnot*))
          (tautologyp1 (cons (logic.~arg (logic.~arg A1))
                             (cdr as))
                       acc))

         ;; TC([~(t1=t2),...], acc) = memberp(t1=t2, acc) orelse
         ;;                           TC(..., ~(t1=t2)::acc)
         ((equal (logic.fmtype A1) 'pnot*)
          (or (memberp (logic.~arg A1) acc)
              (tautologyp1 (cdr as) (cons A1 acc))))

         ;; TC([t1=t2,...], acc) = memberp(~(t1=t2), acc) orelse
         ;;                        TC(..., t1=t2::acc)
         (t
          (or (memberp (logic.pnot A1) acc)
              (tautologyp1 (cdr as) (cons A1 acc))))))
    nil))

(defthm booleanp-of-tautologyp1
  (equal (booleanp (tautologyp1 as acc))
         t)
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-when-not-consp
  (implies (not (consp as))
           (not (tautologyp1 as acc)))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-list-fix-one
  (equal (tautologyp1 (list-fix as) acc)
         (tautologyp1 as acc))
  :hints(("Goal" :in-theory (enable tautologyp1
                                    ;; Yuck!  why?
                                    list-fix))))

(defthm tautologyp1-of-list-fix-two
  (equal (tautologyp1 as (list-fix acc))
         (tautologyp1 as acc))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-recursive-call-in-logic.por-case
  (implies (and (tautologyp1 as acc)
                (equal (logic.fmtype (car as)) 'por*))
           (equal (tautologyp1 (list* (logic.vlhs (car as)) (logic.vrhs (car as)) (cdr as)) acc)
                  t))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-recursive-calls-in-logic.pnot-of-logic.pors-case
  (implies (and (tautologyp1 as acc)
                (equal (logic.fmtype (car as)) 'pnot*)
                (equal (logic.fmtype (logic.~arg (car as))) 'por*))
           (and (tautologyp1 (cons (logic.pnot (logic.vlhs (logic.~arg (car as)))) (cdr as)) acc)
                (tautologyp1 (cons (logic.pnot (logic.vrhs (logic.~arg (car as)))) (cdr as)) acc)))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-recursive-call-in-logic.pnot-of-logic.pnot-case
  (implies (and (tautologyp1 as acc)
                (equal (logic.fmtype (car as)) 'pnot*)
                (equal (logic.fmtype (logic.~arg (car as))) 'pnot*))
           (equal (tautologyp1 (cons (logic.~arg (logic.~arg (car as))) (cdr as)) acc)
                  t))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-recursive-call-in-logic.pnot-of-pequal-case
  (implies (and (tautologyp1 as acc)
                (equal (logic.fmtype (car as)) 'pnot*)
                (equal (logic.fmtype (logic.~arg (car as))) 'pequal*)
                (not (memberp (logic.~arg (car as)) acc)))
           (equal (tautologyp1 (cdr as) (cons (car as) acc))
                  t))
  :hints(("Goal" :in-theory (enable tautologyp1))))

(defthm tautologyp1-of-recursive-call-in-pequal-case
  (implies (and (logic.formula-listp as)
                (tautologyp1 as acc)
                (equal (logic.fmtype (car as)) 'pequal*)
                (not (memberp (logic.pnot (car as)) acc)))
           (equal (tautologyp1 (cdr as) (cons (car as) acc))
                  t))
  :hints(("Goal" :in-theory (enable tautologyp1))))



;; We now begin our correctness argument for tautologyp1.  Our first goal is to
;; show that "tautologies are true".  In other words, suppose that as and acc
;; satisfy the conditions we have described.  Then, it follows that the
;; disjunction of (app as acc) must evaluate to true under every arbitrary
;; truth valuation.  Given our supporting definitions, the proof works out
;; easily.

(defthm forcing-tautologies-are-true
   (implies (and (force (logic.formula-listp as))
                 (force (logic.formula-listp acc))
                 (tautologyp1 as acc))
            (equal (truth-value (logic.disjoin-formulas (app as acc)) valuation)
                   t))
   :hints(("Goal" :in-theory (enable tautologyp1 slow-truth-value-theory))))



;; Our attention now turns to demonstrating the completeness of tautologyp1.
;; That is, suppose that tautologyp1 rejects its inputs.  Then, we would like
;; to show that there is some truth valuation which makes (app as acc) false.
;; To do this, we will actually construct such a valuation.

;; Shoenfield explains this process at the top of Page 27, and in Shankar's
;; work it appears as the function "falsify-taut", which we recreate below with
;; the appropriate changes.  We return a pair of the form (successp
;; . valuation), where if successp is true then valuation is a falsifying
;; valuation for this formula, and otherwise we have failed to produce such a
;; valuation.

(defund falsify-taut (as acc)
  (declare (xargs :measure (logic.formula-list-size as)
                  :guard (and (logic.formula-listp as)
                              (logic.formula-listp acc)
                              (basic-logic.formula-listp acc)
                              (not (find-complements acc)))
                  :verify-guards nil))
  (if (consp as)
      (let ((A1 (car as)))
        (cond ((equal (logic.fmtype A1) 'por*)
               (falsify-taut (list* (logic.vlhs A1) (logic.vrhs A1) (cdr as)) acc))
              ((and (equal (logic.fmtype A1) 'pnot*)
                    (equal (logic.fmtype (logic.~arg A1)) 'por*))
               (let* ((candidate (falsify-taut (cons (logic.pnot (logic.vlhs (logic.~arg A1)))
                                                     (cdr as))
                                               acc))
                      (successp (car candidate)))
                 (if successp
                     candidate
                   (falsify-taut (cons (logic.pnot (logic.vrhs (logic.~arg A1)))
                                       (cdr as))
                                 acc))))
              ((and (equal (logic.fmtype A1) 'pnot*)
                    (equal (logic.fmtype (logic.~arg A1)) 'pnot*))
               (falsify-taut (cons (logic.~arg (logic.~arg A1))
                                   (cdr as))
                             acc))
              ((equal (logic.fmtype A1) 'pnot*)
               (if (memberp (logic.~arg A1) acc)
                   '(nil . nil)
                 (falsify-taut (cdr as) (cons A1 acc))))
              (t
               (if (memberp (logic.pnot A1) acc)
                   '(nil . nil)
                 (falsify-taut (cdr as) (cons A1 acc))))))
    (cons t (falsify-formulas acc))))

(defthm consp-of-falsify-taut
  (equal (consp (falsify-taut as acc))
         t)
  :hints(("Goal" :in-theory (enable falsify-taut))))

(verify-guards falsify-taut
               :hints(("Goal" :in-theory (enable logic.fmtype-normalizer-cheap))))

(encapsulate
 ()

 (local
  (defthm lemma
    ;; By looking at the definitions of falsify-taut and tautologyp1, we can see
    ;; that falsify-taut considers itself "successful" exactly when tautologyp1
    ;; rejects these inputs.
    (implies (and (logic.formula-listp as))
             (equal (tautologyp1 as acc)
                    (not (car (falsify-taut as acc)))))
    :hints(("Goal"
            :in-theory (enable tautologyp1 falsify-taut)
            :induct (tautologyp1 as acc)))))

 (defthm forcing-non-tautologies-are-falsifiable
   ;; We can also demonstrate that when tautologyp1 rejects its inputs, then the
   ;; valuation returned by falsify-taut falsifies the disjunction of these
   ;; formulas.  In other words, anything that tautologyp1 rejects is not true
   ;; in all valuations, and hence is not a tautology.
   (implies (and (force (logic.formula-listp as))
                 (force (logic.formula-listp acc))
                 (force (basic-logic.formula-listp acc))
                 (force (not (find-complements acc)))
                 (not (tautologyp1 as acc)))
            (not (truth-value (logic.disjoin-formulas (app as acc))
                              (cdr (falsify-taut as acc)))))
   :hints(("Goal"
           :in-theory (enable falsify-taut
                              slow-truth-value-theory
                              logic.fmtype-normalizer-cheap)
           :induct (falsify-taut as acc)))))



;; We now have a function, tautologyp1, which we can use to determine precisely
;; when (logic.disjoin-formulas (app as acc)) is a tautology, assuming that as and
;; acc are lists of formulas, where acc consists entirely of basic formulas and
;; has no complementary formulas.  This turns out to be sufficient to answer
;; whether any formula F is a tautology, by asking about (logic.disjoin-formulas
;; (list F) nil).  We now "wrap up" this common usage as follows.

(defund tautologyp (x)
  (declare (xargs :guard (logic.formulap x)))
  (tautologyp1 (list x) nil))

(defthm booleanp-of-tautologyp
  (equal (booleanp (tautologyp x))
         t)
  :hints(("Goal" :in-theory (enable tautologyp))))

(defund tautologyp-counterexample (x)
  (declare (xargs :guard (and (logic.formulap x)
                              (not (tautologyp x)))))
  (cdr (falsify-taut (list x) nil)))

(defthm truth-value-when-tautologyp
  (implies (and (force (logic.formulap x))
                (tautologyp x))
           (equal (truth-value x valuation)
                  t))
  :hints(("Goal"
          :in-theory (e/d (tautologyp)
                          (forcing-tautologies-are-true))
          :use (:instance forcing-tautologies-are-true
                          (as (list x))
                          (acc nil)))))

(defthm truth-value-of-counterexample-when-not-tautologyp
  (implies (and (force (logic.formulap x))
                (not (tautologyp x)))
           (not (truth-value x (tautologyp-counterexample x))))
  :hints(("Goal"
          :in-theory (e/d (tautologyp tautologyp-counterexample)
                          (forcing-non-tautologies-are-falsifiable))
          :use (:instance forcing-non-tautologies-are-falsifiable
                          (as (list x))
                          (acc nil)))))



(encapsulate
 ()
 (local (defthm lemma
          (implies (and (logic.formula-listp xs)
                        (truth-value (logic.disjoin-formulas xs)
                                     (cdr (falsify-taut xs nil))))
                   (tautologyp1 xs nil))
          :hints(("Goal"
                  :in-theory (disable forcing-non-tautologies-are-falsifiable)
                  :use ((:instance forcing-non-tautologies-are-falsifiable
                                   (as xs)
                                   (acc nil)))))))

 (defthm tautologyp-when-cannot-be-falsified
   ;; This is Shankar's trick for allowing us to symbolically simplify
   ;; tautologies as they arise in formulas.  (See page 88 of his book,
   ;; Metamathematics, Machines, and Godel's Proof).
   (implies (and (logic.formulap x)
                 (truth-value x (cdr (falsify-taut (list x) nil))))
            (equal (tautologyp x)
                   t))
   :hints(("Goal"
           :in-theory (enable tautologyp)))))

(defthm forcing-tautologyp-of-logic.piff-a-a
  (implies (force (logic.formulap a))
           (equal (tautologyp (logic.piff a a))
                  t))
  :hints(("Goal" :in-theory (enable logic.piff logic.pand))))





;; It is not sufficient to prove that tautologyp1 is sound and complete in the
;; sense we have demonstrated above.  We need to show that we can actually
;; build proofs of every tautology.


(defund tautology-bldr1 (as acc)
  ;; Derive (logic.disjoin-formulas (app as acc)) when (tautologyp1 as acc).
  ;; Note: This is basically like Shankar's function "taut-proof1".
  (declare (xargs :guard (and (logic.formula-listp as)
                              (logic.formula-listp acc)
                              (tautologyp1 as acc))
                  :verify-guards nil
                  :measure (logic.formula-list-size as)))
  ;; We will denote As = [A1 ... An]
  ;; We will write Acc = [B1 ... Bm]
  ;; Goal is to prove [A1 v... v An v B1 v ... v Bm] (fully right associated)
  (if (consp as)
      (let ((A1 (car as)))
        (cond

         ;; As = [(F v G), A2, ..., An]
         ((equal (logic.fmtype A1) 'por*)

          ;; Case 1: {A2...An}U{B1...Bm} is nonempty
          ;;   Recursively build F v (G v (A2 ... An v B1 ... Bm))
          ;;   Associativity yields (F v G) v (A2 ... An v B1 ... Bm)
          (if (or (consp (cdr as))
                  (consp acc))
              (build.associativity (tautology-bldr1 (list* (logic.vlhs A1) (logic.vrhs A1) (cdr as)) acc))

            ;; Case 2: {A2...An}U{B1...Bm} is empty
            ;;   Recursively build F v G
            (tautology-bldr1 (list* (logic.vlhs A1) (logic.vrhs A1) (cdr as)) acc)))

         ;; As = [~(F v G), A2, ..., An]
         ((and (equal (logic.fmtype A1) 'pnot*)
               (equal (logic.fmtype (logic.~arg A1)) 'por*))

          ;; Case 1: {A2...An}U{B1...Bm} is nonempty
          ;;   Recursively build ~F v (A2 ... An v B1 ... Bm)
          ;;   Recursively build ~G v (A2 ... An v B1 ... Bm)
          ;;   Merge Implications yields ~(F v G) v (A2 ... An v B1 ... Bm)
          (if (or (consp (cdr as))
                  (consp acc))
              (build.merge-implications (tautology-bldr1 (cons (logic.pnot (logic.vlhs (logic.~arg A1))) (cdr as)) acc)
                                       (tautology-bldr1 (cons (logic.pnot (logic.vrhs (logic.~arg A1))) (cdr as)) acc))

            ;; Case 2: {A2...An}U{B1...Bm} is empty
            ;;   Recursively build ~F
            ;;   Recursively Build ~G
            ;;   Merge Negatives yields ~(F v G)
            (build.merge-negatives (tautology-bldr1 (cons (logic.pnot (logic.vlhs (logic.~arg A1))) (cdr as)) acc)
                                  (tautology-bldr1 (cons (logic.pnot (logic.vrhs (logic.~arg A1))) (cdr as)) acc))))

         ;; As = [~~B, A2, ..., An]
         ((and (equal (logic.fmtype A1) 'pnot*)
               (equal (logic.fmtype (logic.~arg A1)) 'pnot*))

          ;; Case 1: [A2...An]@[B1...Bm] is nonempty
          ;;   Recursively build B v (A2 ... An v B1 ... Bm)
          ;;   Lhs Insert ~~ yields ~~B v (A2 ... An v B1 ... Bm)
          (if (or (consp (cdr as))
                  (consp acc))
              (build.lhs-insert-neg-neg (tautology-bldr1 (cons (logic.~arg (logic.~arg A1)) (cdr as)) acc))

            ;; Case 2: [A2...An]@[B1...Bm] is empty
            ;;  Recursively build B
            ;;  Then Double Negate yields ~~B
            (build.insert-neg-neg (tautology-bldr1 (cons (logic.~arg (logic.~arg A1)) (cdr as)) acc))))


        ;; As = [~(t1 = t2), A2, ..., An]
        ((equal (logic.fmtype A1) 'pnot*)

         ;; Case 1: t1=t2 is Bi for some i.
         ;;   Propositional Schema:  A1 v Bi
         ;;   Multi Or Expansion:    A1 ... An v B1 ... Bm
         (if (memberp (logic.~arg A1) acc)
             (build.multi-or-expansion (build.propositional-schema (logic.~arg A1)) (app as acc))

           ;; Case 2: t1=t2 is not Bi for any i.
           ;;   Recursively build A2 ... An v A1 v B1 ... Bm
           ;;   Disjoined Subset yields A1 ... An v B1 ... Bm
           (build.disjoined-subset (app (cdr as) (cons a1 acc))
                                  (app as acc)
                                  (tautology-bldr1 (cdr as) (cons A1 acc)))))


        ;; As = [t1=t2, A2, ..., An]
        (t

         ;; Case 1: ~(t1=t2) is Bi for some i.
         ;;   Propositional Schema:  Bi v A1
         ;;   Multi Or Expansion:    A1 ... An v B1 ... Bm
         (if (memberp (logic.pnot A1) acc)
             (build.multi-or-expansion (build.propositional-schema A1) (app as acc))

           ;; Case 2: ~(t1=t2) is not Bi for any i.
           ;;   Recursively build A2...An v A1 v B1 ... Bm
           ;;   Disjoined Subset yields A1...An v B1...Bm
           (build.disjoined-subset (app (cdr as) (cons a1 acc))
                                  (app as acc)
                                  (tautology-bldr1 (cdr as) (cons A1 acc)))))

         ))

    ;; as = [], our guard is violated; we return garbage.
    nil))



;; We now prove that whenever the tautologyp1 function accepts as and acc, the
;; tautology-bldr1 function will actually construct the appropriate proof.
;; This still leaves the question of whether or not tautologyp1 behaves
;; correctly, but establishes that if it does, then tautologyp-bldr will indeed
;; construct a proof of any arbitrary tautology.

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (force (logic.formula-listp as))
                        (force (logic.formula-listp acc))
                        (force (tautologyp1 as acc)))
                   (and (logic.appealp (tautology-bldr1 as acc))
                        (equal (logic.conclusion (tautology-bldr1 as acc))
                               (logic.disjoin-formulas (app as acc)))))
          :hints(("Goal" :in-theory (enable tautology-bldr1 logic.fmtype-normalizer-cheap)))))

 (verify-guards tautology-bldr1
                :hints(("Goal" :in-theory (enable logic.fmtype-normalizer-cheap))))

 (defthm forcing-logic.appealp-of-tautology-bldr1
   (implies (and (force (logic.formula-listp as))
                 (force (logic.formula-listp acc))
                 (force (tautologyp1 as acc)))
            (equal (logic.appealp (tautology-bldr1 as acc))
                   t)))

 (defthm forcing-logic.conclusion-of-tautology-bldr1
   (implies (and (force (logic.formula-listp as))
                 (force (logic.formula-listp acc))
                 (force (tautologyp1 as acc)))
            (equal (logic.conclusion (tautology-bldr1 as acc))
                   (logic.disjoin-formulas (app as acc))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-tautology-bldr1
   (implies (and (force (logic.formula-listp as))
                 (force (logic.formula-listp acc))
                 (force (tautologyp1 as acc))
                 ;; ---
                 (force (logic.formula-list-atblp as atbl))
                 (force (logic.formula-list-atblp acc atbl)))
            (equal (logic.proofp (tautology-bldr1 as acc) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable tautology-bldr1 logic.fmtype-normalizer-cheap)))))



(defund tautology-bldr (x)
  (declare (xargs :guard (and (logic.formulap x)
                              (tautologyp x))
                  :guard-hints (("Goal" :in-theory (enable tautologyp)))))
  (tautology-bldr1 (list x) nil))

(encapsulate
 ()
 (defthm forcing-logic.appealp-of-tautology-bldr
   (implies (and (force (tautologyp x))
                 (force (logic.formulap x)))
            (equal (logic.appealp (tautology-bldr x))
                   t))
   :hints(("Goal" :in-theory (enable tautologyp tautology-bldr))))

 (defthm forcing-logic.conclusion-of-tautology-bldr
   (implies (and (force (tautologyp x))
                 (force (logic.formulap x)))
            (equal (logic.conclusion (tautology-bldr x))
                   x))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable tautologyp tautology-bldr))))

 (defthm forcing-logic.proofp-of-tautology-bldr
   (implies (and (force (tautologyp x))
                 (force (logic.formulap x))
                 ;; ---
                 (force (logic.formula-atblp x atbl)))
            (equal (logic.proofp (tautology-bldr x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable tautologyp tautology-bldr)))))




;; ------------------------------------------------------------------------- ;;
;;                                                                           ;;
;;                                   Part 3                                  ;;
;;                                                                           ;;
;;                         Tautological Consequences                         ;;
;;                                                                           ;;
;; ------------------------------------------------------------------------- ;;

;; We now write a function that checks if some formula B is a tautological
;; consequence of some other formulas, say A1, A2, ..., An.  We also write a
;; function that will build a proof of B given proofs of each Ai.

(defund tautological-consequencep (b as)
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.formula-listp as))))
  (tautologyp (logic.disjoin-formulas (cons b (logic.negate-formulas as)))))

(defthm booleanp-of-tautological-consequencep
  (equal (booleanp (tautological-consequencep b as))
         t)
  :hints(("Goal" :in-theory (enable tautological-consequencep))))

;; BOZO move; rename
(defthm forcing-tautological-consequencep-of-nots
  (implies (and (force (logic.formulap f))
                (force (logic.formulap g))
                (force (equal (logic.fmtype f) 'pnot*))
                (force (equal (logic.fmtype g) 'pnot*)))
           (equal (tautological-consequencep (logic.piff f g)
                                             (list (logic.piff (logic.~arg f) (logic.~arg g))))
                  t))
  :hints(("Goal" :in-theory (enable slow-truth-value-theory
                                    tautological-consequencep))))

;; BOZO move; rename
(defthm forcing-tautological-consequencep-of-ors
  (implies (and (force (logic.formulap f))
                (force (logic.formulap g))
                (force (equal (logic.fmtype f) 'por*))
                (force (equal (logic.fmtype g) 'por*)))
           (equal (tautological-consequencep (logic.piff f g)
                                             (list (logic.piff (logic.vlhs f) (logic.vlhs g))
                                                   (logic.piff (logic.vrhs f) (logic.vrhs g))))
                  t))
  :hints(("Goal" :in-theory (enable slow-truth-value-theory
                                    logic.piff
                                    tautological-consequencep))))



(defund tautological-consequence-bldr (b as)
  (declare (xargs :guard (and (logic.formulap b)
                              (logic.appeal-listp as)
                              (tautological-consequencep b (logic.strip-conclusions as)))
                  :verify-guards nil))
  (build.modus-ponens-list b as
   (tautology-bldr (logic.disjoin-formulas
                    (fast-app (logic.negate-formulas (logic.strip-conclusions as))
                              (list b))))))



;; There is a slight disconnect here; our builder function appends the
;; singleton list [B] to the end of [A1 ... An], whereas our simple testing
;; function conses B onto the front instead.  We to a little work here to show
;; that there is really no difference between these two lists as far as
;; tautologyp is concerned.

(defthm forcing-truth-value-of-logic.disjoin-formulas-of-superset-one
  (implies (and (subsetp x y)
                (truth-value (logic.disjoin-formulas x) valuation)
                (force (logic.formula-listp y)))
           (equal (truth-value (logic.disjoin-formulas y) valuation)
                  t)))

(defthm forcing-truth-value-of-logic.disjoin-formulas-of-superset-two
  (implies (and (truth-value (logic.disjoin-formulas x) valuation)
                (subsetp x y)
                (force (logic.formula-listp y)))
           (equal (truth-value (logic.disjoin-formulas y) valuation)
                  t)))

(defthm forcing-tautologyp-of-logic.disjoin-formulas-of-superset-one
  (implies (and (tautologyp (logic.disjoin-formulas x))
                (subsetp x y)
                (force (consp x))
                (force (logic.formula-listp y)))
           (equal (tautologyp (logic.disjoin-formulas y))
                  t)))

(defthm forcing-tautologyp-of-logic.disjoin-formulas-of-superset-two
  (implies (and (subsetp x y)
                (tautologyp (logic.disjoin-formulas x))
                (force (consp x))
                (force (logic.formula-listp y)))
           (equal (tautologyp (logic.disjoin-formulas y))
                  t)))




;; And finally we can state the usual properties about our tautological
;; consequence builder function.

(verify-guards tautological-consequence-bldr
  :hints(("Goal" :in-theory (enable tautological-consequencep))))

(defthm forcing-logic.appealp-of-tautological-consequence-bldr
  (implies (and (force (logic.formulap b))
                (force (logic.appeal-listp as))
                (force (tautological-consequencep b (logic.strip-conclusions as))))
           (equal (logic.appealp (tautological-consequence-bldr b as))
                  t))
  :hints(("Goal" :in-theory (enable tautological-consequence-bldr tautological-consequencep))))

(defthm forcing-logic.conclusion-of-tautological-consequence-bldr
  (implies (and (force (logic.formulap b))
                (force (logic.appeal-listp as))
                (force (tautological-consequencep b (logic.strip-conclusions as))))
           (equal (logic.conclusion (tautological-consequence-bldr b as))
                  b))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable tautological-consequence-bldr tautological-consequencep))))

(defthm forcing-logic.proofp-of-tautological-consequence-bldr
  (implies (and (force (logic.formulap b))
                (force (logic.appeal-listp as))
                (force (tautological-consequencep b (logic.strip-conclusions as)))
                ;; ---
                (force (logic.formula-atblp b atbl))
                (force (logic.proof-listp as axioms thms atbl)))
           (equal (logic.proofp (tautological-consequence-bldr b as) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable tautological-consequence-bldr tautological-consequencep))))

