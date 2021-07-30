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
(include-book "base-evaluator")
(include-book "substitute-formula")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; The core proof checker
;;
;; Our proof checker, logic.proofp, takes as arguments:
;;
;;   - an "appeal" to check,
;;   - a list of axioms (formulas) which are assumed to be true,
;;   - a list of theorems (formulas) which have been previously proven, and
;;   - an arity table that specifies the valid functions.
;;
;; An appeal is a tree of proof steps.  Each proof step is a tuple of the form
;; (method conclusion [subproofs] [extras]), where:
;;
;;   - method is the name of the rule used to justify this step,
;;   - conclusion is the formula that we're claiming to prove with this step,
;;   - subproofs are a list of appeals that we are building upon, and
;;   - extras hold any additional information we need, e.g., substitution lists
;;     for instantiation appeals.
;;
;; An appeal is "stepwise ok" if, assuming all of its subproofs are actually
;; legitimate proofs, its conclusion would be provable by the specified method.
;; This is a convenient notion, because we can easily write functions to check
;; that a particular kind of proof step is valid in this sense. Our proof
;; checker recursively extends this stepwise check throughout the tree of
;; appeals.

(defund logic.flag-appealp (flag x)
  (declare (xargs :guard (or (equal flag 'proof)
                             (equal flag 'list))))
  (if (equal flag 'proof)
      (and (true-listp x)
           (<= (len x) 4)
           (symbolp (first x))
           (logic.formulap (second x))
           (true-listp (third x))
           (logic.flag-appealp 'list (third x)))
    (if (consp x)
        (and (logic.flag-appealp 'proof (car x))
             (logic.flag-appealp 'list (cdr x)))
      t)))

(definlined logic.appealp (x)
  (declare (xargs :guard t))
  (logic.flag-appealp 'proof x))

(definlined logic.appeal-listp (x)
  (declare (xargs :guard t))
  (logic.flag-appealp 'list x))

(defthmd definition-of-logic.appealp
  (equal (logic.appealp x)
         (and (true-listp x)
              (<= (len x) 4)
              (symbolp (first x))
              (logic.formulap (second x))
              (true-listp (third x))
              (logic.appeal-listp (third x))))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-appealp
                                    logic.appealp
                                    logic.appeal-listp))))

(defthmd definition-of-logic.appeal-listp
  (equal (logic.appeal-listp x)
         (if (consp x)
             (and (logic.appealp (car x))
                  (logic.appeal-listp (cdr x)))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-appealp
                                    logic.appealp
                                    logic.appeal-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.appealp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.appeal-listp))))


(definlined logic.method (x)
  ;; BOZO consider renaming, e.g., logic.appeal->method, etc.
  (declare (xargs :guard (logic.appealp x)
                  :guard-hints(("Goal" :in-theory (enable logic.appealp)))))
  (first x))

(definlined logic.conclusion (x)
  (declare (xargs :guard (logic.appealp x)
                  :guard-hints(("Goal" :in-theory (enable logic.appealp)))))
  (second x))

(definlined logic.subproofs (x)
  (declare (xargs :guard (logic.appealp x)
                  :guard-hints(("Goal" :in-theory (enable logic.appealp)))))
  (third x))

(definlined logic.extras (x)
  (declare (xargs :guard (logic.appealp x)
                  :guard-hints(("Goal" :in-theory (enable logic.appealp)))))
  (fourth x))

(defund logic.appeal (method conclusion subproofs extras)
  (declare (xargs :guard (and (symbolp method)
                              (logic.formulap conclusion)
                              (logic.appeal-listp subproofs)
                              (true-listp subproofs))))
  (if extras
      (list method conclusion subproofs extras)
    (if subproofs
        (list method conclusion subproofs)
      (list method conclusion))))




(defun logic.appeal-induction (flag x)
  ;; This just defines an induction scheme we can use to reason about appeals.
  (declare (xargs :verify-guards nil
                  :measure (two-nats-measure (rank x) (if (equal flag 'list) 0 1))
                  :hints (("Goal" :in-theory (enable logic.subproofs)))))
  (if (equal flag 'proof)
      (logic.appeal-induction 'list (logic.subproofs x))
    (if (consp x)
        (list (logic.appeal-induction 'proof (car x))
              (logic.appeal-induction 'list (cdr x)))
      nil)))

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'proof)
              (booleanp (logic.appealp x))
            (booleanp (logic.appeal-listp x)))
          :rule-classes nil
          :hints(("Goal"
                  :induct (logic.appeal-induction flag x)
                  :in-theory (enable definition-of-logic.appealp
                                     definition-of-logic.appeal-listp
                                     logic.subproofs)))))

 (defthm booleanp-of-logic.appealp
   (equal (booleanp (logic.appealp x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'proof))))))

 (defthm booleanp-of-logic.appeal-listp
   (equal (booleanp (logic.appeal-listp x))
          t)
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))

(defthm logic.appeal-listp-when-not-consp
  (implies (not (consp x))
           (equal (logic.appeal-listp x)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.appeal-listp))))

(defthm logic.appeal-listp-of-cons
  (equal (logic.appeal-listp (cons a x))
         (and (logic.appealp a)
              (logic.appeal-listp x)))
  :hints(("Goal" :in-theory (enable definition-of-logic.appeal-listp))))

(deflist logic.appeal-listp (x)
  (logic.appealp x)
  :elementp-of-nil nil
  :already-definedp t)

(defthm logic.appealp-of-nth-when-logic.appeal-listp
  ;; BOZO consider adding something like this rule to deflist.
  (implies (logic.appeal-listp x)
           (equal (logic.appealp (nth n x))
                  (< n (len x)))))

(defthm logic.appealp-of-second-when-logic.appeal-listp
  ;; BOZO consider adding something like this rule to deflist
  (implies (logic.appeal-listp x)
           (equal (logic.appealp (second x))
                  (consp (cdr x)))))

(defthm forcing-logic.appeal-listp-of-firstn
  (implies (force (logic.appeal-listp x))
           (equal (logic.appeal-listp (firstn n x))
                  t)))

(defthm forcing-logic.appeal-listp-of-restn
  (implies (force (logic.appeal-listp x))
           (equal (logic.appeal-listp (restn n x))
                  t)))




(defthm logic.method-of-logic.appeal
  (equal (logic.method (logic.appeal method conclusion subproofs extras))
         method)
  :hints(("Goal" :in-theory (enable logic.appeal logic.method))))

(defthm logic.conclusion-of-logic.appeal
  (equal (logic.conclusion (logic.appeal method conclusion subproofs extras))
         conclusion)
  :hints(("Goal" :in-theory (enable logic.appeal logic.conclusion))))

(defthm logic.subproofs-of-logic.appeal
  (equal (logic.subproofs (logic.appeal method conclusion subproofs extras))
         subproofs)
  :hints(("Goal" :in-theory (enable logic.appeal logic.subproofs))))

(defthm logic.extras-of-logic.appeal
  (equal (logic.extras (logic.appeal method conclusion subproofs extras))
         extras)
  :hints(("Goal" :in-theory (enable logic.appeal logic.extras))))

(defthm logic.appeal-under-iff
  (iff (logic.appeal method conclusion subproofs extras)
       t)
  :hints(("Goal" :in-theory (enable logic.appeal))))

(defthm forcing-logic.appealp-of-logic.appeal
  (implies (force (and (symbolp method)
                       (logic.formulap conclusion)
                       (logic.appeal-listp subproofs)
                       (true-listp subproofs)))
           (equal (logic.appealp (logic.appeal method conclusion subproofs extras))
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.appealp logic.appeal))))



(defthm forcing-symbolp-of-logic.method
  (implies (force (logic.appealp x))
           (equal (symbolp (logic.method x))
                  t))
  :hints(("Goal" :in-theory (enable logic.method definition-of-logic.appealp))))

(defthm forcing-logic.formulap-of-logic.conclusion
  (implies (force (logic.appealp x))
           (equal (logic.formulap (logic.conclusion x))
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable logic.conclusion definition-of-logic.appealp))))

(defthm forcing-true-listp-of-logic.subproofs
  (implies (force (logic.appealp x))
           (equal (true-listp (logic.subproofs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.subproofs definition-of-logic.appealp))))

(defthm forcing-logic.appeal-listp-of-logic.subproofs
  (implies (force (logic.appealp x))
           (equal (logic.appeal-listp (logic.subproofs x))
                  t))
  :hints(("Goal" :in-theory (enable logic.subproofs definition-of-logic.appealp))))

(defthm rank-of-logic.subproofs
  (implies (logic.appealp x)
           (equal (< (rank (logic.subproofs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.subproofs definition-of-logic.appealp))))

(defthm rank-of-logic.subproofs-weak
  (equal (< (rank x) (rank (logic.subproofs x)))
         nil)
  :hints(("Goal" :in-theory (enable logic.subproofs))))

(defthm rank-of-logic.subproofs-strong-via-consp
  ;; This rule lets us admit functions that recur on subproofs without having
  ;; to call logic.appealp on every recursive invocation; we just
  ;; need to ensure that the object is a consp.
  ;;
  ;; BOZO.  We can often avoid this by just using two-nats-measure.  Maybe we
  ;; don't really want this rule around?
  (implies (consp x)
           (equal (< (rank (logic.subproofs x)) (rank x))
                  t))
  :hints(("Goal" :in-theory (enable logic.subproofs))))

(defthm rank-of-first-of-logic.subproofs
  (implies (logic.appealp x)
           (equal (< (rank (first (logic.subproofs x))) (rank x))
                  t))
  :hints(("Goal"
          :in-theory (disable rank-of-logic.subproofs)
          :use ((:instance rank-of-logic.subproofs)))))

(defthm rank-of-second-of-logic.subproofs
  (implies (logic.appealp x)
           (equal (< (rank (second (logic.subproofs x))) (rank x))
                  t))
  :hints(("Goal"
          :in-theory (disable rank-of-logic.subproofs)
          :use ((:instance rank-of-logic.subproofs)))))




(defprojection :list (logic.strip-conclusions x)
               :element (logic.conclusion x)
               :guard (logic.appeal-listp x)
               :nil-preservingp t)

(defthm second-of-logic.strip-conclusions
  ;; BOZO consider adding this to deflist
  (equal (second (logic.strip-conclusions x))
         (logic.conclusion (second x))))

(defthm forcing-logic.formula-listp-of-logic.strip-conclusions
  (implies (force (logic.appeal-listp x))
           (equal (logic.formula-listp (logic.strip-conclusions x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp
  (implies (logic.all-disjunctionsp (logic.strip-conclusions x))
           (equal (logic.fmtype (logic.conclusion (nth n x)))
                  (if (< (nfix n) (len x))
                      'por*
                    nil)))
  :hints(("Goal" :use ((:instance logic.fmtype-of-nth-when-logic.all-disjunctionsp
                                  (x (logic.strip-conclusions x)))))))

(defthm logic.fmtype-of-logic.conclusion-of-nth-when-logic.all-atomicp
  (implies (logic.all-atomicp (logic.strip-conclusions x))
           (equal (logic.fmtype (logic.conclusion (nth n x)))
                  (if (< (nfix n) (len x))
                      'pequal*
                    nil)))
  :hints(("Goal" :use ((:instance logic.fmtype-of-nth-when-logic.all-atomicp
                                  (x (logic.strip-conclusions x)))))))

(defthm logic.vlhs-of-logic.conclusion-of-car-when-all-equalp
  (implies (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
           (equal (logic.vlhs (logic.conclusion (car x)))
                  (if (consp x)
                      p
                    nil))))

(defthm logic.vlhs-of-logic.conclusion-of-nth-when-all-equalp-of-logic.vlhses
  (implies (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
           (equal (logic.vlhs (logic.conclusion (nth n x)))
                  (if (< (nfix n) (len x))
                      p
                    nil)))
  :hints(("Goal"
          :in-theory (enable nth)
          :induct (nth n x))))

(defthm logic.fmtype-of-logic.vrhs-of-logic.conclusion-of-nth-when-logic.all-disjunctionsp-of-logic.all-atomicp
  (implies (and (logic.all-disjunctionsp (logic.strip-conclusions x))
                (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))
           (equal (logic.fmtype (logic.vrhs (logic.conclusion (nth n x))))
                  (if (< (nfix n) (len x))
                      'pequal*
                    nil)))
  :hints(("Goal" :use ((:instance logic.fmtype-of-nth-when-logic.all-atomicp
                                  (x (logic.vrhses (logic.strip-conclusions x))))))))

(defthm logic.formula-atblp-of-logic.conclusion-of-car
  (implies (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
           (equal (logic.formula-atblp (logic.conclusion (car x)) atbl)
                  (consp x))))

(defthm logic.formula-atblp-of-logic.conclusion-of-second
  (implies (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
           (equal (logic.formula-atblp (logic.conclusion (second x)) atbl)
                  (consp (cdr x)))))

(defthm logic.formula-atblp-of-logic.conclusion-of-third
  (implies (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
           (equal (logic.formula-atblp (logic.conclusion (third x)) atbl)
                  (consp (cdr (cdr x))))))

(defthmd logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1
  (implies (equal (len x) 1)
           (equal (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
                  (logic.formula-atblp (logic.conclusion (car x)) atbl))))

(defthmd logic.formula-list-atblp-of-logic.strip-conclusions-when-len-2
  (implies (equal (len x) 2)
           (equal (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
                  (and (logic.formula-atblp (logic.conclusion (first x)) atbl)
                       (logic.formula-atblp (logic.conclusion (second x)) atbl)))))



;; The Individual Proof-Step Checkers

(defund logic.axiom-okp (x axioms atbl)
  ;; We ensure the conclusion of x is among axioms.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'axiom)
         (equal subproofs nil)
         (equal extras nil)
         (memberp conclusion axioms)
         (logic.formula-atblp conclusion atbl))))

(defthm booleanp-of-logic.axiom-okp
  (equal (booleanp (logic.axiom-okp x axioms atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.axiom-okp
  (implies (logic.axiom-okp x axioms atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))



(defund logic.theorem-okp (x thms atbl)
  ;; We ensure the conclusion of x is among thms.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'theorem)
         (equal subproofs nil)
         (equal extras nil)
         (memberp conclusion thms)
         (logic.formula-atblp conclusion atbl))))

(defthm booleanp-of-logic.theorem-okp
  (equal (booleanp (logic.theorem-okp x axioms atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.theorem-okp
  (implies (logic.theorem-okp x theorems atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))



(defund logic.propositional-schema-okp (x atbl)
  ;; Propositional axiom schema: ~A v A
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'propositional-schema)
         (equal subproofs nil)
         (equal extras nil)
         (equal (logic.fmtype conclusion) 'por*)
         (let ((not-a (logic.vlhs conclusion))
               (a     (logic.vrhs conclusion)))
           (and (equal (logic.fmtype not-a) 'pnot*)
                (equal (logic.~arg not-a) a)
                (logic.formula-atblp a atbl))))))

(defthm booleanp-of-logic.propositional-schema-okp
  (equal (booleanp (logic.propositional-schema-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (logic.propositional-schema-okp)
                                 ((:executable-counterpart ACL2::force))))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.propositional-schema-okp
  (implies (logic.propositional-schema-okp x atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.propositional-schema-okp backtracking-logic.formula-atblp-rules)
                                 (forcing-logic.formula-atblp-rules)))))




(defund logic.check-functional-axiom (x ti si)
  ;; The functional equality axiom schema is:
  ;;
  ;; (t1 = s1) -> ((t2 = s2) -> ... -> ((tn = sn)
  ;;   -> (f t1 t2 ... tn) = (f s1 s2 ... sn) ... ))
  ;;
  ;; In other words, it should look like this:
  ;;
  ;; (por* (pnot* (pequal* t1 s1)
  ;;       (por* (pnot* (pequal* t2 s2))
  ;;             ...
  ;;             (por* (pnot* (pequal* tn sn))
  ;;                   (pequal* (f t1 t2 ... tn)
  ;;                            (f s1 s2 ... sn))) ...))
  ;;
  ;; We walk through the formula and accumulate the t's and s's we have seen on
  ;; our way down, until we reach the pequal*.  Then, it is easy to see if we
  ;; have (f t1 ... tn) = (f s1 ... sn) at the bottom.
  (declare (xargs :guard (and (logic.formulap x)
                              (logic.term-listp ti)
                              (logic.term-listp si))))
  (if (equal (logic.fmtype x) 'pequal*)
      ;; Reached the end, match (f t1 ... tn) = (f s1 ... sn)
      (and (logic.functionp (logic.=lhs x))
           (logic.functionp (logic.=rhs x))
           (equal (logic.function-name (logic.=lhs x)) (logic.function-name (logic.=rhs x)))
           (equal (logic.function-args (logic.=lhs x)) (rev ti))
           (equal (logic.function-args (logic.=rhs x)) (rev si)))
    ;; Still traversing, match ti != si v [...]
    (and (equal (logic.fmtype x) 'por*)
         (equal (logic.fmtype (logic.vlhs x)) 'pnot*)
         (equal (logic.fmtype (logic.~arg (logic.vlhs x))) 'pequal*)
         (logic.check-functional-axiom (logic.vrhs x)
                                       (cons (logic.=lhs (logic.~arg (logic.vlhs x))) ti)
                                       (cons (logic.=rhs (logic.~arg (logic.vlhs x))) si)))))

(defund logic.functional-equality-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'functional-equality)
         (equal subproofs nil)
         (equal extras nil)
         (logic.check-functional-axiom conclusion nil nil)
         (logic.formula-atblp conclusion atbl))))

(defthm booleanp-of-logic.check-functional-axiom
  (equal (booleanp (logic.check-functional-axiom x ti si))
         t)
  :hints(("Goal" :in-theory (enable logic.check-functional-axiom))))

(defthm booleanp-of-logic.functional-equality-okp
  (equal (booleanp (logic.functional-equality-okp x atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.functional-equality-okp))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.functional-equality-okp
  (implies (logic.functional-equality-okp x atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.functional-equality-okp))))




(defund logic.expansion-okp (x atbl)
  ;; Expansion: Derive A v B from B
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'expansion)
         (equal extras nil)
         (tuplep 1 subproofs)
         (let ((b (logic.conclusion (first subproofs))))
           (and (equal (logic.fmtype conclusion) 'por*)
                (equal (logic.vrhs conclusion) b)
                (logic.formula-atblp (logic.vlhs conclusion) atbl))))))

(defthm booleanp-of-logic.expansion-okp
  (equal (booleanp (logic.expansion-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (logic.expansion-okp)
                                 (forcing-true-listp-of-logic.subproofs
                                  forcing-logic.formula-atblp-rules)))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.expansion-okp
  (implies (and (logic.expansion-okp x atbl)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.expansion-okp
                                  backtracking-logic.formula-atblp-rules
                                  logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))




(defund logic.contraction-okp (x)
  ;; Contraction: Derive A from A v A
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'contraction)
         (equal extras nil)
         (tuplep 1 subproofs)
         (let ((or-a-a (logic.conclusion (first subproofs))))
           (and (equal (logic.fmtype or-a-a) 'por*)
                (equal (logic.vlhs or-a-a) conclusion)
                (equal (logic.vrhs or-a-a) conclusion))))))

(defthm booleanp-of-logic.contraction-okp
  (equal (booleanp (logic.contraction-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (logic.contraction-okp)
                                 (forcing-true-listp-of-logic.subproofs)))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.contraction-okp
  (implies (and (logic.contraction-okp x)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.contraction-okp
                                  backtracking-logic.formula-atblp-rules
                                  logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))




(defund logic.associativity-okp (x)
  ;; Associativity: Derive (A v B) v C from A v (B v C)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'associativity)
         (equal extras nil)
         (tuplep 1 subproofs)
         (let ((sub-or-a-or-b-c (logic.conclusion (first subproofs))))
           (and (equal (logic.fmtype conclusion) 'por*)
                (equal (logic.fmtype sub-or-a-or-b-c) 'por*)
                (let ((conc-or-a-b (logic.vlhs conclusion))
                      (conc-c      (logic.vrhs conclusion))
                      (sub-a       (logic.vlhs sub-or-a-or-b-c))
                      (sub-or-b-c  (logic.vrhs sub-or-a-or-b-c)))
                  (and (equal (logic.fmtype conc-or-a-b) 'por*)
                       (equal (logic.fmtype sub-or-b-c) 'por*)
                       (let ((conc-a (logic.vlhs conc-or-a-b))
                             (conc-b (logic.vrhs conc-or-a-b))
                             (sub-b  (logic.vlhs sub-or-b-c))
                             (sub-c  (logic.vrhs sub-or-b-c)))
                         (and (equal conc-a sub-a)
                              (equal conc-b sub-b)
                              (equal conc-c sub-c))))))))))

(defthm booleanp-of-logic.associativity-okp
  (equal (booleanp (logic.associativity-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (logic.associativity-okp)
                                 (forcing-true-listp-of-logic.subproofs)))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.associativity-okp
  (implies (and (logic.associativity-okp x)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.associativity-okp
                                  backtracking-logic.formula-atblp-rules
                                  logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))




(defund logic.cut-okp (x)
  ;; Cut: Derive B v C from A v B and ~A v C
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'cut)
         (equal extras nil)
         (tuplep 2 subproofs)
         (let ((or-a-b     (logic.conclusion (first subproofs)))
               (or-not-a-c (logic.conclusion (second subproofs))))
             (and (equal (logic.fmtype or-a-b) 'por*)
                  (equal (logic.fmtype or-not-a-c) 'por*)
                  (let ((a     (logic.vlhs or-a-b))
                        (b     (logic.vrhs or-a-b))
                        (not-a (logic.vlhs or-not-a-c))
                        (c     (logic.vrhs or-not-a-c)))
                    (and (equal (logic.fmtype not-a) 'pnot*)
                         (equal (logic.~arg not-a) a)
                         (equal (logic.fmtype conclusion) 'por*)
                         (equal (logic.vlhs conclusion) b)
                         (equal (logic.vrhs conclusion) c))))))))

(defthm booleanp-of-logic.cut-okp
  (equal (booleanp (logic.cut-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (logic.cut-okp)
                                 (forcing-true-listp-of-logic.subproofs)))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.cut-okp
  (implies (and (logic.cut-okp x)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.cut-okp
                                  backtracking-logic.formula-atblp-rules
                                  logic.formula-list-atblp-of-logic.strip-conclusions-when-len-2)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))



(defund logic.instantiation-okp (x atbl)
  ;; Instantiation: Derive A/sigma from A
  ;;
  ;; Why don't we take an arity table?  The conclusion gets arity checked for
  ;; us by proofp, and if a malformed term is being used it will show up in the
  ;; conclusion.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))  ;; We put the sigma into "extras"
    (and (equal method 'instantiation)
         (logic.sigmap extras)
         (tuplep 1 subproofs)
         (equal (logic.substitute-formula (logic.conclusion (first subproofs)) extras) conclusion)
         (logic.formula-atblp conclusion atbl))))

(defthm booleanp-of-logic.instantiation-okp
  (equal (booleanp (logic.instantiation-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (logic.instantiation-okp)
                                 (forcing-true-listp-of-logic.subproofs)))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.instantiation-okp
  (implies (and (logic.instantiation-okp x atbl)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.instantiation-okp
                                  backtracking-logic.formula-atblp-rules
                                  logic.formula-list-atblp-of-logic.strip-conclusions-when-len-1)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))




(defund logic.beta-reduction-okp (x atbl)
  ;; Beta Reduction (Schema): ((lambda (x1 ... xn) B) t1 ... tn) = B/[x1 <- t1, ..., xn <- tn]
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'beta-reduction)
         (equal subproofs nil)
         (equal extras nil)
         (logic.formula-atblp conclusion atbl)
         (equal (logic.fmtype conclusion) 'pequal*)
         (let ((lhs (logic.=lhs conclusion))
               (rhs (logic.=rhs conclusion)))
           (and (logic.lambdap lhs)
                (let ((formals (logic.lambda-formals lhs))
                      (body    (logic.lambda-body lhs))
                      (actuals (logic.lambda-actuals lhs)))
                  (equal (logic.substitute body (pair-lists formals actuals)) rhs)))))))

(defthm booleanp-of-logic.beta-reduction-okp
  (equal (booleanp (logic.beta-reduction-okp x atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.beta-reduction-okp))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.beta-reduction-okp
  (implies (logic.beta-reduction-okp x atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.beta-reduction-okp))))




(defund logic.base-eval-okp (x atbl)
  ;; Base evaluation: Derive (f c1 ... cn) = result, where f is one of the base
  ;; functions such as if, equal, consp, etc., c1..cn are constants, and result
  ;; is the "correct" value for f applied to these constants.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'base-eval)
         (equal subproofs nil)
         (equal extras nil)
         (equal (logic.fmtype conclusion) 'pequal*)
         (let ((lhs (logic.=lhs conclusion))
               (rhs (logic.=rhs conclusion)))
           (and (logic.base-evaluablep lhs)
                (equal (logic.base-evaluator lhs) rhs)
                (logic.term-atblp lhs atbl))))))

(defthm booleanp-of-logic.base-eval-okp
  (equal (booleanp (logic.base-eval-okp x atbl))
         t)
  :hints(("Goal" :in-theory (e/d (logic.base-eval-okp)
                                 ((:executable-counterpart ACL2::force))))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.base-eval-okp
  (implies (logic.base-eval-okp x atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.base-eval-okp
                                  backtracking-logic.formula-atblp-rules)
                                 (forcing-logic.formula-atblp-rules
                                  forcing-true-listp-of-logic.subproofs
                                  )))))





;; The Induction Rule.
;;
;; Derive F from:
;;
;;   - A term, m, called the measure,
;;
;;   - A set of formulas, {q1, ..., qk}, and
;;
;;   - For each formula qi, a set of sigmas
;;       Sigma-i = { sigma_<i,1>, ..., sigma_<i,hi> }, and
;;
;;   - Proofs of each of the following formulas:
;;
;;     * Basis Step:       F v q1 v ... v qk
;;
;;     * Inductive Steps:  For each 1 <= i <= k,
;;                             F v ~qi v ~F/sigma_<i,1> v ... v ~F/sigma_<i,hi>
;;
;;     * Ordinal Step:     (ordp m) = t
;;
;;     * Measure Steps:    For each 1 <= i <= k and 1 <= j <= hi,
;;                             ~qi v (ord< m/sigma_<i,j> m) = t

(definlined logic.make-basis-step (f qs)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.formula-listp qs))))
  (logic.disjoin-formulas (cons f qs)))

(definlined logic.make-induction-step (f q-i sigmas-i)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.formulap q-i)
                              (logic.sigma-listp sigmas-i))))
  (logic.disjoin-formulas
   (cons f (cons (logic.pnot q-i) (logic.substitute-each-sigma-into-formula (logic.pnot f) sigmas-i)))))

(defund logic.make-induction-steps (f qs all-sigmas)
  (declare (xargs :guard (and (logic.formulap f)
                              (logic.formula-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas)))))
  (if (consp qs)
      (cons (logic.make-induction-step f (car qs) (car all-sigmas))
            (logic.make-induction-steps f (cdr qs) (cdr all-sigmas)))
    nil))

(definlined logic.make-ordinal-step (m)
  (declare (xargs :guard (logic.termp m)))
  (logic.pequal (logic.function 'ordp (list m)) ''t))

(definlined logic.make-measure-step (m q-i sigma-i-j)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.formulap q-i)
                              (logic.sigmap sigma-i-j))))
  (logic.por (logic.pnot q-i)
             (logic.pequal (logic.function 'ord< (list (logic.substitute m sigma-i-j) m)) ''t)))

(defund logic.make-measure-steps (m q-i sigmas-i)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.formulap q-i)
                              (logic.sigma-listp sigmas-i))))
  (if (consp sigmas-i)
      (cons (logic.make-measure-step m q-i (car sigmas-i))
            (logic.make-measure-steps m q-i (cdr sigmas-i)))
    nil))

(defund logic.make-all-measure-steps (m qs all-sigmas)
  (declare (xargs :guard (and (logic.termp m)
                              (logic.formula-listp qs)
                              (logic.sigma-list-listp all-sigmas)
                              (equal (len qs) (len all-sigmas)))))
  (if (consp all-sigmas)
      (app (logic.make-measure-steps m (car qs) (car all-sigmas))
           (logic.make-all-measure-steps m (cdr qs) (cdr all-sigmas)))
    nil))

(defund logic.induction-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'induction)
         (tuplep 3 extras)
         (let ((m          (first extras))
               (qs         (second extras))
               (all-sigmas (third extras))
               (subconcs   (logic.strip-conclusions subproofs)))
           (and (logic.termp m)
                (logic.formula-listp qs)
                (logic.sigma-list-listp all-sigmas)
                (equal (len qs) (len all-sigmas))
                (memberp (logic.make-basis-step conclusion qs) subconcs)
                (subsetp (logic.make-induction-steps conclusion qs all-sigmas) subconcs)
                (memberp (logic.make-ordinal-step m) subconcs)
                (subsetp (logic.make-all-measure-steps m qs all-sigmas) subconcs))))))

(defthm booleanp-of-logic.induction-okp
  (equal (booleanp (logic.induction-okp x))
         t)
  :hints(("Goal" :in-theory (enable logic.induction-okp))))

(encapsulate
 ()
 (defthmd lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp
   (implies (logic.formula-atblp (logic.make-basis-step f qs) atbl)
            (equal (logic.formula-atblp f atbl)
                   t))
   :hints(("Goal" :in-theory (enable logic.make-basis-step))))

 (defthm logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp
   (implies (and (logic.induction-okp x)
                 (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
            (equal (logic.formula-atblp (logic.conclusion x) atbl)
                   t))
   :hints(("Goal"
           :in-theory (e/d (logic.induction-okp
                            lemma-for-logic.formula-atblp-of-logic.conclusion-when-logic.induction-okp)
                           (logic.formula-atblp-when-memberp-of-logic.formula-list-atblp
                            logic.formula-atblp-when-memberp-of-logic.formula-list-atblp-alt))
           :use ((:instance logic.formula-atblp-when-memberp-of-logic.formula-list-atblp
                            (a (logic.make-basis-step (logic.conclusion x) (second (logic.extras x))))
                            (x (logic.strip-conclusions (logic.subproofs x)))))))))


;; BOZO reorder this stuff, it should be up near the definitions instead of after induction-okp.

(defthm forcing-logic.formulap-of-logic.make-basis-step
  (implies (force (and (logic.formulap f)
                       (logic.formula-listp qs)))
           (equal (logic.formulap (logic.make-basis-step f qs))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-basis-step))))

(defthm forcing-logic.formula-atblp-of-logic.make-basis-step
  (implies (force (and (logic.formula-atblp f atbl)
                       (logic.formula-list-atblp qs atbl)))
           (equal (logic.formula-atblp (logic.make-basis-step f qs) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-basis-step))))

(defthm forcing-logic.formulap-of-logic.make-induction-step
  (implies (force (and (logic.formulap f)
                       (logic.formulap q-i)
                       (logic.sigma-listp sigmas-i)))
           (equal (logic.formulap (logic.make-induction-step f q-i sigmas-i))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-induction-step))))

(defthm forcing-logic.formula-atblp-of-logic.make-induction-step
  (implies (force (and (logic.formula-atblp f atbl)
                       (logic.formula-atblp q-i atbl)
                       (logic.sigma-list-atblp sigmas-i atbl)))
           (equal (logic.formula-atblp (logic.make-induction-step f q-i sigmas-i) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-induction-step))))

(defthm true-listp-of-logic.make-induction-steps
  (equal (true-listp (logic.make-induction-steps f qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable logic.make-induction-steps))))

(defthm len-of-logic.make-induction-steps
  (equal (len (logic.make-induction-steps f qs all-sigmas))
         (len qs))
  :hints(("Goal" :in-theory (enable logic.make-induction-steps))))

(defthm forcing-logic.formula-listp-of-logic.make-induction-steps
  (implies (force (and (logic.formulap f)
                       (logic.formula-listp qs)
                       (logic.sigma-list-listp all-sigmas)
                       (equal (len qs) (len all-sigmas))))
           (equal (logic.formula-listp (logic.make-induction-steps f qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-induction-steps))))

(defthm forcing-logic.formula-list-atblp-of-logic.make-induction-steps
  (implies (force (and (logic.formula-atblp f atbl)
                       (logic.formula-list-atblp qs atbl)
                       (logic.sigma-list-list-atblp all-sigmas atbl)))
           (equal (logic.formula-list-atblp (logic.make-induction-steps f qs all-sigmas) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-induction-steps))))

(defthm forcing-logic.formulap-of-logic.make-ordinal-step
  (implies (force (logic.termp m))
           (equal (logic.formulap (logic.make-ordinal-step m))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-ordinal-step))))

(defthm forcing-logic.formula-atblp-of-logic.make-ordinal-step
  (implies (force (and (logic.term-atblp m atbl)
                       (equal (cdr (lookup 'ordp atbl)) 1)))
           (equal (logic.formula-atblp (logic.make-ordinal-step m) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-ordinal-step))))


(defthm forcing-logic.formulap-of-logic.make-measure-step
  (implies (force (and (logic.termp m)
                       (logic.formulap q-i)
                       (logic.sigmap sigma-i-j)))
           (equal (logic.formulap (logic.make-measure-step m q-i sigma-i-j))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-measure-step))))

(defthm forcing-logic.formula-atblp-of-logic.make-measure-step
  (implies (force (and (logic.term-atblp m atbl)
                       (logic.formula-atblp q-i atbl)
                       (logic.sigma-atblp sigma-i-j atbl)
                       (equal (cdr (lookup 'ord< atbl)) 2)))
           (equal (logic.formula-atblp (logic.make-measure-step m q-i sigma-i-j) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-measure-step))))


(defthm forcing-logic.formula-listp-of-logic.make-measure-steps
  (implies (force (and (logic.termp m)
                       (logic.formulap q-i)
                       (logic.sigma-listp sigmas-i)))
           (equal (logic.formula-listp (logic.make-measure-steps m q-i sigmas-i))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-measure-steps))))

(defthm forcing-logic.formula-list-atblp-of-logic.make-measure-steps
  (implies (force (and (logic.term-atblp m atbl)
                       (logic.formula-atblp q-i atbl)
                       (logic.sigma-list-atblp sigmas-i atbl)
                       (equal (cdr (lookup 'ord< atbl)) 2)))
           (equal (logic.formula-list-atblp (logic.make-measure-steps m q-i sigmas-i) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-measure-steps))))


(defthm true-listp-of-logic.make-all-measure-steps
  (equal (true-listp (logic.make-all-measure-steps m qs all-sigmas))
         t)
  :hints(("Goal" :in-theory (enable logic.make-all-measure-steps))))

(defthm forcing-logic.formula-listp-of-logic.make-all-measure-steps
  (implies (force (and (logic.termp m)
                       (logic.formula-listp qs)
                       (logic.sigma-list-listp all-sigmas)
                       (equal (len qs) (len all-sigmas))))
           (equal (logic.formula-listp (logic.make-all-measure-steps m qs all-sigmas))
                  t))
  :hints(("Goal" :in-theory (enable logic.make-all-measure-steps))))

(defthm forcing-logic.formula-list-atblp-of-logic.make-all-measure-steps
  (implies (force (and (logic.term-atblp m atbl)
                       (logic.formula-list-atblp qs atbl)
                       (logic.sigma-list-list-atblp all-sigmas atbl)
                       (equal (cdr (lookup 'ord< atbl)) 2)
                       (equal (len qs) (len all-sigmas))))
           (equal (logic.formula-list-atblp (logic.make-all-measure-steps m qs all-sigmas) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.make-all-measure-steps))))




(defund logic.skip-okp (x atbl)
  ;; BOZO THIS IS UNSOUND!!!
  ;; This needs to be removed eventually, but for now it's damn convenient.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'skip)
         (not subproofs)
         (not extras)
         (logic.formula-atblp conclusion atbl))))

(defthm booleanp-of-logic.skip-okp
  (equal (booleanp (logic.skip-okp x atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.skip-okp))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.skip-okp
  (implies (logic.skip-okp x atbl)
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.skip-okp))))




(defund logic.appeal-step-okp (x axioms thms atbl)
  ;; We check to see if an appeal step is ok using the basic proof methods.
  ;; This is our step function and doesn't do anything recursive.  Sometimes I
  ;; think of this as a virtual method call or a higher order function lookup
  ;; ni a table.  But in our first order system, we have to make an explicit
  ;; case statement.
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :export (let ((how (logic.method x)))
                            (cond ((equal how 'axiom)                (logic.axiom-okp x axioms atbl))
                                  ((equal how 'theorem)              (logic.theorem-okp x thms atbl))
                                  ((equal how 'propositional-schema) (logic.propositional-schema-okp x atbl))
                                  ((equal how 'functional-equality)  (logic.functional-equality-okp x atbl))
                                  ((equal how 'beta-reduction)       (logic.beta-reduction-okp x atbl))
                                  ((equal how 'expansion)            (logic.expansion-okp x atbl))
                                  ((equal how 'contraction)          (logic.contraction-okp x))
                                  ((equal how 'associativity)        (logic.associativity-okp x))
                                  ((equal how 'cut)                  (logic.cut-okp x))
                                  ((equal how 'instantiation)        (logic.instantiation-okp x atbl))
                                  ((equal how 'induction)            (logic.induction-okp x))
                                  ((equal how 'base-eval)            (logic.base-eval-okp x atbl))
                                  ;; We don't provide :skip for Milawa itself
                                  (t nil)))
                  ))
  (let ((how (logic.method x)))
    (cond ((equal how 'axiom)                (logic.axiom-okp x axioms atbl))
          ((equal how 'theorem)              (logic.theorem-okp x thms atbl))
          ((equal how 'propositional-schema) (logic.propositional-schema-okp x atbl))
          ((equal how 'functional-equality)  (logic.functional-equality-okp x atbl))
          ((equal how 'beta-reduction)       (logic.beta-reduction-okp x atbl))
          ((equal how 'expansion)            (logic.expansion-okp x atbl))
          ((equal how 'contraction)          (logic.contraction-okp x))
          ((equal how 'associativity)        (logic.associativity-okp x))
          ((equal how 'cut)                  (logic.cut-okp x))
          ((equal how 'instantiation)        (logic.instantiation-okp x atbl))
          ((equal how 'induction)            (logic.induction-okp x))
          ((equal how 'base-eval)            (logic.base-eval-okp x atbl))
          ;; BOZO eventually remove skip from even the ACL2 model
          ((equal how 'skip)                 (logic.skip-okp x atbl))
          (t nil))))

(defthm booleanp-of-logic.appeal-step-okp
  (equal (booleanp (logic.appeal-step-okp x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))

(defthm logic.appeal-step-okp-when-not-consp
  (implies (not (consp x))
           (equal (logic.appeal-step-okp x axioms thms atbl)
                  nil))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp logic.method))))

(defthm logic.formula-atblp-of-logic.conclusion-when-logic.appeal-step-okp
  (implies (and (logic.appeal-step-okp x axioms thms atbl)
                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl))
           (equal (logic.formula-atblp (logic.conclusion x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.appeal-step-okp))))




(defund logic.flag-proofp (flag x axioms thms atbl)
  ;; We check that all of our conclusions throughout the proof are valid with
  ;; respect to the arity table, and that every step throughout the proof is
  ;; stepwise ok.
  (declare (xargs :guard (and (if (equal flag 'proof)
                                  (logic.appealp x)
                                (and (equal flag 'list)
                                     (logic.appeal-listp x)))
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :measure (two-nats-measure (rank x) (if (equal flag 'proof) 1 0))))
  (if (equal flag 'proof)
      (and (logic.appeal-step-okp x axioms thms atbl)
           (logic.flag-proofp 'list (logic.subproofs x) axioms thms atbl))
    (if (consp x)
        (and (logic.flag-proofp 'proof (car x) axioms thms atbl)
             (logic.flag-proofp 'list (cdr x) axioms thms atbl))
      t)))

(definlined logic.proofp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (logic.flag-proofp 'proof x axioms thms atbl))

(definlined logic.proof-listp (x axioms thms atbl)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.formula-listp axioms)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))))
  (logic.flag-proofp 'list x axioms thms atbl))

(defthmd definition-of-logic.proofp
  (equal (logic.proofp x axioms thms atbl)
         (and (logic.appeal-step-okp x axioms thms atbl)
              (logic.proof-listp (logic.subproofs x) axioms thms atbl)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-proofp
                                    logic.proofp
                                    logic.proof-listp))))

(defthmd definition-of-logic.proof-listp
  (equal (logic.proof-listp x axioms thms atbl)
         (if (consp x)
             (and (logic.proofp (car x) axioms thms atbl)
                  (logic.proof-listp (cdr x) axioms thms atbl))
           t))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable logic.flag-proofp
                                    logic.proofp
                                    logic.proof-listp))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.proofp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition logic.proof-listp))))



(defthm logic.proofp-when-not-consp
   (implies (not (consp x))
            (equal (logic.proofp x axioms thms atbl)
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp))))

(defthm logic.proof-listp-when-not-consp
  (implies (not (consp x))
           (equal (logic.proof-listp x axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-logic.proof-listp))))

(defthm logic.proof-listp-of-cons
  (equal (logic.proof-listp (cons a x) axioms thms atbl)
         (and (logic.proofp a axioms thms atbl)
              (logic.proof-listp x axioms thms atbl)))
  :hints(("Goal" :in-theory (enable definition-of-logic.proof-listp))))


(defthms-flag
  :thms ((proof booleanp-of-logic.proofp
                (equal (booleanp (logic.proofp x axioms thms atbl))
                       t))
         (list booleanp-of-logic.proof-listp
               (equal (booleanp (logic.proof-listp x axioms thms atbl))
                      t)))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.proofp)
           :induct (logic.appeal-induction flag x))))

(deflist logic.proof-listp (x axioms thms atbl)
  (logic.proofp x axioms thms atbl)
  :elementp-of-nil nil
  :already-definedp t)

(defthm logic.proofp-of-nth-when-logic.proof-listp
  ;; BOZO consider adding me to deflist
  (implies (logic.proof-listp x axioms thms atbl)
           (equal (logic.proofp (nth n x) axioms thms atbl)
                  (if (natp n)
                      (< n (len x))
                    (consp x))))
  :hints(("Goal" :in-theory (enable nth))))

(defthm forcing-logic.proof-listp-of-firstn
  (implies (force (logic.proof-listp x axioms thms atbl))
           (equal (logic.proof-listp (firstn n x) axioms thms atbl)
                  t)))

(defthm forcing-logic.proof-listp-of-restn
  (implies (force (logic.proof-listp x axioms thms atbl))
           (equal (logic.proof-listp (restn n x) axioms thms atbl)
                  t)))


(defthms-flag
  :thms ((proof logic.formula-atblp-of-logic.conclusion-when-logic.proofp
                (implies (logic.proofp x axioms thms atbl)
                         (equal (logic.formula-atblp (logic.conclusion x) atbl)
                                t)))
         (list logic.formula-list-atblp-of-logic.strip-conclusions-when-logic.proof-listp
               (implies (logic.proof-listp x axioms thms atbl)
                        (equal (logic.formula-list-atblp (logic.strip-conclusions x) atbl)
                               t))))
  :hints (("Goal"
           :in-theory (enable definition-of-logic.proofp)
           :induct (logic.appeal-induction flag x))))

(defthm logic.proof-listp-of-logic.subproofs-when-logic.proofp
   (implies (logic.proofp x axioms thms atbl)
            (equal (logic.proof-listp (logic.subproofs x) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp))))


(encapsulate
 ()
 (defun-sk logic.provablep (x axioms thms atbl)
   ;; A formula is provable if there exists some proof of it.
   #-skip-guards
   (declare (xargs ;:non-executable t

             ;; ACL2 4.0 change: must verify guards later to avoid new
             ;; checking about guards inside encapsulates.
             :verify-guards nil
             :guard (and (logic.formulap x)
                         (logic.formula-listp axioms)
                         (logic.formula-listp thms)
                         (logic.arity-tablep atbl))))
   #+skip-guards
   (declare (xargs ;:non-executable t
             :verify-guards nil))
   (acl2::exists proof
                 (and (logic.appealp proof)
                      (logic.proofp proof axioms thms atbl)
                      (equal (logic.conclusion proof) x)))
   :skolem-name logic.provable-witness)

 ;; ACL2 4.0 change: verify guards here instead of inline
 (verify-guards logic.provablep)

 (in-theory (disable logic.provablep)))


(defthm booleanp-of-logic.provablep
  (equal (booleanp (logic.provablep x axioms thms atbl))
         t)
  :hints(("Goal" :in-theory (enable logic.provablep))))

(defthm forcing-logic.appealp-of-logic.provable-witness
  (implies (force (logic.provablep x axioms thms atbl))
           (equal (logic.appealp (logic.provable-witness x axioms thms atbl))
                  t))
  :hints(("Goal" :in-theory (enable logic.provablep))))

(defthm forcing-logic.proofp-of-logic.provable-witness
  (implies (force (logic.provablep x axioms thms atbl))
           (equal (logic.proofp (logic.provable-witness x axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.provablep)
                                 (forcing-logic.appealp-of-logic.provable-witness)))))

(defthm forcing-logic.conclusion-of-logic.provable-witness
  (implies (force (logic.provablep x axioms thms atbl))
           (equal (logic.conclusion (logic.provable-witness x axioms thms atbl))
                  x))
  :hints(("Goal" :in-theory (e/d (logic.provablep)
                                 (forcing-logic.appealp-of-logic.provable-witness
                                  forcing-logic.proofp-of-logic.provable-witness)))))

(defthm logic.formulap-when-logic.provablep
  ;; Hrmn.  We might not want this rule, since we probably want to know ahead of
  ;; time that the formula is well-formed before we give it to provablep.
  (implies (logic.provablep x axioms thms atbl)
           (equal (logic.formulap x)
                  t))
  :hints(("Goal"
          :in-theory (disable forcing-logic.formulap-of-logic.conclusion)
          :use ((:instance forcing-logic.formulap-of-logic.conclusion
                           (x (logic.provable-witness x axioms thms atbl)))))))

(defthm logic.formula-atblp-when-logic.provablep
  ;; Hrmn.  We might not want this rule, since we probably want to know ahead of
  ;; time that the formula is well-formed before we give it to provablep.
  (implies (logic.provablep x axioms thms atbl)
           (equal (logic.formula-atblp x atbl)
                  t))
  :hints(("Goal"
          :in-theory (disable logic.formula-atblp-of-logic.conclusion-when-logic.proofp)
          :use ((:instance logic.formula-atblp-of-logic.conclusion-when-logic.proofp
                           (x (logic.provable-witness x axioms thms atbl)))))))

(defthm logic.provablep-when-not-consp
  (implies (not (consp x))
           (equal (logic.provablep x axioms thms atbl)
                  nil))
  :hints(("Goal"
          :in-theory (disable logic.formulap-when-not-consp)
          :use ((:instance logic.formulap-when-not-consp)))))

(defthm forcing-logic.provablep-when-logic.proofp
  (implies (and (logic.proofp x axioms thms atbl)
                (force (logic.appealp x)))
           (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                  t))
  :hints(("Goal" :use (:instance logic.provablep-suff
                                 (proof x)
                                 (x (logic.conclusion x))))))




(deflist logic.provable-listp (x axioms thms atbl)
  (logic.provablep x axioms thms atbl)
  :elementp-of-nil nil
  :guard (and (logic.formula-listp x)
              (logic.formula-listp axioms)
              (logic.formula-listp thms)
              (logic.arity-tablep atbl)))

(defthm logic.provablep-of-car-when-logic.provable-listp-free
  (implies (and (equal free (logic.conclusion (car x)))
                (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl))
           (equal (logic.provablep free axioms thms atbl)
                  (consp x))))

(defthm logic.provablep-of-second-when-logic.provable-listp
  ;; BOZO consider adding this to deflist.
  (implies (logic.provable-listp x axioms thms atbl)
           (equal (logic.provablep (second x) axioms thms atbl)
                  (consp (cdr x)))))

(defthm forcing-logic.provable-listp-of-logic.strip-conclusions-when-logic.proof-listp
  (implies (and (logic.proof-listp x axioms thms atbl)
                (force (logic.appeal-listp x)))
           (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.provable-listp-of-logic.subproofs-when-logic.proofp
   (implies (and (logic.proofp x axioms thms atbl)
                 (force (logic.appealp x)))
            (equal (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-logic.proofp))))

(defthm logic.formula-list-atblp-of-when-logic.provable-listp
  (implies (logic.provable-listp x axioms thms atbl)
           (equal (logic.formula-list-atblp x atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (logic.provable-list-witness x axioms thms atbl)
               :element (logic.provable-witness x axioms thms atbl)
               :guard (and (logic.formula-listp x)
                           (logic.formula-listp axioms)
                           (logic.formula-listp thms)
                           (logic.arity-tablep atbl)))

(defthm forcing-logic.appeal-listp-of-logic.provable-list-witness
  (implies (force (logic.provable-listp x axioms thms atbl))
           (equal (logic.appeal-listp (logic.provable-list-witness x axioms thms atbl))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm force-logic.proof-listp-of-logic.provable-list-witness
  (implies (force (logic.provable-listp x axioms thms atbl))
           (equal (logic.proof-listp (logic.provable-list-witness x axioms thms atbl) axioms thms atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.strip-conclusions-of-logic.provable-list-witness
  (implies (force (logic.provable-listp x axioms thms atbl))
           (equal (logic.strip-conclusions (logic.provable-list-witness x axioms thms atbl))
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.provablep-of-logic.conclusion-of-first-when-logic.provable-listp
  (implies (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
           (equal (logic.provablep (logic.conclusion (car x)) axioms thms atbl)
                  (consp x))))

(defthm logic.provablep-of-logic.conclusion-of-second-when-logic.provable-listp
  (implies (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
           (equal (logic.provablep (logic.conclusion (second x)) axioms thms atbl)
                  (consp (cdr x)))))

(defthm logic.provablep-of-logic.conclusion-of-third-when-logic.provable-listp
  (implies (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
           (equal (logic.provablep (logic.conclusion (third x)) axioms thms atbl)
                  (consp (cdr (cdr x))))))

(defthm logic.provablep-of-logic.conclusion-of-fourth-when-logic.provable-listp
  (implies (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
           (equal (logic.provablep (logic.conclusion (fourth x)) axioms thms atbl)
                  (consp (cdr (cdr (cdr x)))))))




;; BOZO fix proofp.lisp to unlocalize these
;; Skip can stay local

(defthmd lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.axiom-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) axioms atbl)
                  (logic.axiom-okp x axioms atbl)))
  :hints(("Goal" :in-theory (enable logic.axiom-okp))))

(defthmd lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.theorem-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) thms atbl)
                  (logic.theorem-okp x thms atbl)))
  :hints(("Goal" :in-theory (enable logic.theorem-okp))))

(defthmd lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.propositional-schema-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.propositional-schema-okp x atbl)))
  :hints(("Goal" :in-theory (e/d (logic.propositional-schema-okp)
                                 ((:executable-counterpart ACL2::force))))))

(defthmd lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.functional-equality-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.functional-equality-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.functional-equality-okp))))

(defthmd lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.beta-reduction-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.beta-reduction-okp x atbl)))
  :hints(("Goal" :in-theory (enable logic.beta-reduction-okp))))

(defthmd lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (equal (logic.strip-conclusions a) (logic.strip-conclusions b))
           (equal (equal (len a) (len b))
                  t))
  :hints(("Goal"
          :in-theory (disable len-of-logic.strip-conclusions)
          :use ((:instance len-of-logic.strip-conclusions (x a))
                (:instance len-of-logic.strip-conclusions (x b))))))

(defthmd lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.expansion-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.expansion-okp x atbl)))
  :hints(("Goal"
          :in-theory (e/d (logic.expansion-okp)
                          ((:executable-counterpart ACL2::force)))
          :use ((:instance lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
                           (a (logic.subproofs x))
                           (b new-subproofs))))))

(defthmd lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.contraction-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)))
                  (logic.contraction-okp x)))
  :hints(("Goal"
          :in-theory (enable logic.contraction-okp)
          :use ((:instance lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
                           (a (logic.subproofs x))
                           (b new-subproofs))))))

(defthmd lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.associativity-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)))
                  (logic.associativity-okp x)))
  :hints(("Goal"
          :in-theory (enable logic.associativity-okp)
          :use ((:instance lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
                           (a (logic.subproofs x))
                           (b new-subproofs))))))

(defthmd lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable
          (implies (and (logic.appealp x)
                        (logic.appeal-listp new-subproofs)
                        (true-listp new-subproofs)
                        (equal (logic.strip-conclusions (logic.subproofs x))
                               (logic.strip-conclusions new-subproofs)))
                   (equal (logic.cut-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)))
                          (logic.cut-okp x)))
          :hints(("Goal"
                  :in-theory (enable logic.cut-okp)
                  :use ((:instance lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
                                   (a (logic.subproofs x))
                                   (b new-subproofs))))))

(defthmd lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.instantiation-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.instantiation-okp x atbl)))
  :hints(("Goal"
          :in-theory (enable logic.instantiation-okp)
          :use ((:instance lemma-equal-lens-of-logic.strip-conclusions-for-forcing-logic.provablep-when-logic.subproofs-provable
                           (a (logic.subproofs x))
                           (b new-subproofs))))))

(defthmd lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.induction-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)))
                  (logic.induction-okp x)))
  :hints(("Goal" :in-theory (enable logic.induction-okp))))

(defthmd lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable
  (implies (and (logic.appealp x)
                (logic.appeal-listp new-subproofs)
                (true-listp new-subproofs)
                (equal (logic.strip-conclusions (logic.subproofs x))
                       (logic.strip-conclusions new-subproofs)))
           (equal (logic.base-eval-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                  (logic.base-eval-okp x atbl)))
  :hints(("Goal" :in-theory (e/d (logic.base-eval-okp)
                                 ((:executable-counterpart ACL2::force))))))

(encapsulate
 ()
 (local (defthm lemma-skip
          ;; BOZO remove me eventually
          (implies (and (logic.appealp x)
                        (logic.appeal-listp new-subproofs)
                        (true-listp new-subproofs)
                        (equal (logic.strip-conclusions (logic.subproofs x))
                               (logic.strip-conclusions new-subproofs)))
                   (equal (logic.skip-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) atbl)
                          (logic.skip-okp x atbl)))
          :hints(("Goal" :in-theory (enable logic.skip-okp)))))

 (defthmd lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable
   (implies (and (logic.appealp x)
                 (logic.appeal-listp new-subproofs)
                 (true-listp new-subproofs)
                 (equal (logic.strip-conclusions (logic.subproofs x))
                        (logic.strip-conclusions new-subproofs)))
            (equal (logic.appeal-step-okp (logic.appeal (logic.method x) (logic.conclusion x) new-subproofs (logic.extras x)) axioms thms atbl)
                   (logic.appeal-step-okp x axioms thms atbl)))
   :hints(("Goal" :in-theory (enable logic.appeal-step-okp
                                     lemma-axiom-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-theorem-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-propositional-schema-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-functional-equality-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-beta-reduction-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-expansion-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-contraction-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-associativity-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-cut-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-instantiation-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-induction-for-forcing-logic.provablep-when-logic.subproofs-provable
                                     lemma-base-eval-for-forcing-logic.provablep-when-logic.subproofs-provable)))))

(defthmd lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable
  ;; If we have a step-wise ok appeal, and all of its subproofs are
  ;; provable, then we can prove its conclusion by applying this step to
  ;; the witnessing proofs for its subproofs.
  (implies (and (logic.appealp x)
                (logic.appeal-step-okp x axioms thms atbl)
                (logic.formula-atblp (logic.conclusion x) atbl)
                (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
           (equal (logic.proofp
                   (logic.appeal (logic.method x)
                                 (logic.conclusion x)
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl)
                                 (logic.extras x))
                   axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable lemma-appeal-step-for-forcing-logic.provablep-when-logic.subproofs-provable
                                    definition-of-logic.proofp))))



(defthm forcing-logic.provablep-when-logic.subproofs-provable
   (implies (and (logic.appeal-step-okp x axioms thms atbl)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (force (logic.appealp x))
                 (force (logic.formula-atblp (logic.conclusion x) atbl)))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints(("Goal"
           :in-theory (enable lemma-main-for-forcing-logic.provablep-when-logic.subproofs-provable)
           :use (:instance forcing-logic.provablep-when-logic.proofp
                           (x (logic.appeal (logic.method x)
                                            (logic.conclusion x)
                                            (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                         axioms thms atbl)
                                            (logic.extras x)))))))



(defthm logic.provable-listp-of-logic.strip-conclusions-when-provable-first-and-rest
  ;; BOZO What in the world is this rule for?
  (implies (and (logic.provablep (logic.conclusion (car x)) axioms thms atbl)
                (logic.provable-listp (logic.strip-conclusions (cdr x)) axioms thms atbl))
           (equal (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
                  t)))


(defthm logic.formula-list-atblp-of-logic.strip-conclusions-of-cdr-when-logic.provable-listp
  ;; BOZO add to backchaining rules
  (implies (logic.provable-listp (logic.strip-conclusions x) axioms thms atbl)
           (equal (logic.formula-list-atblp (logic.strip-conclusions (cdr x)) atbl)
                  t)))



(defund logic.soundness-claim (name)
  (declare (xargs :guard (logic.function-namep name)))
  (logic.por '(pequal* (logic.appealp x) 'nil)
   (logic.por (logic.pequal (logic.function name '(x axioms thms atbl)) ''nil)
              '(pnot* (pequal* (logic.provablep (logic.conclusion x) axioms thms atbl) 'nil)))))
