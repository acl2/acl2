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
(include-book "fertilize")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Distribute All
;;
;; In the fertilize tactic, we provide the following capability.  Suppose
;; (equal t1 t2) is a hypothesis in the clause.  Then, we can replace t1 with
;; t2 or vice versa everywhere throughout the clause.  We have no good
;; heuristic for deciding when this is desirable in general, or even which
;; direction the fertilization should go if we decided we wanted to try it.
;; However, consider the special cases:
;;
;;   (equal var expr)
;;   (equal expr var)
;;
;; Where var does not occur in expr.  Then, we think it is desirable to
;; entirely eliminate var from the clause, replacing it with expr instead.  We
;; call this distribution.  ACL2 does this as part of simplification, but has a
;; much more complicated routine in order to handle equivalence relations.
;; (See the function "remove-trivial-equivalences", etc.)
;;
;; As a special case of fertilization, distribution is easy to justify; we just
;; reuse the argument there.  The only twist is deciding how to fertilize.



(defun distribute.type1-literalp (x)
  ;; We recognize terms of the form (not (equal var expr)) where expr does
  ;; not contain var.
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (equal (logic.function-name x) 'not)
       (equal (len (logic.function-args x)) 1)
       (let ((body (first (logic.function-args x))))
         (and (logic.functionp body)
              (equal (logic.function-name body) 'equal)
              (equal (len (logic.function-args body)) 2)
              (let ((var (first (logic.function-args body)))
                    (expr (second (logic.function-args body))))
                (and (logic.variablep var)
                     (not (memberp var (logic.term-vars expr)))))))))

(defthm booleanp-of-distribute.type1-literalp
  (equal (booleanp (distribute.type1-literalp x))
         t))

(defun distribute.type1-var (x)
  (declare (xargs :guard (and (logic.termp x)
                              (distribute.type1-literalp x))
                  :guard-hints (("Goal" :in-theory (enable distribute.type1-literalp)))))
  (first (logic.function-args (first (logic.function-args x)))))

(defun distribute.type1-expr (x)
  (declare (xargs :guard (and (logic.termp x)
                              (distribute.type1-literalp x))
                  :guard-hints (("Goal" :in-theory (enable distribute.type1-literalp)))))
  (second (logic.function-args (first (logic.function-args x)))))

(defun distribute.substitute-type1-literal (literal clause)
  (declare (xargs :guard (and (logic.termp literal)
                              (distribute.type1-literalp literal)
                              (logic.term-listp clause)
                              (memberp literal clause))))
  (let ((var (distribute.type1-var literal))
        (expr (distribute.type1-expr literal)))
    (logic.replace-subterm-list clause var expr)))

(defthm cons-listp-of-distribute.substitute-type1-literal
  (equal (consp (distribute.substitute-type1-literal literal clause))
         (consp clause)))

(defthm forcing-logic.term-listp-of-distribute.substitute-type1-literal
  (implies (force (and (logic.termp literal)
                       (distribute.type1-literalp literal)
                       (logic.term-listp clause)))
           (equal (logic.term-listp (distribute.substitute-type1-literal literal clause))
                  t)))

(defthm forcing-logic.term-list-atblp-of-distribute.substitute-type1-literal
  (implies (force (and (logic.termp literal)
                       (logic.term-atblp literal atbl)
                       (distribute.type1-literalp literal)
                       (logic.term-list-atblp clause atbl)))
           (equal (logic.term-list-atblp (distribute.substitute-type1-literal literal clause) atbl)
                  t)))

(defun distribute.substitute-type1-literal-bldr (literal clause proof)
   (declare (xargs :guard (and (logic.termp literal)
                               (distribute.type1-literalp literal)
                               (logic.term-listp clause)
                               (memberp literal clause)
                               (logic.appealp proof)
                               (equal (logic.conclusion proof)
                                      (clause.clause-formula (distribute.substitute-type1-literal literal clause))))))
   (let ((var (distribute.type1-var literal))
         (expr (distribute.type1-expr literal)))
     (tactic.fertilize-bldr var expr clause proof)))

(defobligations distribute.substitute-type1-literal-bldr
  (tactic.fertilize-bldr))

(defthm distribute.substitute-type1-literal-bldr-under-iff
  (iff (distribute.substitute-type1-literal-bldr literal clause proof)
       t))

(defthm forcing-logic.appealp-of-distribute.substitute-type1-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type1-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type1-literal literal clause)))))
           (equal (logic.appealp (distribute.substitute-type1-literal-bldr literal clause proof))
                  t)))

(defthm forcing-logic.conclusion-of-distribute.substitute-type1-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type1-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type1-literal literal clause)))))
           (equal (logic.conclusion (distribute.substitute-type1-literal-bldr literal clause proof))
                  (clause.clause-formula clause)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm@ forcing-logic.proofp-of-distribute.substitute-type1-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type1-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type1-literal literal clause)))
                       ;; ---
                       (logic.term-list-atblp clause atbl)
                       (logic.term-atblp literal atbl)
                       (logic.proofp proof axioms thms atbl)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (@obligations distribute.substitute-type1-literal-bldr)))
           (equal (logic.proofp (distribute.substitute-type1-literal-bldr literal clause proof) axioms thms atbl)
                  t)))

(in-theory (disable distribute.type1-literalp
                    distribute.type1-var
                    distribute.type1-expr
                    distribute.substitute-type1-literal
                    distribute.substitute-type1-literal-bldr))




(defun distribute.type2-literalp (x)
  ;; We recognize terms of the form (not (equal expr var)) where expr does
  ;; not contain var.
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (equal (logic.function-name x) 'not)
       (equal (len (logic.function-args x)) 1)
       (let ((body (first (logic.function-args x))))
         (and (logic.functionp body)
              (equal (logic.function-name body) 'equal)
              (equal (len (logic.function-args body)) 2)
              (let ((expr (first (logic.function-args body)))
                    (var (second (logic.function-args body))))
                (and (logic.variablep var)
                     (not (memberp var (logic.term-vars expr)))))))))

(defthm booleanp-of-distribute.type2-literalp
  (equal (booleanp (distribute.type2-literalp x))
         t))

(defun distribute.type2-var (x)
  (declare (xargs :guard (and (logic.termp x)
                              (distribute.type2-literalp x))
                  :guard-hints (("Goal" :in-theory (enable distribute.type2-literalp)))))
  (second (logic.function-args (first (logic.function-args x)))))

(defun distribute.type2-expr (x)
  (declare (xargs :guard (and (logic.termp x)
                              (distribute.type2-literalp x))
                  :guard-hints (("Goal" :in-theory (enable distribute.type2-literalp)))))
  (first (logic.function-args (first (logic.function-args x)))))

(defun distribute.substitute-type2-literal (literal clause)
  (declare (xargs :guard (and (logic.termp literal)
                              (distribute.type2-literalp literal)
                              (logic.term-listp clause)
                              (memberp literal clause))))
  (let ((var (distribute.type2-var literal))
        (expr (distribute.type2-expr literal)))
    (logic.replace-subterm-list clause var expr)))

(defthm cons-listp-of-distribute.substitute-type2-literal
  (equal (consp (distribute.substitute-type2-literal literal clause))
         (consp clause)))

(defthm forcing-logic.term-listp-of-distribute.substitute-type2-literal
  (implies (force (and (logic.termp literal)
                       (distribute.type2-literalp literal)
                       (logic.term-listp clause)))
           (equal (logic.term-listp (distribute.substitute-type2-literal literal clause))
                  t)))

(defthm forcing-logic.term-list-atblp-of-distribute.substitute-type2-literal
  (implies (force (and (logic.termp literal)
                       (logic.term-atblp literal atbl)
                       (distribute.type2-literalp literal)
                       (logic.term-list-atblp clause atbl)))
           (equal (logic.term-list-atblp (distribute.substitute-type2-literal literal clause) atbl)
                  t)))

(defun distribute.substitute-type2-literal-bldr (literal clause proof)
   (declare (xargs :guard (and (logic.termp literal)
                               (distribute.type2-literalp literal)
                               (logic.term-listp clause)
                               (memberp literal clause)
                               (logic.appealp proof)
                               (equal (logic.conclusion proof)
                                      (clause.clause-formula (distribute.substitute-type2-literal literal clause))))))
   (let ((var (distribute.type2-var literal))
         (expr (distribute.type2-expr literal)))
     (tactic.fertilize-bldr var expr clause proof)))

(defobligations distribute.substitute-type2-literal-bldr
  (tactic.fertilize-bldr))

(defthm distribute.substitute-type2-literal-bldr-under-iff
  (iff (distribute.substitute-type2-literal-bldr literal clause proof)
       t))

(defthm forcing-logic.appealp-of-distribute.substitute-type2-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type2-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type2-literal literal clause)))))
           (equal (logic.appealp (distribute.substitute-type2-literal-bldr literal clause proof))
                  t)))

(defthm forcing-logic.conclusion-of-distribute.substitute-type2-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type2-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type2-literal literal clause)))))
           (equal (logic.conclusion (distribute.substitute-type2-literal-bldr literal clause proof))
                  (clause.clause-formula clause)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm@ forcing-logic.proofp-of-distribute.substitute-type2-literal-bldr
  (implies (force (and (logic.termp literal)
                       (distribute.type2-literalp literal)
                       (logic.term-listp clause)
                       (memberp literal clause)
                       (logic.appealp proof)
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (distribute.substitute-type2-literal literal clause)))
                       ;; ---
                       (logic.term-list-atblp clause atbl)
                       (logic.term-atblp literal atbl)
                       (logic.proofp proof axioms thms atbl)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (@obligations distribute.substitute-type2-literal-bldr)))
           (equal (logic.proofp (distribute.substitute-type2-literal-bldr literal clause proof) axioms thms atbl)
                  t)))

(in-theory (disable distribute.type2-literalp
                    distribute.type2-var
                    distribute.type2-expr
                    distribute.substitute-type2-literal
                    distribute.substitute-type2-literal-bldr))




(defund distribute.find-type1-literal (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (distribute.type1-literalp (car x))
          (car x)
        (distribute.find-type1-literal (cdr x)))
    nil))

(defthm distribute.type1-literalp-of-distribute.find-type1-literal
  (equal (distribute.type1-literalp (distribute.find-type1-literal x))
         (if (distribute.find-type1-literal x)
             t
           nil))
  :hints(("Goal" :in-theory (enable distribute.find-type1-literal))))

(defthm forcing-logic.termp-of-distribute.find-type1-literal
  (implies (and (distribute.find-type1-literal x)
                (force (logic.term-listp x)))
           (equal (logic.termp (distribute.find-type1-literal x))
                  t))
  :hints(("Goal" :in-theory (enable distribute.find-type1-literal))))

(defthm memberp-of-distribute.find-type1-literal
  (implies (distribute.find-type1-literal x)
           (equal (memberp (distribute.find-type1-literal x) x)
                  t))
  :hints(("Goal" :in-theory (enable distribute.find-type1-literal))))



(defund distribute.find-type2-literal (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (if (distribute.type2-literalp (car x))
          (car x)
        (distribute.find-type2-literal (cdr x)))
    nil))

(defthm distribute.type2-literalp-of-distribute.find-type2-literal
  (equal (distribute.type2-literalp (distribute.find-type2-literal x))
         (if (distribute.find-type2-literal x)
             t
           nil))
  :hints(("Goal" :in-theory (enable distribute.find-type2-literal))))

(defthm forcing-logic.termp-of-distribute.find-type2-literal
  (implies (and (distribute.find-type2-literal x)
                (force (logic.term-listp x)))
           (equal (logic.termp (distribute.find-type2-literal x))
                  t))
  :hints(("Goal" :in-theory (enable distribute.find-type2-literal))))

(defthm memberp-of-distribute.find-type2-literal
  (implies (distribute.find-type2-literal x)
           (equal (memberp (distribute.find-type2-literal x) x)
                  t))
  :hints(("Goal" :in-theory (enable distribute.find-type2-literal))))




(defund distribute.try-distributing-clause (x)
  (declare (xargs :guard (logic.term-listp x)))
  (let ((lit1 (distribute.find-type1-literal x)))
    (if lit1
        (distribute.substitute-type1-literal lit1 x)
      (let ((lit2 (distribute.find-type2-literal x)))
        (if lit2
            (distribute.substitute-type2-literal lit2 x)
          x)))))

(defthm consp-of-distribute.try-distributing-clause
  (equal (consp (distribute.try-distributing-clause x))
         (consp x))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause))))

(defthm forcing-logic.term-listp-of-distribute.try-distributing-clause
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (distribute.try-distributing-clause x))
                  t))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause))))

(defthm forcing-logic.term-list-atblp-of-distribute.try-distributing-clause
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)))
           (equal (logic.term-list-atblp (distribute.try-distributing-clause x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause))))




(defund distribute.try-distributing-clause-bldr (x proof)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (distribute.try-distributing-clause x))))
                  :verify-guards nil))
  (let ((lit1 (distribute.find-type1-literal x)))
    (if lit1
        (distribute.substitute-type1-literal-bldr lit1 x proof)
      (let ((lit2 (distribute.find-type2-literal x)))
        (if lit2
            (distribute.substitute-type2-literal-bldr lit2 x proof)
          (logic.appeal-identity proof))))))

(defobligations distribute.try-distributing-clause-bldr
  (distribute.substitute-type1-literal-bldr
   distribute.substitute-type2-literal-bldr))

(encapsulate
 ()
 (local (in-theory (enable distribute.try-distributing-clause
                           distribute.try-distributing-clause-bldr)))

 (verify-guards distribute.try-distributing-clause-bldr)

 (defthm distribute.try-distributing-clause-bldr-under-iff
   (iff (distribute.try-distributing-clause-bldr x proof)
        t))

 (defthm forcing-logic.appealp-of-distribute.try-distributing-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (distribute.try-distributing-clause x)))))
            (equal (logic.appealp (distribute.try-distributing-clause-bldr x proof))
                   t)))

 (defthm forcing-logic.conclusion-of-distribute.try-distributing-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (distribute.try-distributing-clause x)))))
            (equal (logic.conclusion (distribute.try-distributing-clause-bldr x proof))
                   (clause.clause-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-distribute.try-distributing-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.clause-formula (distribute.try-distributing-clause x)))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations distribute.try-distributing-clause-bldr)))
            (equal (logic.proofp (distribute.try-distributing-clause-bldr x proof) axioms thms atbl)
                   t))))



(defprojection :list (distribute.try-distributing-clause-list x)
               :element (distribute.try-distributing-clause x)
               :guard (logic.term-list-listp x))

(defthm cons-listp-of-distribute.try-distributing-clause-list
  (equal (cons-listp (distribute.try-distributing-clause-list x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-listp-of-distribute.try-distributing-clause-list
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (distribute.try-distributing-clause-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-list-atblp-of-distribute.try-distributing-clause-list
  (implies (force (and (logic.term-list-listp x)
                       (logic.term-list-list-atblp x atbl)))
           (equal (logic.term-list-list-atblp (distribute.try-distributing-clause-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund distribute.try-distributing-clause-list-bldr (x proofs)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (distribute.try-distributing-clause-list x))))))
  (if (consp x)
      (cons (distribute.try-distributing-clause-bldr (car x) (car proofs))
            (distribute.try-distributing-clause-list-bldr (cdr x) (cdr proofs)))
    nil))

(defobligations distribute.try-distributing-clause-list-bldr
  (distribute.try-distributing-clause-bldr))

(defthm forcing-logic.appeal-listp-of-distribute.try-distributing-clause-list-bldr
  (implies (force (and (logic.term-list-listp x)
                       (cons-listp x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (clause.clause-list-formulas (distribute.try-distributing-clause-list x)))))
           (equal (logic.appeal-listp (distribute.try-distributing-clause-list-bldr x proofs))
                  t))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause-list-bldr))))

(defthm forcing-logic.strip-conclusions-of-distribute.try-distributing-clause-list-bldr
  (implies (force (and (logic.term-list-listp x)
                       (cons-listp x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (clause.clause-list-formulas (distribute.try-distributing-clause-list x)))))
           (equal (logic.strip-conclusions (distribute.try-distributing-clause-list-bldr x proofs))
                  (clause.clause-list-formulas x)))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause-list-bldr))))

(defthm@ forcing-logic.proof-listp-of-distribute.try-distributing-clause-list-bldr
  (implies (force (and (logic.term-list-listp x)
                       (cons-listp x)
                       (logic.appeal-listp proofs)
                       (equal (logic.strip-conclusions proofs)
                              (clause.clause-list-formulas (distribute.try-distributing-clause-list x)))
                       ;; ---
                       (@obligations distribute.try-distributing-clause-list-bldr)
                       (equal (cdr (lookup 'not atbl)) 1)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (logic.term-list-list-atblp x atbl)
                       (logic.proof-listp proofs axioms thms atbl)
                       ))
           (equal (logic.proof-listp (distribute.try-distributing-clause-list-bldr x proofs) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable distribute.try-distributing-clause-list-bldr))))




(defund tactic.distribute-all-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'distribute-all)
         (not extras)
         (let ((prev-goals (tactic.skeleton->goals history)))
           (equal goals
                  (distribute.try-distributing-clause-list prev-goals))))))

(defthm booleanp-of-tactic.distribute-all-okp
  (equal (booleanp (tactic.distribute-all-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (tactic.distribute-all-okp)
                                 ((:executable-counterpart acl2::force))))))



(defund tactic.distribute-all-tac (x warnp)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (booleanp warnp))))
  (let ((goals (tactic.skeleton->goals x)))
    (if (not (consp goals))
        (ACL2::cw "~s0distribute-all-tac failure~s1: all clauses have already been proven.~%" *red* *black*)
      (let ((new-goals (distribute.try-distributing-clause-list goals)))
        (if (equal goals new-goals)
            (and warnp
                 (ACL2::cw "~s0distribute-all-tac failure~s1: there are no trivial equalities to distribute.~%" *red* *black*))
          (tactic.extend-skeleton new-goals
                                  'distribute-all
                                  nil
                                  x))))))

(defthm forcing-tactic.skeletonp-of-tactic.distribute-all-tac
  (implies (and (tactic.distribute-all-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.skeletonp (tactic.distribute-all-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.distribute-all-tac))))

(defthm forcing-tactic.distribute-all-okp-of-tactic.distribute-all-tac
  (implies (and (tactic.distribute-all-tac x warnp)
                (force (tactic.skeletonp x)))
           (equal (tactic.distribute-all-okp (tactic.distribute-all-tac x warnp))
                  t))
  :hints(("Goal" :in-theory (enable tactic.distribute-all-tac
                                    tactic.distribute-all-okp))))



(defund tactic.distribute-all-compile (x proofs)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.distribute-all-okp x)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((history      (tactic.skeleton->history x))
         (orig-goals   (tactic.skeleton->goals history)))
    (distribute.try-distributing-clause-list-bldr orig-goals proofs)))

(defobligations tactic.distribute-all-compile
  (distribute.try-distributing-clause-list-bldr))

(encapsulate
 ()
 (local (in-theory (enable tactic.distribute-all-okp
                           tactic.distribute-all-compile)))

 (verify-guards tactic.distribute-all-compile)

 (defthm forcing-logic.appeal-listp-of-tactic.distribute-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.distribute-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appeal-listp (tactic.distribute-all-compile x proofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-tactic.distribute-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.distribute-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))))
            (equal (logic.strip-conclusions (tactic.distribute-all-compile x proofs))
                   (clause.clause-list-formulas (tactic.skeleton->goals (tactic.skeleton->history x))))))

 (defthm@ forcing-logic.proof-listp-of-tactic.distribute-all-compile
   (implies (force (and (tactic.skeletonp x)
                        (tactic.distribute-all-okp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (tactic.skeleton->goals x))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (tactic.skeleton-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations tactic.distribute-all-compile)))
            (equal (logic.proof-listp (tactic.distribute-all-compile x proofs) axioms thms atbl)
                   t))))

