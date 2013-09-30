;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "factor")
(include-book "../../build/lambda")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; (binding-formula x)
;;
;; Assume x is a (term . value) pair which occurs in an assignment.  We
;; produce a corresponding formula, i.e., term = nil when the value is nil,
;; or term != nil otherwise.
;;
;; Note: We leave this function enabled.

(defun binding-formula (x)
  (declare (xargs :guard (and (consp x)
                              (logic.termp (car x)))))
  (if (cdr x)
      (logic.pnot (logic.pequal (car x) ''nil))
    (logic.pequal (car x) ''nil)))




;; (assignment-formulas x)
;;
;; We produce a list of formulas corresponding to each binding in the
;; assignment.

(encapsulate
 ()
 (local (in-theory (disable binding-formula)))
 (defprojection
   :list (assignment-formulas x)
   :element (binding-formula x)
   :guard (and (mapp x)
               (logic.term-listp (domain x)))))

(defthm forcing-logic.formulap-listp-of-assignment-formulas
  (implies (force (logic.term-listp (domain x)))
           (equal (logic.formula-listp (assignment-formulas x))
                  t))
  :hints(("Goal" :in-theory (enable assignment-formulas))))

(defthm forcing-logic.formula-atblp-listp-of-assignment-formulas
  (implies (force (logic.term-list-atblp (domain x) atbl))
           (equal (logic.formula-list-atblp (assignment-formulas x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable assignment-formulas))))






(defderiv clause.factor-bldr-lemma-1
  :from   ((proof x (v P (!= (? a2) nil)))
           (proof y (v P (= (? a1) (? a2))))
           (proof z (v P (= (? b1) (? b2))))
           (term  c (? c)))
  :derive (v P (= (if (? a1) (? b1) (? c)) (? b2)))
  :proof  (@derive
           ((v P (!= (? a2) nil))                                          (@given x))
           ((v P (= (? a1) (? a2)))                                        (@given y))
           ((v P (!= (? a1) nil))                                          (build.disjoined-substitute-into-not-pequal @-- @-) *1)
           ((v (= x nil) (= (if x y z) y))                                 (build.axiom (axiom-if-when-not-nil)))
           ((v (= (? a1) nil) (= (if (? a1) (? b1) (? c)) (? b1)))         (build.instantiation @- (@sigma (x . (? a1)) (y . (? b1)) (z . (? c)))))
           ((v P (v (= (? a1) nil) (= (if (? a1) (? b1) (? c)) (? b1))))   (build.expansion (@formula P) @-))
           ((v P (= (if (? a1) (? b1) c) (? b1)))                          (build.disjoined-modus-ponens-2 *1 @-))
           ((v P (= (? b1) (? b2)))                                        (@given z))
           ((v P (= (if (? a1) (? b1) c) (? b2)))                          (build.disjoined-transitivity-of-pequal @-- @-)))
  :minatbl ((if . 3)))

(defderiv clause.factor-bldr-lemma-2
  :from   ((proof x (v P (= (? a2) nil)))
           (proof y (v P (= (? a1) (? a2))))
           (proof z (v P (= (? c1) (? c2))))
           (term  b (? b)))
  :derive (v P (= (if (? a1) (? b) (? c1)) (? c2)))
  :proof  (@derive
           ((v P (= (? a2) nil))                                            (@given x))
           ((v P (= (? a1) (? a2)))                                         (@given y))
           ((v P (= (? a1) nil))                                            (build.disjoined-transitivity-of-pequal @- @--) *1)
           ((v (!= x nil) (= (if x y z) z))                                 (build.axiom (axiom-if-when-nil)))
           ((v (!= (? a1) nil) (= (if (? a1) (? b) (? c1)) (? c1)))         (build.instantiation @- (@sigma (x . (? a1)) (y . (? b)) (z . (? c1)))))
           ((v P (v (!= (? a1) nil) (= (if (? a1) (? b) (? c1)) (? c1))))   (build.expansion (@formula P) @-))
           ((v P (= (if (? a1) (? b) (? c1)) (? c1)))                       (build.disjoined-modus-ponens *1 @-))
           ((v P (= (? c1) (? c2)))                                         (@given z))
           ((v P (= (if (? a1) (? b) (? c1)) (? c2)))                       (build.disjoined-transitivity-of-pequal @-- @-)))
  :minatbl ((if . 3)))



(defund clause.flag-factor-bldr (flag x assignment hyps hyps-formula)
   ;; X is a term and assignment is non-empty.
   ;; Our "hyps" are the negated formulas from the assignment, i.e.,
   ;;
   ;;   hyps = (logic.smart-negate-formulas (assignment-formulas assignment))
   ;;
   ;; Our goal is to prove hyps v x = x|assignment
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (consp assignment)
                              (mapp assignment)
                              (logic.term-listp (domain assignment))
                              ;; hyps just saves us from having to recons this each time.
                              (equal hyps (logic.smart-negate-formulas (assignment-formulas assignment)))
                              ;; hyps-formula just saves us from having to recons this each time.
                              (equal hyps-formula (logic.disjoin-formulas hyps)))
                   :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x)
             (build.expansion hyps-formula (build.reflexivity x)))
            ((logic.variablep x)
             (build.expansion hyps-formula (build.reflexivity x)))
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (if (and (equal name 'if)
                        (equal (len args) 3))
                   ;; Matched (if a b c).
                   (let* ((a-proof (clause.flag-factor-bldr 'term (first args) assignment hyps hyps-formula))
                          (a-prime (logic.=rhs (logic.vrhs (logic.conclusion a-proof))))
                          (binding (lookup a-prime assignment)))
                     (if binding
                         (if (cdr binding)
                             ;; Assignment binds a' to t.
                             ;;  -- a' != nil is the binding formula.
                             ;;  -- a' = nil is one of the disjuncts in hyps.
                             ;; Goal is to prove hyps v (if a b c) = b'.
                             (clause.factor-bldr-lemma-1 (build.multi-assoc-expansion
                                                          (build.commute-or
                                                           (build.propositional-schema (logic.pequal a-prime ''nil))) hyps)
                                                             a-proof
                                                             (clause.flag-factor-bldr 'term (second args) assignment hyps hyps-formula)
                                                             (third args))
                           (clause.factor-bldr-lemma-2 (build.multi-assoc-expansion (build.propositional-schema (logic.pequal a-prime ''nil)) hyps)
                                                           a-proof
                                                           (clause.flag-factor-bldr 'term (third args) assignment hyps hyps-formula)
                                                           (second args)))
                       ;; Assignment does not bind a'.
                       ;; Goal is hyps v (if a b c) = (if a' b' c')
                       (build.disjoined-pequal-by-args 'if
                                                       hyps-formula
                                                       (list a-proof
                                                             (clause.flag-factor-bldr 'term (second args) assignment hyps hyps-formula)
                                                             (clause.flag-factor-bldr 'term (third args) assignment hyps hyps-formula)))))
                 ;; Matched a non-if function.
                 (build.disjoined-pequal-by-args name
                                                 hyps-formula
                                                 (clause.flag-factor-bldr 'list args assignment hyps hyps-formula)))))
            ((logic.lambdap x)
             (let ((formals (logic.lambda-formals x))
                   (body    (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (build.disjoined-lambda-pequal-by-args formals body
                                                      hyps-formula
                                                      (clause.flag-factor-bldr 'list actuals assignment hyps hyps-formula))))
            (t nil))
    (if (consp x)
        (cons (clause.flag-factor-bldr 'term (car x) assignment hyps hyps-formula)
              (clause.flag-factor-bldr 'list (cdr x) assignment hyps hyps-formula))
      nil)))

(defobligations clause.flag-factor-bldr
  (build.reflexivity
   build.expansion
   build.propositional-schema
   build.commute-or
   build.multi-assoc-expansion
   clause.factor-bldr-lemma-1
   clause.factor-bldr-lemma-2
   build.disjoined-pequal-by-args
   build.disjoined-lambda-pequal-by-args))

(defund clause.factor-bldr (x assignment)
  (declare (xargs :guard (and (logic.termp x)
                              (consp assignment)
                              (mapp assignment)
                              (logic.term-listp (domain assignment)))
                  :verify-guards nil))
  (let* ((hyps         (logic.smart-negate-formulas (assignment-formulas assignment)))
         (hyps-formula (logic.disjoin-formulas hyps)))
    (clause.flag-factor-bldr 'term x assignment hyps hyps-formula)))

(defund clause.factor-list-bldr (x assignment)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp assignment)
                              (mapp assignment)
                              (logic.term-listp (domain assignment)))
                  :verify-guards nil))
  (let* ((hyps         (logic.smart-negate-formulas (assignment-formulas assignment)))
         (hyps-formula (logic.disjoin-formulas hyps)))
    (clause.flag-factor-bldr 'list x assignment hyps hyps-formula)))

(defobligations clause.factor-bldr
  (clause.flag-factor-bldr))

(defobligations clause.factor-list-bldr
  (clause.flag-factor-bldr))

(defthmd definition-of-clause.factor-bldr
  (equal (clause.factor-bldr x assignment)
         (let* ((hyps          (logic.smart-negate-formulas (assignment-formulas assignment)))
                (hyps-formula  (logic.disjoin-formulas hyps)))
           (cond ((logic.constantp x)
                  (build.expansion hyps-formula (build.reflexivity x)))
                 ((logic.variablep x)
                  (build.expansion hyps-formula (build.reflexivity x)))
                 ((logic.functionp x)
                  (let ((name (logic.function-name x))
                        (args (logic.function-args x)))
                    (if (and (equal name 'if)
                             (equal (len args) 3))
                        ;; Matched (if a b c).
                        (let* ((a-proof (clause.factor-bldr (first args) assignment))
                               (a-prime (logic.=rhs (logic.vrhs (logic.conclusion a-proof))))
                               (binding (lookup a-prime assignment)))
                          (if binding
                              (if (cdr binding)
                                  ;; Assignment binds a' to t.
                                  ;;  -- a' != nil is the binding formula.
                                  ;;  -- a' = nil is one of the disjuncts in hyps.
                                  ;; Goal is to prove hyps v (if a b c) = b'.
                                  (clause.factor-bldr-lemma-1 (build.multi-assoc-expansion (build.commute-or (build.propositional-schema (logic.pequal a-prime ''nil))) hyps)
                                                                  a-proof
                                                                  (clause.factor-bldr (second args) assignment)
                                                                  (third args))
                                (clause.factor-bldr-lemma-2 (build.multi-assoc-expansion (build.propositional-schema (logic.pequal a-prime ''nil)) hyps)
                                                                a-proof
                                                                (clause.factor-bldr (third args) assignment)
                                                                (second args)))
                            ;; Assignment does not bind a'.
                            ;; Goal is hyps v (if a b c) = (if a' b' c')
                            (build.disjoined-pequal-by-args 'if
                                                            hyps-formula
                                                            (list a-proof
                                                                  (clause.factor-bldr (second args) assignment)
                                                                  (clause.factor-bldr (third args) assignment)))))
                      ;; Matched a non-if function.
                      (build.disjoined-pequal-by-args name
                                                      hyps-formula
                                                      (clause.factor-list-bldr args assignment)))))
                 ((logic.lambdap x)
                  (let ((formals (logic.lambda-formals x))
                        (body    (logic.lambda-body x))
                        (actuals (logic.lambda-actuals x)))
                    (build.disjoined-lambda-pequal-by-args formals body
                                                           hyps-formula
                                                           (clause.factor-list-bldr actuals assignment))))
                 (t nil))))
         :rule-classes :definition
         :hints(("Goal" :in-theory (enable clause.factor-bldr
                                           clause.factor-list-bldr
                                           clause.flag-factor-bldr))))

(defthmd definition-of-clause.factor-list-bldr
  (equal (clause.factor-list-bldr x assignment)
         (if (consp x)
             (cons (clause.factor-bldr (car x) assignment)
                   (clause.factor-list-bldr (cdr x) assignment))
           nil))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.factor-bldr
                                    clause.factor-list-bldr
                                    clause.flag-factor-bldr))))

(defthm forcing-clause.flag-factor-bldr-of-term-removal
  (implies (force (and (equal hyps (logic.smart-negate-formulas (assignment-formulas assignment)))
                       (equal hyps-formula (logic.disjoin-formulas hyps))))
           (equal (clause.flag-factor-bldr 'term x assignment hyps hyps-formula)
                  (clause.factor-bldr x assignment)))
  :hints(("Goal" :in-theory (enable clause.factor-bldr))))

(defthm clause.flag-factor-bldr-of-list-removal
  (implies (force (and (equal hyps (logic.smart-negate-formulas (assignment-formulas assignment)))
                       (equal hyps-formula (logic.disjoin-formulas hyps))))
           (equal (clause.flag-factor-bldr 'list x assignment hyps hyps-formula)
                  (clause.factor-list-bldr x assignment)))
  :hints(("Goal" :in-theory (enable clause.factor-list-bldr))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.factor-bldr))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.factor-list-bldr))))



(defthm clause.factor-list-bldr-when-not-consp
  (implies (not (consp x))
           (equal (clause.factor-list-bldr x assignment)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-list-bldr))))

(defthm clause.factor-list-bldr-of-cons
  (equal (clause.factor-list-bldr (cons a x) assignment)
         (cons (clause.factor-bldr a assignment)
               (clause.factor-list-bldr x assignment)))
  :hints(("Goal" :in-theory (enable definition-of-clause.factor-list-bldr))))

(encapsulate
 ()
 (defthmd lemma-for-nil-preservingp-of-clause.factor-list-bldr
   (equal (clause.factor-bldr nil assignment)
          nil)
   :hints(("Goal" :in-theory (enable definition-of-clause.factor-bldr))))
 (local (in-theory (enable lemma-for-nil-preservingp-of-clause.factor-list-bldr)))
 (defprojection
   :list (clause.factor-list-bldr x assignment)
   :element (clause.factor-bldr x assignment)
   :guard (and (logic.term-listp x)
               (consp assignment)
               (mapp assignment)
               (logic.term-listp (domain assignment)))
   :verify-guards nil
   :nil-preservingp t
   :already-definedp t))


;; This is super-aggressive forcing, but we should only be looking for the
;; right terms during these proofs.
(defthmd lemma-forcing-memberp-of-pequal-a-nil-in-assignment-formulas
  (implies (and (force (lookup a x))
                (force (not (cdr (lookup a x))))
                (force (logic.term-listp (domain x)))
                (force (logic.termp a)))
           (equal (memberp (logic.pequal a ''nil) (assignment-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

;; This is super-aggressive forcing, but we should only be looking for the
;; right terms during these proofs.
(defthmd lemma-forcing-memberp-of-logic.pnot-pequal-a-nil-in-assignment-formulas
  (implies (and (force (lookup a x))
                (force (cdr (lookup a x)))
                (force (logic.term-listp (domain x)))
                (force (logic.termp a)))
           (equal (memberp (logic.pnot (logic.pequal a ''nil)) (assignment-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defthmd lemma-1-for-forcing-logic.appealp-of-clause.factor-bldr
  (implies (and (logic.appeal-listp (clause.factor-list-bldr x assignment))
                (force (consp x)))
           (equal (logic.appealp (clause.factor-bldr (first x) assignment))
                  t)))

(defthmd lemma-2-for-forcing-logic.appealp-of-clause.factor-bldr
  (implies (and (logic.appeal-listp (clause.factor-list-bldr x assignment))
                (force (consp (cdr x))))
           (equal (logic.appealp (clause.factor-bldr (second x) assignment))
                  t)))

(defthmd lemma-3-for-forcing-logic.appealp-of-clause.factor-bldr
  (implies (and (logic.appeal-listp (clause.factor-list-bldr x assignment))
                (force (consp (cdr (cdr x)))))
           (equal (logic.appealp (clause.factor-bldr (third x) assignment))
                  t)))

(defthmd lemma-1-for-forcing-logic.conclusion-of-clause.factor-bldr
  (implies (and (equal (logic.strip-conclusions (clause.factor-list-bldr x assignment))
                       (logic.por-list y z))
                (force (consp x)))
           (equal (logic.conclusion (clause.factor-bldr (first x) assignment))
                  (logic.por (first y) (first z))))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-2-for-forcing-logic.conclusion-of-clause.factor-bldr
  (implies (and (equal (logic.strip-conclusions (clause.factor-list-bldr x assignment))
                       (logic.por-list y z))
                (force (consp (cdr x))))
           (equal (logic.conclusion (clause.factor-bldr (second x) assignment))
                  (logic.por (second y) (second z))))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-3-for-forcing-logic.conclusion-of-clause.factor-bldr
  (implies (and (equal (logic.strip-conclusions (clause.factor-list-bldr x assignment))
                       (logic.por-list y z))
                (force (consp (cdr (cdr x)))))
           (equal (logic.conclusion (clause.factor-bldr (third x) assignment))
                  (logic.por (third y) (third z))))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))




(local (in-theory (enable lemma-forcing-memberp-of-pequal-a-nil-in-assignment-formulas
                          lemma-forcing-memberp-of-logic.pnot-pequal-a-nil-in-assignment-formulas)))

(local (in-theory (disable forcing-equal-of-logic.pequal-list-rewrite
                           forcing-equal-of-logic.por-list-rewrite)))

(defthms-flag
  :shared-hyp (force (and (consp assignment)
                          (logic.term-listp (domain assignment))))
  :thms ((term forcing-logic.appealp-of-clause.factor-bldr
               (implies (force (logic.termp x))
                        (equal (logic.appealp (clause.factor-bldr x assignment))
                               t)))
         (term forcing-logic.conclusion-of-clause.factor-bldr ;; BOZO backchain limit 0?
               (implies (force (logic.termp x))
                        (equal (logic.conclusion (clause.factor-bldr x assignment))
                               (logic.por (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment)))
                                          (logic.pequal x (clause.factor x assignment))))))
         (t forcing-logic.appeal-listp-of-clause.factor-list-bldr
            (implies (force (logic.term-listp x))
                     (equal (logic.appeal-listp (clause.factor-list-bldr x assignment))
                            t)))
         (t forcing-logic.strip-conclusions-of-clause.factor-list-bldr ;; BOZO backchain limit 0?
            (implies (force (logic.term-listp x))
                     (equal (logic.strip-conclusions (clause.factor-list-bldr x assignment))
                            (logic.por-list (repeat (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment))) (len x))
                                            (logic.pequal-list x (clause.factor-list x assignment)))))))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable definition-of-clause.factor-bldr
                              lemma-1-for-forcing-logic.appealp-of-clause.factor-bldr
                              lemma-2-for-forcing-logic.appealp-of-clause.factor-bldr
                              lemma-3-for-forcing-logic.appealp-of-clause.factor-bldr
                              lemma-1-for-forcing-logic.conclusion-of-clause.factor-bldr
                              lemma-2-for-forcing-logic.conclusion-of-clause.factor-bldr
                              lemma-3-for-forcing-logic.conclusion-of-clause.factor-bldr)
           :expand ((clause.factor-bldr x assignment)))))

(verify-guards clause.flag-factor-bldr)
(verify-guards clause.factor-bldr)
(verify-guards clause.factor-list-bldr)




(defthmd lemma-1-for-forcing-logic.proofp-of-clause.factor-bldr
  (implies (and (logic.proof-listp (clause.factor-list-bldr x assignment) axioms thms atbl)
                (force (consp x)))
           (equal (logic.proofp (clause.factor-bldr (first x) assignment) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-2-for-forcing-logic.proofp-of-clause.factor-bldr
  (implies (and (logic.proof-listp (clause.factor-list-bldr x assignment) axioms thms atbl)
                (force (consp (cdr x))))
           (equal (logic.proofp (clause.factor-bldr (second x) assignment) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthmd lemma-3-for-forcing-logic.proofp-of-clause.factor-bldr
  (implies (and (logic.proof-listp (clause.factor-list-bldr x assignment) axioms thms atbl)
                (force (consp (cdr (cdr x)))))
           (equal (logic.proofp (clause.factor-bldr (third x) assignment) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))



(defthms-flag
  :@contextp t
  :shared-hyp (force (and (consp assignment)
                          (logic.term-listp (domain assignment))
                          (logic.term-list-atblp (domain assignment) atbl)
                          (@obligations clause.factor-bldr)))
  :thms ((term forcing-logic.proofp-of-clause.factor-bldr
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)))
                        (equal (logic.proofp (clause.factor-bldr x assignment) axioms thms atbl)
                               t)))
         (t forcing-logic.proof-listp-of-clause.factor-list-bldr
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)))
                     (equal (logic.proof-listp (clause.factor-list-bldr x assignment) axioms thms atbl)
                            t))))
  :hints (("Goal"
           :induct (logic.term-induction flag x)
           :in-theory (enable definition-of-clause.factor-bldr
                              lemma-1-for-forcing-logic.proofp-of-clause.factor-bldr
                              lemma-2-for-forcing-logic.proofp-of-clause.factor-bldr
                              lemma-3-for-forcing-logic.proofp-of-clause.factor-bldr)
           :expand ((clause.factor-bldr x assignment)))))




(defund logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas (x)
  (declare (xargs :guard (and (mapp x)
                              (logic.term-listp (domain x))
                              (consp x))))
  (if (consp x)
      (let* ((binding-formula (binding-formula (car x)))
             (smartly-negated (if (equal (logic.fmtype binding-formula) 'pnot*)
                                  (logic.~arg binding-formula)
                                (logic.pnot binding-formula))))
        (if (consp (cdr x))
            (logic.por smartly-negated
                       (logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas (cdr x)))
          smartly-negated))
    nil))

(defthm logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas-removal
  (equal (logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas x)
         (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas x))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (e/d (logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas)
                          ((:executable-counterpart ACL2::force))))))




(defund clause.factor-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.factor-bldr)
         (not subproofs)
         (tuplep 2 extras)
         (let ((term       (first extras))
               (assignment (second extras)))
           (and (logic.termp term)
                (logic.term-atblp term atbl)
                (consp assignment)
                (mapp assignment)
                (let ((domain (fast-domain$ assignment nil)))
                  (and (logic.term-listp domain)
                       (logic.term-list-atblp domain atbl)))
                (equal conclusion
                       (logic.por (logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas assignment)
                                  (logic.pequal term (clause.factor term assignment)))))))))

(defund clause.factor-bldr-high (x assignment)
  (declare (xargs :guard (and (logic.termp x)
                              (consp assignment)
                              (mapp assignment)
                              (logic.term-listp (domain assignment)))))
  (logic.appeal 'clause.factor-bldr
                (logic.por (logic.disjoin-formulas-of-smart-negate-formulas-of-assignment-formulas assignment)
                           (logic.pequal x (clause.factor x assignment)))
                nil
                (list x assignment)))

(defobligations clause.factor-bldr-okp
  (clause.factor-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.factor-bldr-okp)))

 (defthm booleanp-of-clause.factor-bldr-okp
   (equal (booleanp (clause.factor-bldr-okp x atbl))
          t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.factor-bldr-okp-of-logic.appeal-identity
   (equal (clause.factor-bldr-okp (logic.appeal-identity x) atbl)
          (clause.factor-bldr-okp x atbl))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-clause.factor-bldr-okp
   (implies (and (clause.factor-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (clause.factor-bldr (first (logic.extras x))
                                                         (second (logic.extras x))))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.factor-bldr-okp
   (implies (and (clause.factor-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.factor-bldr-okp))
            (equal (logic.proofp (clause.factor-bldr (first (logic.extras x))
                                                     (second (logic.extras x)))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.factor-bldr-okp
   (implies (and (clause.factor-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.factor-bldr-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.factor-bldr-okp
                               lemma-2-for-soundness-of-clause.factor-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.factor-bldr (first (logic.extras x))
                                                    (second (logic.extras x))))))))))


