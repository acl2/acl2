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
(include-book "limlift")
(include-book "casesplit-bldr")
(include-book "../update-clause-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund clause.limlift-term1-bldr (x k)
  (declare (xargs :guard (and (logic.termp x)
                              (natp k))
                  :verify-guards nil))
  (cond ((logic.constantp x)
         (cons (build.reflexivity x) k))
        ((logic.variablep x)
         (cons (build.reflexivity x) k))
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (cond ((and (equal name 'if)
                       (equal (len args) 3))
                  (let* ((lift-first  (clause.limlift-term1-bldr (first args) k))
                         (lift-second (clause.limlift-term1-bldr (second args) (cdr lift-first)))
                         (lift-third  (clause.limlift-term1-bldr (third args) (cdr lift-second))))
                    (cons (build.pequal-by-args 'if (list (car lift-first) (car lift-second) (car lift-third)))
                          (cdr lift-third))))
                 ((clause.simple-term-listp args)
                  (cons (build.reflexivity x) k))
                 (t
                  (let* ((tests    (clause.simple-tests x))
                         (numtests (fast-len tests 0)))
                    (if (<= numtests k)
                        (cons (clause.cases-bldr x tests nil) (- k numtests))
                      (cons (clause.cases-bldr x (firstn k tests) nil) 0)))))))
        ((logic.lambdap x)
         (let ((actuals (logic.lambda-actuals x)))
           (if (clause.simple-term-listp actuals)
               (cons (build.reflexivity x) k)
             (let* ((tests    (clause.simple-tests x))
                    (numtests (fast-len tests 0)))
               (if (<= numtests k)
                   (cons (clause.cases-bldr x tests nil) (- k numtests))
                 (cons (clause.cases-bldr x (firstn k tests) nil) 0))))))
        (t
         (cons nil k))))

(defobligations clause.limlift-term1-bldr
  (build.reflexivity
   build.pequal-by-args
   clause.cases-bldr))

(defthm cdr-of-clause.limlift-term1-bldr
  (equal (cdr (clause.limlift-term1-bldr x k))
         (cdr (clause.limlift-term1 x k)))
  :hints(("Goal"
          :expand ((clause.limlift-term1-bldr x k)
                   (clause.limlift-term1 x k))
          :in-theory (enable clause.limlift-term1-bldr)
          :induct (clause.limlift-term1-bldr x k))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (logic.termp x)
                   (and (logic.appealp (car (clause.limlift-term1-bldr x k)))
                        (equal (logic.conclusion (car (clause.limlift-term1-bldr x k)))
                               (logic.pequal x (car (clause.limlift-term1 x k))))))
          :hints(("Goal"
                  :expand ((clause.limlift-term1-bldr x k)
                           (clause.limlift-term1 x k))
                  :in-theory (enable clause.limlift-term1-bldr)
                  :induct (clause.limlift-term1-bldr x k)))))

 (defthm forcing-logic.appealp-of-car-of-clause.limlift-term1-bldr
   (implies (force (logic.termp x))
            (equal (logic.appealp (car (clause.limlift-term1-bldr x k)))
                   t)))

 (defthm forcing-logic.conclusion-of-car-of-clause.limlift-term1-bldr
   (implies (force (logic.termp x))
            (equal (logic.conclusion (car (clause.limlift-term1-bldr x k)))
                   (logic.pequal x (car (clause.limlift-term1 x k)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(verify-guards clause.limlift-term1-bldr)

(defthm@ forcing-logic.proofp-of-car-of-clause.limlift-term1-bldr
  (implies (force (and (logic.termp x)
                       ;; ---
                       (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.limlift-term1-bldr)))
           (equal (logic.proofp (car (clause.limlift-term1-bldr x k)) axioms thms atbl)
                  t))
  :hints(("Goal"
          :expand (clause.limlift-term1-bldr x k)
          :in-theory (enable clause.limlift-term1-bldr)
          :induct (clause.limlift-term1-bldr x k))))




(defund clause.limlift-term-bldr (x k)
  (declare (xargs :guard (and (logic.termp x)
                              (natp k))
                  :verify-guards nil
                  :measure (nfix k)))
  (cond ((zp k)
         (build.reflexivity x))
        ((clause.lifted-termp x)
         (build.reflexivity x))
        (t
         (let* ((lift1       (clause.limlift-term1-bldr x k))
                (lift1-proof (car lift1))
                (lift1-k     (cdr lift1))
                (lift1-rhs   (logic.=rhs (logic.conclusion lift1-proof))))
           (build.transitivity-of-pequal lift1-proof
                                         (clause.limlift-term-bldr lift1-rhs lift1-k))))))

(defobligations clause.limlift-term-bldr
  (clause.limlift-term1-bldr
   build.transitivity-of-pequal
   build.reflexivity))

(encapsulate
 ()
 (local (defthm lemma
          (implies (logic.termp x)
                   (and (logic.appealp (clause.limlift-term-bldr x k))
                        (equal (logic.conclusion (clause.limlift-term-bldr x k))
                               (logic.pequal x (clause.limlift-term x k)))))
          :hints(("Goal" :in-theory (enable clause.limlift-term-bldr clause.limlift-term)))))

 (defthm forcing-logic.appealp-of-clause.limlift-term-bldr
   (implies (force (logic.termp x))
            (equal (logic.appealp (clause.limlift-term-bldr x k))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.limlift-term-bldr
   (implies (force (logic.termp x))
            (equal (logic.conclusion (clause.limlift-term-bldr x k))
                   (logic.pequal x (clause.limlift-term x k))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(verify-guards clause.limlift-term-bldr)

(defthm@ forcing-logic.proofp-of-clause.limlift-term-bldr
  (implies (force (and (logic.termp x)
                       (logic.term-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.limlift-term-bldr)))
           (equal (logic.proofp (clause.limlift-term-bldr x k) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term-bldr))))




(defprojection
  :list (clause.limlift-term-list-bldr x k)
  :element (clause.limlift-term-bldr x k)
  :guard (and (logic.term-listp x)
              (natp k)))

(defobligations clause.limlift-term-list-bldr
  (clause.limlift-term-bldr))

(defthm forcing-logic.appeal-listp-of-clause.limlift-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.appeal-listp (clause.limlift-term-list-bldr x k))
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term-list-bldr))))

(defthm forcing-logic.strip-conclusions-of-clause.limlift-term-list-bldr
  (implies (force (logic.term-listp x))
           (equal (logic.strip-conclusions (clause.limlift-term-list-bldr x k))
                  (logic.pequal-list x (clause.limlift-term-list x k))))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable clause.limlift-term-list-bldr))))

(defthm@ forcing-logic.proof-listp-of-clause.limlift-term-list-bldr
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.limlift-term-list-bldr)))
           (equal (logic.proof-listp (clause.limlift-term-list-bldr x k) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.limlift-term-list-bldr))))



(defun clause.limlift-clauses-bldr (x limit proofs)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x)
                              (natp limit)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (clause.limlift-term-list-list x limit))))))
  (if (consp x)
      (let* ((lift-proofs  (clause.limlift-term-list-bldr (car x) limit))
             (lift-terms   (clause.limlift-term-list (car x) limit))
             (update-proof (clause.update-clause-bldr lift-terms (car proofs) lift-proofs)))
        (ACL2::prog2$
         (ACL2::cw! ";; Limlift step: ~s0~|"
                    (STR::ncat "Input " (unbounded-rank (car proofs))
                              "; Lift " (unbounded-rank lift-proofs)
                              "; Update " (- (unbounded-rank update-proof)
                                             (ACL2::+ (unbounded-rank lift-proofs)
                                                      (unbounded-rank (car proofs))))
                              "; Output " (unbounded-rank update-proof)))
         (cons update-proof
               (clause.limlift-clauses-bldr (cdr x) limit (cdr proofs)))))
    nil))

(defobligations clause.limlift-clauses-bldr
  (clause.limlift-term-list-bldr
   clause.update-clause-bldr))

(encapsulate
 ()
 (assume (force (and (logic.term-list-listp x)
                     (cons-listp x)
                     (natp limit)
                     (logic.appeal-listp proofs)
                     (equal (logic.strip-conclusions proofs)
                            (clause.clause-list-formulas (clause.limlift-term-list-list x limit))))))

 (conclude forcing-logic.appeal-listp-of-clause.limlift-clauses-bldr
           (equal (logic.appeal-listp (clause.limlift-clauses-bldr x limit proofs))
                  t))

 (conclude forcing-logic.strip-conclusions-of-clause.limlift-clauses-bldr
           (equal (logic.strip-conclusions (clause.limlift-clauses-bldr x limit proofs))
                  (clause.clause-list-formulas x))
           :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-clause.limlift-clauses-bldr
   (implies (force (and (logic.term-list-listp x)
                        (cons-listp x)
                        (natp limit)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (clause.limlift-term-list-list x limit)))
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.term-list-list-atblp x atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.limlift-clauses-bldr)))
            (equal (logic.proof-listp (clause.limlift-clauses-bldr x limit proofs) axioms thms atbl)
                   t))))