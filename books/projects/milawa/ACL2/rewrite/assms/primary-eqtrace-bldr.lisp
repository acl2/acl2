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
(include-book "eqtrace-okp")
(include-book "../../clauses/basic-bldrs")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defderiv rw.primary-eqtrace-nhyp-bldr-lemma-1
  :derive (v (!= (equal (? a) (? b)) nil) (!= (? nhyp) nil))
  :from   ((proof x (= (? nhyp) (not (equal (? a) (? b))))))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))                                             (build.theorem (theorem-not-when-nil)))
           ((v (!= (equal (? a) (? b)) nil) (= (not (equal (? a) (? b))) t))         (build.instantiation @- (@sigma (x . (equal (? a) (? b))))) *1)
           ((= (? nhyp) (not (equal (? a) (? b))))                                   (@given x))
           ((v (!= (equal (? a) (? b)) nil) (= (? nhyp) (not (equal (? a) (? b)))))  (build.expansion (@formula (!= (equal (? a) (? b)) nil)) @-))
           ((v (!= (equal (? a) (? b)) nil) (= (? nhyp) t))                          (build.disjoined-transitivity-of-pequal @- *1))
           ((v (!= (equal (? a) (? b)) nil) (!= (? nhyp) nil))                       (build.disjoined-not-nil-from-t @-))))

(defderiv rw.primary-eqtrace-nhyp-bldr-lemma-2
  :derive (v (!= (? nhyp) nil) (= (equal (? a) (? b)) t))
  :from   ((proof x (= (? nhyp) (not (equal (? a) (? b))))))
  :proof  (@derive
           ((= (? nhyp) (not (equal (? a) (? b))))                                   (@given x))
           ((v (!= (equal (? a) (? b)) nil) (!= (? nhyp) nil))                       (rw.primary-eqtrace-nhyp-bldr-lemma-1 @-))
           ((v (!= (? nhyp) nil) (!= (equal (? a) (? b)) nil))                       (build.commute-or @-))
           ((v (!= (? nhyp) nil) (= (equal (? a) (? b)) t))                          (build.disjoined-equal-t-from-not-nil @-))))

(defund@ rw.primary-eqtrace-nhyp-bldr (nhyp x)
  ;; Given an nhyp that matches a primary eqtrace, prove:
  ;;   nhyp != nil v (equal lhs rhs) = t
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.eqtracep x)
                              (equal (rw.primary-eqtrace t nhyp) x))
                  :verify-guards nil))
  ;; Let nhyp be (not* (equal a b)).
  (let* ((guts (clause.negative-term-guts nhyp))
         (args (logic.function-args guts))
         (a    (first args))
         (main-proof (@derive
                      ((= nhyp (not (equal a b)))                           (clause.standardize-negative-term-bldr nhyp))
                      ((v (!= nhyp nil) (= (equal a b) t))                  (rw.primary-eqtrace-nhyp-bldr-lemma-2 @-)))))
    (if (equal a (rw.eqtrace->lhs x))
        main-proof
      (build.disjoined-commute-equal main-proof))))

(defobligations rw.primary-eqtrace-nhyp-bldr
  (clause.standardize-negative-term-bldr
   rw.primary-eqtrace-nhyp-bldr-lemma-2
   build.disjoined-commute-equal))

(encapsulate
 ()
 (local (in-theory (enable rw.primary-eqtrace
                           rw.primary-eqtrace-nhyp-bldr
                           theorem-not-when-nil
                           logic.term-formula)))

 (local (in-theory (disable forcing-equal-of-logic.pequal-rewrite-two
                            forcing-equal-of-logic.pequal-rewrite
                            forcing-equal-of-logic.por-rewrite-two
                            forcing-equal-of-logic.por-rewrite
                            forcing-equal-of-logic.pnot-rewrite-two
                            forcing-equal-of-logic.pnot-rewrite)))

 (defthm rw.primary-eqtrace-nhyp-bldr-under-iff
   (iff (rw.primary-eqtrace-nhyp-bldr nhyp x)
        t))

 (defthm forcing-logic.appealp-of-rw.primary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.primary-eqtrace t nhyp) x)))
            (equal (logic.appealp (rw.primary-eqtrace-nhyp-bldr nhyp x))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.primary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.primary-eqtrace t nhyp) x)))
            (equal (logic.conclusion (rw.primary-eqtrace-nhyp-bldr nhyp x))
                   (logic.por (logic.term-formula nhyp)
                              (logic.pequal (logic.function 'equal
                                                            (list (rw.eqtrace->lhs x)
                                                                  (rw.eqtrace->rhs x)))
                                            ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.primary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.primary-eqtrace t nhyp) x)
                        ;; ---
                        (logic.term-atblp nhyp atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations rw.primary-eqtrace-nhyp-bldr)))
            (equal (logic.proofp (rw.primary-eqtrace-nhyp-bldr nhyp x) axioms thms atbl)
                   t)))

 (verify-guards rw.primary-eqtrace-nhyp-bldr))


(defund rw.primary-eqtrace-bldr (x box)
  ;; Given a primary eqtrace that is box-okp, prove
  ;;   hypbox-formula v (equal lhs rhs) = t
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.primary-eqtrace-okp x box))
                  :verify-guards nil))
  (let* ((left      (rw.hypbox->left box))
         (right     (rw.hypbox->right box))
         (nhyp-left (rw.find-nhyp-for-primary-eqtracep left x)))
    ;; First search for a working hyp on the left.
    (if nhyp-left
        ;; 1. nhyp-left v (equal lhs rhs) = t      Primary eqtrace nhyp bldr
        ;; 2. Left v (equal lhs rhs) = t           Multi assoc expansion
        (let* ((line-1 (rw.primary-eqtrace-nhyp-bldr nhyp-left x))
               (line-2 (build.multi-assoc-expansion line-1 (logic.term-list-formulas left))))
          (if right
              ;; 3. Left v (Right v (equal lhs rhs) = t)    DJ Left Expansion
              ;; 4. (Left v Right) v (equal lhs rhs) = t    Associativity
              (build.associativity (build.disjoined-left-expansion line-2 (clause.clause-formula right)))
            ;; Else we're done already
            line-2))
      ;; Else we know there must be a matching hyp on the right, since our guard
      ;; requires we are a box-okp primary eqtrace.
      ;;
      ;; 1. nhyp-right v (equal lhs rhs) = t       Primary eqtrace nhyp bldr
      ;; 2. Right v (equal lhs rhs) = t            Multi assoc expansion.
      (let* ((nhyp-right (rw.find-nhyp-for-primary-eqtracep right x))
             (line-1 (rw.primary-eqtrace-nhyp-bldr nhyp-right x))
             (line-2 (build.multi-assoc-expansion line-1 (logic.term-list-formulas right))))
        (if left
            ;; 3. Left v (Right v (equal lhs rhs) = t)    Expansion
            ;; 4. (Left v Right) v (equal lhs rhs) = t    Associativity
            (build.associativity
             (build.expansion (clause.clause-formula left) line-2))
          ;; Else we're done already.
          line-2)))))

(defobligations rw.primary-eqtrace-bldr
  (rw.primary-eqtrace-nhyp-bldr
   build.multi-assoc-expansion
   build.disjoined-left-expansion))

(encapsulate
 ()
 (local (in-theory (enable rw.primary-eqtrace-bldr
                           rw.primary-eqtrace-okp
                           rw.hypbox-formula
                           rw.eqtrace-formula
                           )))

 (defthm rw.primary-eqtrace-bldr-under-iff
   (iff (rw.primary-eqtrace-bldr x box)
        t))

 (defthm forcing-logic.appealp-of-rw.primary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.primary-eqtrace-okp x box)))
            (equal (logic.appealp (rw.primary-eqtrace-bldr x box))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.primary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.primary-eqtrace-okp x box)))
            (equal (logic.conclusion (rw.primary-eqtrace-bldr x box))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.primary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.primary-eqtrace-okp x box)
                        ;; ---
                        (equal (cdr (lookup 'not atbl)) 1)
                        (rw.hypbox-atblp box atbl)
                        (@obligations rw.primary-eqtrace-bldr)))
            (equal (logic.proofp (rw.primary-eqtrace-bldr x box) axioms thms atbl)
                   t)))

 (verify-guards rw.primary-eqtrace-bldr))


