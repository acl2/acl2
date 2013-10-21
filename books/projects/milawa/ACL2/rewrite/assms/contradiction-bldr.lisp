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
(include-book "contradictionp")
(include-book "eqtrace-compiler")
(include-book "../../clauses/basic-bldrs")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(deftheorem theorem-inequality-of-not-x-and-x
  :derive (!= (not x) x)
  :proof  (@derive
           ((v (= x nil) (= (if x y z) y))       (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= (if x nil t) nil))   (build.instantiation @- (@sigma (y . nil) (z . t)))   *1a)
           ((v (!= nil x) (= nil x))             (build.propositional-schema (@formula (= nil x))))
           ((v (!= nil x) (= x nil))             (build.disjoined-commute-pequal @-))
           ((v (= x nil) (!= nil x))             (build.commute-or @-))
           ((v (= x nil) (!= (if x nil t) x))    (build.disjoined-substitute-into-not-pequal @- *1a)   *1)
           ;; ---
           ((v (!= x nil) (= (if x y z) z))      (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= (if x nil t) t))    (build.instantiation @- (@sigma (y . nil) (z . t)))   *2a)
           ((v (!= x nil) (= x nil))             (build.propositional-schema (@formula (= x nil))))
           ((v (!= x nil) (!= x t))              (build.disjoined-not-t-from-nil @-))
           ((v (!= x nil) (!= t x))              (build.disjoined-commute-not-pequal @-))
           ((v (!= x nil) (!= (if x nil t) x))   (build.disjoined-substitute-into-not-pequal @- *2a)   *2)
           ;; ---
           ((v (!= (if x nil t) x)
               (!= (if x nil t) x))              (build.cut *1 *2))
           ((!= (if x nil t) x)                  (build.contraction @-))
           ((= (not x) (if x nil t))             (build.axiom (definition-of-not)))
           ((!= (not x) x)                       (build.substitute-into-not-pequal @-- @-)))
  :minatbl ((not . 1)
            (if . 3)))

(deftheorem theorem-not-x-and-x-under-iff
  :derive (= (iff (not x) x) nil)
  :proof  (@derive
           ((= (iff x y) (if x (if y t nil) (if y nil t)))                             (build.axiom (definition-of-iff)))
           ((= (iff (not x) x) (if (not x) (if x t nil) (if x nil t)))                 (build.instantiation @- (@sigma (x . (not x)) (y . x)))                        *0)
           ;; ---
           ((v (!= x nil) (= (not x) t))                                               (build.theorem (theorem-not-when-nil))                                         *1a)
           ((v (!= x nil) (= (if x y z) z))                                            (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= (if x t nil) nil))                                        (build.instantiation @- (@sigma (y . t) (z . nil)))                            *1b)
           ((v (!= x nil) (= (if x nil t) t))                                          (build.instantiation @-- (@sigma (y . nil) (z . t)))                           *1c)
           ((v (!= x nil) (= (if (not x) (if x t nil) (if x nil t)) (if t nil t)))     (build.disjoined-pequal-by-args 'if (@formula (!= x nil)) (list *1a *1b *1c))  *1d)
           ((= (if t y z) y)                                                           (build.theorem (theorem-if-redux-t)))
           ((= (if t nil t) nil)                                                       (build.instantiation @- (@sigma (y . nil) (z . t))))
           ((v (!= x nil) (= (if t nil t) nil))                                        (build.expansion (@formula (!= x nil)) @-))
           ((v (!= x nil) (= (if (not x) (if x t nil) (if x nil t)) nil))              (build.disjoined-transitivity-of-pequal *1d @-))
           ((v (!= x nil) (= (iff (not x) x) (if (not x) (if x t nil) (if x nil t))))  (build.expansion (@formula (!= x nil)) *0))
           ((v (!= x nil) (= (iff (not x) x) nil))                                     (build.disjoined-transitivity-of-pequal @- @--)                                *1)
           ;; ---
           ((v (= x nil) (= (not x) nil))                                              (build.theorem (theorem-not-when-not-nil))                                     *2a)
           ((v (= x nil) (= (if x y z) y))                                             (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= (if x t nil) t))                                           (build.instantiation @- (@sigma (y . t) (z . nil)))                            *2b)
           ((v (= x nil) (= (if x nil t) nil))                                         (build.instantiation @-- (@sigma (y . nil) (z . t)))                           *2c)
           ((v (= x nil) (= (if (not x) (if x t nil) (if x nil t)) (if nil t nil)))    (build.disjoined-pequal-by-args 'if (@formula (= x nil)) (list *2a *2b *2c))   *2d)
           ((= (if nil y z) z)                                                         (build.theorem (theorem-if-redux-nil)))
           ((= (if nil t nil) nil)                                                     (build.instantiation @- (@sigma (y . t) (z . nil))))
           ((v (= x nil) (= (if nil t nil) nil))                                       (build.expansion (@formula (= x nil)) @-))
           ((v (= x nil) (= (if (not x) (if x t nil) (if x nil t)) nil))               (build.disjoined-transitivity-of-pequal *2d @-))
           ((v (= x nil) (= (iff (not x) x) (if (not x) (if x t nil) (if x nil t))))   (build.expansion (@formula (= x nil)) *0))
           ((v (= x nil) (= (iff (not x) x) nil))                                      (build.disjoined-transitivity-of-pequal @- @--)                                *2)
           ;; ---
           ((v (= (iff (not x) x) nil) (= (iff (not x) x) nil))                        (build.cut *2 *1))
           ((= (iff (not x) x) nil)                                                    (build.contraction @-)))
  :minatbl ((iff . 2)
            (not . 1)
            (if . 3)))

(deftheorem rw.eqtrace-contradiction-lemma1
  :derive (!= (iff nil t) t)
  :proof  (@derive
           ((v (!= x nil) (= (iff x t) nil))      (build.theorem (theorem-iff-t-when-nil)))
           ((v (!= nil nil) (= (iff nil t) nil))  (build.instantiation @- (@sigma (x . nil))))
           ((= nil nil)                           (build.reflexivity (@term nil)))
           ((= (iff nil t) nil)                   (build.modus-ponens @- @--))
           ((!= (iff nil t) t)                    (build.not-t-from-nil @-)))
  :minatbl ((iff . 2)))

(defund@ rw.eqtrace-contradiction-lemma2 (lhs rhs)
  (declare (xargs :guard (and (logic.termp lhs)
                              (logic.termp rhs)
                              (clause.negative-termp rhs)
                              (equal (clause.negative-term-guts rhs) lhs))
                  :verify-guards nil))
  (@derive ((= lhs lhs)                            (build.reflexivity lhs))
           ((= rhs (not lhs))                      (clause.standardize-negative-term-bldr rhs))
           ((= (iff rhs lhs) (iff (not lhs) lhs))  (build.pequal-by-args 'iff (list @- @--))                    *1)
           ((= (iff (not x) x) nil)                (build.theorem (theorem-not-x-and-x-under-iff)))
           ((= (iff (not lhs) lhs) nil)            (build.instantiation @- (list (cons 'x lhs))))
           ((= (iff rhs lhs) nil)                  (build.transitivity-of-pequal *1 @-)                         *2)
           ((= (iff x y) (iff y x))                (build.theorem (theorem-symmetry-of-iff)))
           ((= (iff lhs rhs) (iff rhs lhs))        (build.instantiation @- (list (cons 'x lhs) (cons 'y rhs))))
           ((= (iff lhs rhs) nil)                  (build.transitivity-of-pequal @- *2))
           ((!= (iff lhs rhs) t)                   (build.not-t-from-nil @-))))

(defobligations rw.eqtrace-contradiction-lemma2
  (build.reflexivity
   clause.standardize-negative-term-bldr
   build.pequal-by-args
   build.transitivity-of-pequal
   build.not-t-from-nil)
  :extra-thms ((theorem-not-x-and-x-under-iff)
               (theorem-symmetry-of-iff)))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-contradiction-lemma2
                           theorem-not-x-and-x-under-iff
                           theorem-symmetry-of-iff)))

 (defthm rw.eqtrace-contradiction-lemma2-under-iff
   (iff (rw.eqtrace-contradiction-lemma2 lhs rhs)
        t))

 (defthm forcing-logic.appealp-of-rw.eqtrace-contradiction-lemma2
   (implies (force (and (logic.termp lhs)
                        (logic.termp rhs)
                        (clause.negative-termp rhs)
                        (equal (clause.negative-term-guts rhs) lhs)))
            (equal (logic.appealp (rw.eqtrace-contradiction-lemma2 lhs rhs))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.eqtrace-contradiction-lemma2
   (implies (force (and (logic.termp lhs)
                        (logic.termp rhs)
                        (clause.negative-termp rhs)
                        (equal (clause.negative-term-guts rhs) lhs)))
            (equal (logic.conclusion (rw.eqtrace-contradiction-lemma2 lhs rhs))
                   (logic.pnot (logic.pequal (logic.function 'iff (list lhs rhs)) ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.eqtrace-contradiction-lemma2
   (implies (force (and (logic.termp lhs)
                        (logic.termp rhs)
                        (clause.negative-termp rhs)
                        (equal (clause.negative-term-guts rhs) lhs)
                        ;; --
                        (logic.term-atblp lhs atbl)
                        (logic.term-atblp rhs atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.eqtrace-contradiction-lemma2)))
            (equal (logic.proofp (rw.eqtrace-contradiction-lemma2 lhs rhs) axioms thms atbl)
                   t)))

 (verify-guards rw.eqtrace-contradiction-lemma2))




(defderiv rw.eqtrace-contradiction-bldr-lemma3a
  :derive (!= (equal (? lhs) (? rhs)) t)
  :from   ((proof x (= (? rhs) (not (? lhs)))))
  :proof  (@derive
           ((!= (not x) x)                                (build.theorem (theorem-inequality-of-not-x-and-x)))
           ((!= (not (? lhs)) (? lhs))                    (build.instantiation @- (@sigma (x . (? lhs)))))
           ((= (? rhs) (not (? lhs)))                     (@given x))
           ((!= (? rhs) (? lhs))                          (build.substitute-into-not-pequal @-- @-))
           ((!= (? lhs) (? rhs))                          (build.commute-not-pequal @-))
           ((= (equal (? lhs) (? rhs)) nil)               (build.not-equal-from-not-pequal @-))
           ((!= (equal (? lhs) (? rhs)) t)                (build.not-t-from-nil @-)))
  :minatbl ((equal . 2)))

(defderiv rw.eqtrace-contradiction-bldr-lemma3
  :derive P
  :from   ((proof x (v P (= (equal (? lhs) (? rhs)) t)))
           (proof y (= (? rhs) (not (? lhs)))))
  :proof (@derive
          ((v P (= (equal (? lhs) (? rhs)) t))           (@given x))
          ((v (= (equal (? lhs) (? rhs)) t) P)           (build.commute-or @-) *1)
          ((= (? rhs) (not (? lhs)))                     (@given y))
          ((!= (equal (? lhs) (? rhs)) t)                (rw.eqtrace-contradiction-bldr-lemma3a @-))
          (P                                             (build.modus-ponens-2 @- *1))))


(defund@ rw.eqtrace-contradiction-bldr (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.eqtrace-contradictionp x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box))
                  :verify-guards nil))
  (let ((lhs  (rw.eqtrace->lhs x))
        (rhs  (rw.eqtrace->rhs x))
        (iffp (rw.eqtrace->iffp x)))
    (cond ((and iffp
                (equal lhs ''nil)
                (equal rhs ''t))
           (@derive
            ((v hyps (= (iff nil t) t))            (rw.eqtrace-bldr x box))
            ((v (= (iff nil t) t) hyps)            (build.commute-or @-))
            ((!= (iff nil t) t)                    (build.theorem (rw.eqtrace-contradiction-lemma1)))
            (hyps                                  (build.modus-ponens-2 @- @--))))
          ((and (not iffp)
                (logic.constantp lhs)
                (logic.constantp rhs)
                (not (equal lhs rhs)))
           (@derive
            ((v hyps (= (equal lhs rhs) t))        (rw.eqtrace-bldr x box))
            ((v (= (equal lhs rhs) t) hyps)        (build.commute-or @-) *1)
            ((= (equal lhs rhs) nil)               (build.base-eval (logic.function 'equal (list lhs rhs))))
            ((!= (equal lhs rhs) t)                (build.not-t-from-nil @-))
            ;((!= lhs rhs)                          (build.not-pequal-constants lhs rhs))
            ;((= (equal lhs rhs) nil)               (build.not-equal-from-not-pequal @-))
            ;((!= (equal lhs rhs) t)                (build.not-t-from-nil @-))
            (hyps                                  (build.modus-ponens-2 @- *1))))
          (iffp
           ;; The trace is (iff x (not* x)) = t
           (@derive
            ((v hyps (= (iff lhs rhs) t))           (rw.eqtrace-bldr x box))
            ((v (= (iff lhs rhs) t) hyps)           (build.commute-or @-)                                        *0)
            ((!= (iff lhs rhs) t)                   (rw.eqtrace-contradiction-lemma2 lhs rhs))
            (hyps                                   (build.modus-ponens-2 @- *0))))
          (t
           ;; The trace is (equal x (not* x)) = t
           (@derive
            ((v hyps (= (equal lhs rhs) t))        (rw.eqtrace-bldr x box))
            ((= rhs (not lhs))                     (clause.standardize-negative-term-bldr rhs))
            (hyps                                  (rw.eqtrace-contradiction-bldr-lemma3 @-- @-)))))))

(defobligations rw.eqtrace-contradiction-bldr
 (rw.eqtrace-bldr
   build.commute-or
   build.modus-ponens-2
   build.base-eval
   ;build.not-pequal-constants
   ;build.not-equal-from-not-pequal
   build.not-t-from-nil
   rw.eqtrace-contradiction-lemma2
   rw.eqtrace-contradiction-bldr-lemma3)
  :extra-thms ((rw.eqtrace-contradiction-lemma1)))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-contradictionp
                           rw.eqtrace-contradiction-bldr
                           rw.eqtrace-formula
                           rw.eqtrace-contradiction-lemma1)))

 (defthm rw.eqtrace-contradiction-bldr-under-iff
   (iff (rw.eqtrace-contradiction-bldr x box)
        t))

 (defthm forcing-logic.appealp-of-rw.eqtrace-contradiction-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.eqtrace-contradictionp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)))
            (equal (logic.appealp (rw.eqtrace-contradiction-bldr x box))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.eqtrace-contradiction-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.eqtrace-contradictionp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)))
            (equal (logic.conclusion (rw.eqtrace-contradiction-bldr x box))
                   (rw.hypbox-formula box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.eqtrace-contradiction-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.eqtrace-contradictionp x)
                        (rw.hypboxp box)
                        (rw.eqtrace-okp x box)
                        ;; ---
                        (rw.eqtrace-atblp x atbl)
                        (rw.hypbox-atblp box atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.eqtrace-contradiction-bldr)))
            (equal (logic.proofp (rw.eqtrace-contradiction-bldr x box) axioms thms atbl)
                   t)))

 (verify-guards rw.eqtrace-contradiction-bldr))



(defund rw.eqtrace-contradiction-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'rw.eqtrace-contradiction-bldr)
         (tuplep 2 extras)
         (let ((trace (first extras))
               (box   (second extras)))
           (and (rw.eqtracep trace)
                (rw.eqtrace-contradictionp trace)
                (rw.eqtrace-atblp trace atbl)
                (rw.hypboxp box)
                (rw.hypbox-atblp box atbl)
                (rw.eqtrace-okp trace box)
                (equal conclusion (rw.hypbox-formula box))
                (not subproofs))))))

(defund rw.eqtrace-contradiction-bldr-high (x box)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.eqtrace-contradictionp x)
                              (rw.hypboxp box)
                              (rw.eqtrace-okp x box))))
  (logic.appeal 'rw.eqtrace-contradiction-bldr
                (rw.hypbox-formula box)
                nil
                (list x box)))

(defobligations rw.eqtrace-contradiction-bldr-okp
  (rw.eqtrace-contradiction-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.eqtrace-contradiction-bldr-okp)))

 (defthm booleanp-of-rw.eqtrace-contradiction-bldr-okp
   (equal (booleanp (rw.eqtrace-contradiction-bldr-okp x atbl))
          t))

 (defthm rw.eqtrace-contradiction-bldr-okp-of-logic.appeal-identity
   (equal (rw.eqtrace-contradiction-bldr-okp (logic.appeal-identity x) atbl)
          (rw.eqtrace-contradiction-bldr-okp x atbl)))

 (local (in-theory (enable backtracking-logic.formula-atblp-rules)))
 (local (in-theory (disable forcing-logic.formula-atblp-rules
                            forcing-lookup-of-logic.function-name-free
                            forcing-logic.term-list-atblp-of-logic.function-args)))

 (defthm lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp
   (implies (and (rw.eqtrace-contradiction-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (rw.eqtrace-contradiction-bldr (first (logic.extras x))
                                                   (second (logic.extras x))))
                   (logic.conclusion x))))

 (defthm@ lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp
   (implies (and (rw.eqtrace-contradiction-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 ;; ---
                 (@obligations rw.eqtrace-contradiction-bldr-okp)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'equal atbl)) 2))
            (equal (logic.proofp
                    (rw.eqtrace-contradiction-bldr (first (logic.extras x))
                                                   (second (logic.extras x)))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-rw.eqtrace-contradiction-bldr-okp
   (implies (and (rw.eqtrace-contradiction-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)))
                 ;; ---
                 (@obligations rw.eqtrace-contradiction-bldr-okp)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'equal atbl)) 2))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-rw.eqtrace-contradiction-bldr-okp
                               lemma-2-for-soundness-of-rw.eqtrace-contradiction-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (rw.eqtrace-contradiction-bldr (first (logic.extras x))
                                                               (second (logic.extras x))))))))))




;; (defund@ rw.eqtrace-contradiction-bldr-alt (x box)
;;   (declare (xargs :guard (and (rw.eqtracep x)
;;                               (rw.eqtrace-contradictionp x)
;;                               (rw.hypboxp box)
;;                               (rw.eqtrace-okp x box))
;;                   :verify-guards nil))
;;   (let ((lhs  (rw.eqtrace->lhs x))
;;         (rhs  (rw.eqtrace->rhs x))
;;         (iffp (rw.eqtrace->iffp x)))
;;     (cond ((and iffp
;;                 (equal lhs ''nil)
;;                 (equal rhs ''t))
;;            (@derive
;;             ((v hyps (= (iff nil t) t))            (rw.eqtrace-bldr x box))
;;             ((v (= (iff nil t) t) hyps)            (build.commute-or @-))
;;             ((!= (iff nil t) t)                    (build.theorem (rw.eqtrace-contradiction-lemma1)))
;;             (hyps                                  (build.modus-ponens-2 @- @--))))
;;           ((and (not iffp)
;;                 (logic.constantp lhs)
;;                 (logic.constantp rhs)
;;                 (not (equal lhs rhs)))
;;            (@derive
;;             ((v hyps (= (equal lhs rhs) t))        (rw.eqtrace-bldr x box))
;;             ((v (= (equal lhs rhs) t) hyps)        (build.commute-or @-) *1)
;;             ((!= lhs rhs)                          (build.not-pequal-constants lhs rhs))
;;             ((= (equal lhs rhs) nil)               (build.not-equal-from-not-pequal @-))
;;             ((!= (equal lhs rhs) t)                (build.not-t-from-nil @-))
;;             (hyps                                  (build.modus-ponens-2 @- *1))))
;;           (iffp
;;            ;; The trace is (iff x (not* x)) = t
;;            (@derive
;;             ((v hyps (= (iff lhs rhs) t))           (rw.eqtrace-bldr x box))
;;             ((v (= (iff lhs rhs) t) hyps)           (build.commute-or @-)                                        *0)
;;             ((!= (iff lhs rhs) t)                   (rw.eqtrace-contradiction-lemma2 lhs rhs))
;;             (hyps                                   (build.modus-ponens-2 @- *0))))
;;           (t
;;            ;; The trace is (equal x (not* x)) = t
;;            (@derive
;;             ((v hyps (= (equal lhs rhs) t))        (rw.eqtrace-bldr x box))
;;             ((= rhs (not lhs))                     (clause.standardize-negative-term-bldr rhs))
;;             (hyps                                  (rw.eqtrace-contradiction-bldr-lemma3 @-- @-)))))))

;; (defobligations rw.eqtrace-contradiction-bldr-alt
;;   (rw.eqtrace-bldr
;;    build.commute-or
;;    build.modus-ponens-2
;;    build.not-pequal-constants
;;    build.not-equal-from-not-pequal
;;    build.not-t-from-nil
;;    rw.eqtrace-contradiction-lemma2
;;    rw.eqtrace-contradiction-bldr-lemma3)
;;   :extra-thms ((rw.eqtrace-contradiction-lemma1)))

;; (encapsulate
;;  ()
;;  (local (in-theory (enable rw.eqtrace-contradictionp
;;                            rw.eqtrace-contradiction-bldr-alt
;;                            rw.eqtrace-formula
;;                            rw.eqtrace-contradiction-lemma1
;;                            theorem-inequality-of-not-x-and-x)))

;;  (defthm rw.eqtrace-contradiction-bldr-alt-under-iff
;;    (iff (rw.eqtrace-contradiction-bldr-alt x box)
;;         t))

;;  (defthm forcing-logic.appealp-of-rw.eqtrace-contradiction-bldr-alt
;;    (implies (force (and (rw.eqtracep x)
;;                         (rw.eqtrace-contradictionp x)
;;                         (rw.hypboxp box)
;;                         (rw.eqtrace-okp x box)))
;;             (equal (logic.appealp (rw.eqtrace-contradiction-bldr-alt x box))
;;                    t)))

;;  (defthm forcing-logic.conclusion-of-rw.eqtrace-contradiction-bldr-alt
;;    (implies (force (and (rw.eqtracep x)
;;                         (rw.eqtrace-contradictionp x)
;;                         (rw.hypboxp box)
;;                         (rw.eqtrace-okp x box)))
;;             (equal (logic.conclusion (rw.eqtrace-contradiction-bldr-alt x box))
;;                    (rw.hypbox-formula box)))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;  (defthm@ forcing-logic.proofp-of-rw.eqtrace-contradiction-bldr-alt
;;    (implies (force (and (rw.eqtracep x)
;;                         (rw.eqtrace-contradictionp x)
;;                         (rw.hypboxp box)
;;                         (rw.eqtrace-okp x box)
;;                         ;; ---
;;                         (rw.eqtrace-atblp x atbl)
;;                         (rw.hypbox-atblp box atbl)
;;                         (equal (cdr (lookup 'not atbl)) 1)
;;                         (equal (cdr (lookup 'equal atbl)) 2)
;;                         (equal (cdr (lookup 'iff atbl)) 2)
;;                         (@obligations rw.eqtrace-contradiction-bldr-alt)))
;;             (equal (logic.proofp (rw.eqtrace-contradiction-bldr-alt x box) axioms thms atbl)
;;                    t)))

;;  (verify-guards rw.eqtrace-contradiction-bldr-alt))
