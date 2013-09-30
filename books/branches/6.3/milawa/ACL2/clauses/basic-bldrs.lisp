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
(include-book "basic")
(include-book "../build/not")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defderiv clause.substitute-iff-into-literal-bldr
  :derive (!= (? a) nil)
  :from   ((proof x (!= (? b) nil))
           (proof y (= (iff (? a) (? b)) t)))
  :proof  (@derive
           ((!= (? b) nil)              (@given x))
           ((= (iff (? b) t) t)         (build.iff-t-from-not-pequal-nil @-))
           ((= (iff (? a) (? b)) t)     (@given y))
           ((= (iff (? a) t) t)         (build.transitivity-of-iff @- @--))
           ((!= (iff (? a) t) nil)      (build.not-nil-from-t @-))
           ((!= (? a) nil)              (build.not-pequal-nil-from-iff-t @-))))


(defderiv clause.disjoined-substitute-iff-into-literal-bldr
  :derive (v P (!= (? a) nil))
  :from   ((proof x (v P (!= (? b) nil)))
           (proof y (v P (= (iff (? a) (? b)) t))))
  :proof  (@derive
           ((v P (!= (? b) nil))             (@given x))
           ((v P (= (iff (? b) t) t))        (build.disjoined-iff-t-from-not-pequal-nil @-))
           ((v P (= (iff (? a) (? b)) t))    (@given y))
           ((v P (= (iff (? a) t) t))        (build.disjoined-transitivity-of-iff @- @--))
           ((v P (!= (iff (? a) t) nil))     (build.disjoined-not-nil-from-t @-))
           ((v P (!= (? a) nil))             (build.disjoined-not-pequal-nil-from-iff-t @-))))



;; Not standardization.
;;
;; Negative-termp recognizes many variants of (not x).  We can normalize any of
;; these to (not x) with standardize-negative-term-bldr.

(deftheorem clause.theorem-standardize-equal-x-nil
  :derive (= (equal x nil) (not x))
  :proof  (@derive
           ((v (= x y) (= (equal x y) nil))                (build.axiom (axiom-equal-when-diff)))
           ((v (= x nil) (= (equal x nil) nil))            (build.instantiation @- (@sigma (y . nil)))          *1a)
           ((v (= x nil) (= (if x y z) y))                 (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= (if x nil t) nil))             (build.instantiation @- (@sigma (y . nil) (z . t))))
           ((v (= x nil) (= nil (if x nil t)))             (build.disjoined-commute-pequal @-))
           ((v (= x nil) (= (equal x nil) (if x nil t)))   (build.disjoined-transitivity-of-pequal *1a @-)      *1)
           ;; ---
           ((v (!= x y) (= (equal x y) t))                 (build.axiom (axiom-equal-when-same)))
           ((v (!= x nil) (= (equal x nil) t))             (build.instantiation @- (@sigma (y . nil)))          *2a)
           ((v (!= x nil) (= (if x y z) z))                (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= (if x nil t) t))              (build.instantiation @- (@sigma (y . nil) (z . t))))
           ((v (!= x nil) (= t (if x nil t)))              (build.disjoined-commute-pequal @-))
           ((v (!= x nil) (= (equal x nil) (if x nil t)))  (build.disjoined-transitivity-of-pequal *2a @-)      *2)
           ;; ---
           ((v (= (equal x nil) (if x nil t))
               (= (equal x nil) (if x nil t)))             (build.cut *1 *2))
           ((= (equal x nil) (if x nil t))                 (build.contraction @-)                               *3)
           ((= (not x) (if x nil t))                       (build.axiom (definition-of-not)))
           ((= (if x nil t) (not x))                       (build.commute-pequal @-))
           ((= (equal x nil) (not x))                      (build.transitivity-of-pequal *3 @-)))
  :minatbl ((if . 3)
            (equal . 2)
            (not . 1)))

(deftheorem clause.theorem-standardize-equal-nil-x
  :derive (= (equal nil x) (not x))
  :proof  (@derive
           ((= (equal x y) (equal y x))      (build.theorem (theorem-symmetry-of-equal)))
           ((= (equal nil x) (equal x nil))  (build.instantiation @- (@sigma (x . nil) (y . x))))
           ((= (equal x nil) (not x))        (build.theorem (clause.theorem-standardize-equal-x-nil)))
           ((= (equal nil x) (not x))        (build.transitivity-of-pequal @-- @-)))
  :minatbl ((equal . 2)
            (if . 3)
            (not . 1)))

(deftheorem clause.theorem-standardize-iff-x-nil
  :derive (= (iff x nil) (not x))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))                   (build.theorem (theorem-not-when-nil)))
           ((v (!= x nil) (= t (not x)))                   (build.disjoined-commute-pequal @-))
           ((v (!= x nil) (= (iff x nil) t))               (build.theorem (theorem-iff-nil-when-nil)))
           ((v (!= x nil) (= (iff x nil) (not x)))         (build.disjoined-transitivity-of-pequal @- @--) *1)

           ((v (= x nil) (= (not x) nil))                  (build.theorem (theorem-not-when-not-nil)))
           ((v (= x nil) (= nil (not x)))                  (build.disjoined-commute-pequal @-))
           ((v (= x nil) (= (iff x nil) nil))              (build.theorem (theorem-iff-nil-when-not-nil)))
           ((v (= x nil) (= (iff x nil) (not x)))          (build.disjoined-transitivity-of-pequal @- @--))

           ((v (= (iff x nil) (not x))
               (= (iff x nil) (not x)))                    (build.cut @- *1))
           ((= (iff x nil) (not x))                        (build.contraction @-)))
  :minatbl ((iff . 2)
            (equal . 2)
            (not . 1)))

(deftheorem clause.theorem-standardize-iff-nil-x
  :derive (= (iff nil x) (not x))
  :proof  (@derive
           ((= (iff x y) (iff y x))        (build.theorem (theorem-symmetry-of-iff)))
           ((= (iff nil x) (iff x nil))    (build.instantiation @- (@sigma (x . nil) (y . x))))
           ((= (iff x nil) (not x))        (build.theorem (clause.theorem-standardize-iff-x-nil)))
           ((= (iff nil x) (not x))        (build.transitivity-of-pequal @-- @-)))
  :minatbl ((iff . 2)
            (not . 1)))



(defund@ clause.standardize-negative-term-bldr (x)
  ;; Prove that any negative term is equal to (not guts).
  (declare (xargs :guard (and (logic.termp x)
                              (clause.negative-termp x))
                  :guard-hints (("Goal" :in-theory (enable clause.negative-termp
                                                           definition-of-not
                                                           clause.theorem-standardize-equal-x-nil
                                                           clause.theorem-standardize-equal-nil-x
                                                           clause.theorem-standardize-iff-nil-x
                                                           clause.theorem-standardize-iff-x-nil)))))
  (let ((name (logic.function-name x))
        (args (logic.function-args x)))
    (cond ((equal name 'not)
           ;; Found (not guts)
           (@derive ((= (not guts) (not guts))             (build.reflexivity x))))
          ((equal name 'if)
           ;; Found (if guts nil t).
           (@derive ((= (not x) (if x nil t))              (build.axiom (definition-of-not)))
                    ((= (if x nil t) (not x))              (build.commute-pequal @-))
                    ((= (if guts nil t) (not guts))        (build.instantiation @- (list (cons 'x (first args)))))))
          ((equal name 'equal)
           (if (equal (first args) ''nil)
               ;; Found (equal nil guts).
               (@derive ((= (equal nil x) (not x))         (build.theorem (clause.theorem-standardize-equal-nil-x)))
                        ((= (equal nil guts) (not guts))   (build.instantiation @- (list (cons 'x (second args))))))
             ;; Found (equal guts nil)
             (@derive ((= (equal x nil) (not x))           (build.theorem (clause.theorem-standardize-equal-x-nil)))
                      ((= (equal guts nil) (not guts))     (build.instantiation @- (list (cons 'x (first args))))))))
          (t
           (if (equal (first args) ''nil)
               ;; Found (iff nil guts)
               (@derive ((= (iff nil x) (not x))           (build.theorem (clause.theorem-standardize-iff-nil-x)))
                        ((= (iff nil guts) (not guts))     (build.instantiation @- (list (cons 'x (second args))))))
             ;; Found (iff guts nil)
             (@derive ((= (iff x nil) (not x))             (build.theorem (clause.theorem-standardize-iff-x-nil)))
                      ((= (iff guts nil) (not guts))       (build.instantiation @- (list (cons 'x (first args)))))))))))

(defobligations clause.standardize-negative-term-bldr
  (build.reflexivity build.commute-pequal build.instantiation)
  :extra-axioms ((definition-of-not))
  :extra-thms ((clause.theorem-standardize-equal-nil-x)
               (clause.theorem-standardize-equal-x-nil)
               (clause.theorem-standardize-iff-nil-x)
               (clause.theorem-standardize-iff-x-nil)))

(encapsulate
 ()
 (local (in-theory (enable clause.standardize-negative-term-bldr
                           clause.negative-termp
                           clause.negative-term-guts
                           definition-of-not
                           clause.theorem-standardize-equal-nil-x
                           clause.theorem-standardize-equal-x-nil
                           clause.theorem-standardize-iff-nil-x
                           clause.theorem-standardize-iff-x-nil)))

 (defthm forcing-logic.appealp-of-clause.standardize-negative-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.negative-termp x)))
            (equal (logic.appealp (clause.standardize-negative-term-bldr x))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.standardize-negative-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.negative-termp x)))
            (equal (logic.conclusion (clause.standardize-negative-term-bldr x))
                   (logic.pequal x (logic.function 'not (list (clause.negative-term-guts x)))))))

 (defthm@ forcing-logic.proofp-of-clause.standardize-negative-term-bldr
   (implies (force (and (logic.termp x)
                        (clause.negative-termp x)
                        ;; ---
                        (logic.term-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.standardize-negative-term-bldr)))
            (equal (logic.proofp (clause.standardize-negative-term-bldr x) axioms thms atbl)
                   t))))



(defund clause.standardize-negative-term-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.standardize-negative-term-bldr)
         (equal extras nil)
         (equal subproofs nil)
         (equal (logic.fmtype conclusion) 'pequal*)
         (let ((lhs (logic.=lhs conclusion))
               (rhs (logic.=rhs conclusion)))
           (and (logic.term-atblp lhs atbl)
                (clause.negative-termp lhs)
                (equal rhs (logic.function 'not (list (clause.negative-term-guts lhs)))))))))

(defund clause.standardize-negative-term-bldr-high (x)
  (declare (xargs :guard (and (logic.termp x)
                              (clause.negative-termp x))))
  (logic.appeal 'clause.standardize-negative-term-bldr
                (logic.pequal x (logic.function 'not (list (clause.negative-term-guts x))))
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable clause.standardize-negative-term-bldr-okp)))

 (defthm booleanp-of-clause.standardize-negative-term-bldr-okp
   (equal (booleanp (clause.standardize-negative-term-bldr-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.standardize-negative-term-bldr-okp-of-logic.appeal-identity
   (equal (clause.standardize-negative-term-bldr-okp (logic.appeal-identity x) atbl)
          (clause.standardize-negative-term-bldr-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthm lemma-1-for-soundness-of-clause.standardize-negative-term-bldr-okp
   (implies (and (clause.standardize-negative-term-bldr-okp x atbl)
                 (logic.appealp x))
            (equal (logic.conclusion (clause.standardize-negative-term-bldr (logic.=lhs (logic.conclusion x))))
                   (logic.conclusion x))))

 (defthm@ lemma-2-for-soundness-of-clause.standardize-negative-term-bldr-okp
   (implies (and (clause.standardize-negative-term-bldr-okp x atbl)
                 (logic.appealp x)
                 (@obligations clause.standardize-negative-term-bldr)
                 (equal (cdr (lookup 'not atbl)) 1))
            (equal (logic.proofp (clause.standardize-negative-term-bldr (logic.=lhs (logic.conclusion x)))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.standardize-negative-term-bldr-okp
   (implies (and (clause.standardize-negative-term-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.standardize-negative-term-bldr)
                             (equal (cdr (lookup 'not atbl)) 1))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.standardize-negative-term-bldr-okp
                               lemma-2-for-soundness-of-clause.standardize-negative-term-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.standardize-negative-term-bldr (logic.=lhs (logic.conclusion x))))))))))






(defund@ clause.standardize-double-negative-term-bldr (a)
  ;; Prove that any double-negative term is equal to (not (not guts')), where
  ;; guts' is the guts of its guts.
  (declare (xargs :guard (and (logic.termp a)
                              (clause.negative-termp a)
                              (clause.negative-termp (clause.negative-term-guts a)))))
  (let* ((guts (clause.negative-term-guts a)))
    (@derive ((= guts (not guts-prime))               (clause.standardize-negative-term-bldr guts))
             ((= (not guts) (not (not guts-prime)))   (build.pequal-by-args 'not (list @-)))
             ((= a (not guts))                        (clause.standardize-negative-term-bldr a))
             ((= a (not (not guts-prime)))            (build.transitivity-of-pequal @- @--)))))

(defobligations clause.standardize-double-negative-term-bldr
  (clause.standardize-negative-term-bldr build.pequal-by-args build.transitivity-of-pequal))

(encapsulate
 ()
 (local (in-theory (enable clause.standardize-double-negative-term-bldr)))

 (defthm forcing-logic.appealp-of-clause.standardize-double-negative-term-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))))
            (equal (logic.appealp (clause.standardize-double-negative-term-bldr a))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.standardize-double-negative-term-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))))
            (equal (logic.conclusion (clause.standardize-double-negative-term-bldr a))
                   (logic.pequal a (logic.function 'not (list (logic.function 'not (list (clause.negative-term-guts (clause.negative-term-guts a))))))))))

 (defthm@ forcing-logic.proofp-of-clause.standardize-double-negative-term-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))
                        ;; ---
                        (logic.term-atblp a atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.standardize-double-negative-term-bldr)))
            (equal (logic.proofp (clause.standardize-double-negative-term-bldr a) axioms thms atbl)
                   t))))



(defund clause.standardize-double-negative-term-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.standardize-double-negative-term-bldr)
         (equal extras nil)
         (equal subproofs nil)
         (equal (logic.fmtype conclusion) 'pequal*)
         (let ((lhs (logic.=lhs conclusion))
               (rhs (logic.=rhs conclusion)))
           (and (clause.negative-termp lhs)
                (clause.negative-termp (clause.negative-term-guts lhs))
                (logic.term-atblp lhs atbl)
                (equal rhs (logic.function 'not (list
                            (logic.function 'not (list
                             (clause.negative-term-guts
                              (clause.negative-term-guts lhs))))))))))))

(defund clause.standardize-double-negative-term-bldr-high (a)
  (declare (xargs :guard (and (logic.termp a)
                              (clause.negative-termp a)
                              (clause.negative-termp (clause.negative-term-guts a)))))
  (logic.appeal 'clause.standardize-double-negative-term-bldr
                (logic.pequal a (logic.function 'not (list
                                 (logic.function 'not (list
                                  (clause.negative-term-guts
                                   (clause.negative-term-guts a)))))))
                nil
                nil))

(encapsulate
 ()
 (local (in-theory (enable clause.standardize-double-negative-term-bldr-okp)))

 (defthm booleanp-of-clause.standardize-double-negative-term-bldr-okp
   (equal (booleanp (clause.standardize-double-negative-term-bldr-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.standardize-double-negative-term-bldr-okp-of-logic.appeal-identity
   (equal (clause.standardize-double-negative-term-bldr-okp (logic.appeal-identity x) atbl)
          (clause.standardize-double-negative-term-bldr-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthm lemma-1-for-soundness-of-clause.standardize-double-negative-term-bldr-okp
   (implies (and (clause.standardize-double-negative-term-bldr-okp x atbl)
                 (logic.appealp x))
            (equal (logic.conclusion (clause.standardize-double-negative-term-bldr (logic.=lhs (logic.conclusion x))))
                   (logic.conclusion x))))

 (defthm@ lemma-2-for-soundness-of-clause.standardize-double-negative-term-bldr-okp
   (implies (and (clause.standardize-double-negative-term-bldr-okp x atbl)
                 (logic.appealp x)
                 (@obligations clause.standardize-double-negative-term-bldr)
                 (equal (cdr (lookup 'not atbl)) 1))
            (equal (logic.proofp (clause.standardize-double-negative-term-bldr (logic.=lhs (logic.conclusion x)))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.standardize-double-negative-term-bldr-okp
   (implies (and (clause.standardize-double-negative-term-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.standardize-double-negative-term-bldr)
                             (equal (cdr (lookup 'not atbl)) 1))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.standardize-double-negative-term-bldr-okp
                               lemma-2-for-soundness-of-clause.standardize-double-negative-term-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.standardize-double-negative-term-bldr (logic.=lhs (logic.conclusion x))))))))))




(defund@ clause.standardize-double-negative-term-under-iff-bldr (a)
  ;; Prove that any double-negative term is iff to (not (not guts')), where
  ;; guts' is the guts of its guts.
  (declare (xargs :guard (and (logic.termp a)
                              (clause.negative-termp a)
                              (clause.negative-termp (clause.negative-term-guts a)))
                  :guard-hints (("Goal" :in-theory (enable theorem-not-of-not-under-iff)))))
  (let ((guts-prime (clause.negative-term-guts (clause.negative-term-guts a))))
    (@derive
     ((= a (not (not guts-prime)))                   (clause.standardize-double-negative-term-bldr a))
     ((= (iff a (not (not guts-prime))) t)           (build.iff-from-pequal @-)                           *1)
     ((= (iff (not (not x)) x) t)                    (build.theorem (theorem-not-of-not-under-iff)))
     ((= (iff (not (not guts-prime)) guts-prime) t)  (build.instantiation @- (list (cons 'x guts-prime))))
     ((= (iff a guts-prime) t)                       (build.transitivity-of-iff *1 @-)))))

(defobligations clause.standardize-double-negative-term-under-iff-bldr
  (clause.standardize-double-negative-term-bldr
   build.iff-from-pequal build.instantiation build.transitivity-of-iff)
  :extra-thms ((theorem-not-of-not-under-iff)))

(encapsulate
 ()
 (local (in-theory (enable clause.standardize-double-negative-term-under-iff-bldr
                           theorem-not-of-not-under-iff)))

 (defthm forcing-logic.appealp-of-clause.standardize-double-negative-term-under-iff-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))))
            (equal (logic.appealp (clause.standardize-double-negative-term-under-iff-bldr a))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.standardize-double-negative-term-under-iff-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))))
            (equal (logic.conclusion (clause.standardize-double-negative-term-under-iff-bldr a))
                   (let* ((guts-prime         (clause.negative-term-guts (clause.negative-term-guts a))))
                     (logic.pequal (logic.function 'iff (list a guts-prime))
                                   ''t)))))

 (defthm@ forcing-logic.proofp-of-clause.standardize-double-negative-term-under-iff-bldr
   (implies (force (and (logic.termp a)
                        (clause.negative-termp a)
                        (clause.negative-termp (clause.negative-term-guts a))
                        ;; ---
                        (logic.term-atblp a atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations clause.standardize-double-negative-term-under-iff-bldr)))
            (equal (logic.proofp (clause.standardize-double-negative-term-under-iff-bldr a) axioms thms atbl)
                   t))))