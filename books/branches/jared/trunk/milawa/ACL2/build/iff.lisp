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
(include-book "equal")
(include-book "if")
(include-book "disjoined-subset")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "iff.tex")

(dd.section "Iff manipulation")


(defund definition-of-iff ()
  (logic.pequal (logic.function 'iff (list 'x 'y))
                (logic.function 'if (list 'x
                                          (logic.function 'if (list 'y ''t ''nil))
                                          (logic.function 'if (list 'y ''nil ''t))))))

(in-theory (disable (:executable-counterpart definition-of-iff)))

(defthm logic.formulap-of-definition-of-iff
  (equal (logic.formulap (definition-of-iff))
         t)
  :hints(("Goal" :in-theory (enable definition-of-iff))))

(defthm forcing-logic.formula-atblp-of-definition-of-iff
  (implies (force (and (equal (cdr (lookup 'iff atbl)) 2)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.formula-atblp (definition-of-iff) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-iff))))

(acl2::set-ignore-ok t)





;; LEMMAS.
;;
;; We characterize the behavior of iff when one or both of its arguments are
;; known to be nil or non-nil.  These lemmas are useful in proving the theorems
;; and rules we are actually interested in.

(deftheorem theorem-iff-lhs-false
  :derive (v (!= x nil) (= (iff x y) (if y nil t)))
  :proof  (@derive
           ((= (iff x y) (if x (if y t nil) (if y nil t)))        (build.axiom (definition-of-iff)))

           ((v (!= x nil)
               (= (iff x y) (if x (if y t nil) (if y nil t))))    (build.expansion (@formula (!= x nil)) @-)   *1)

           ((v (!= x nil) (= x nil))                              (build.propositional-schema (@formula (= x nil))))

           ((v (!= x nil) (= (if x (if y t nil) (if y nil t))
                             (if y nil t)))                       (build.disjoined-if-when-nil @-
                                                                                               (@term (if y t nil))
                                                                                               (@term (if y nil t))))

           ((v (!= x nil) (= (iff x y) (if y nil t)))             (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-iff-lhs-true
  :derive (v (= x nil) (= (iff x y) (if y t nil)))
  :proof  (@derive
           ((= (iff x y) (if x (if y t nil) (if y nil t)))        (build.axiom (definition-of-iff)))

           ((v (= x nil)
               (= (iff x y) (if x (if y t nil) (if y nil t))))    (build.expansion (@formula (= x nil)) @-)   *1)

           ((v (!= x nil) (= x nil))                              (build.propositional-schema (@formula (= x nil))))

           ((v (= x nil) (!= x nil))                              (build.commute-or @-))

           ((v (= x nil) (= (if x (if y t nil) (if y nil t))
                            (if y t nil)))                        (build.disjoined-if-when-not-nil @-
                                                                                                   (@term (if y t nil))
                                                                                                   (@term (if y nil t))))

           ((v (= x nil) (= (iff x y) (if y t nil)))              (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-iff-rhs-false
  :derive (v (!= y nil) (= (iff x y) (if x nil t)))
  :proof  (@derive
           ((= (iff x y) (if x (if y t nil) (if y nil t)))        (build.axiom (definition-of-iff)))

           ((v (!= y nil)
               (= (iff x y) (if x (if y t nil) (if y nil t))))    (build.expansion (@formula (!= y nil)) @-)   *1)

           ((= x x)                                               (build.reflexivity (@term x)))
           ((v (!= y nil) (= x x))                                (build.expansion (@formula (!= y nil)) @-)   *2a)

           ((v (!= y nil) (= y nil))                              (build.propositional-schema (@formula (= y nil))))
           ((v (!= y nil) (= (if y t nil) nil))                   (build.disjoined-if-when-nil @- (@term t) (@term nil))  *2b)
           ((v (!= y nil) (= (if y nil t) t))                     (build.disjoined-if-when-nil @-- (@term nil) (@term t))  *2c)

           ((v (!= y nil) (= (if x (if y t nil) (if y nil t))
                             (if x nil t)))                       (build.disjoined-pequal-by-args 'if
                                                                                                  (@formula (!= y nil))
                                                                                                  (list *2a *2b *2c)))

           ((v (!= y nil) (= (iff x y) (if x nil t)))             (build.disjoined-transitivity-of-pequal *1 @-)))

  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-iff-rhs-true
  :derive (v (= y nil) (= (iff x y) (if x t nil)))
  :proof  (@derive
           ((= (iff x y) (if x (if y t nil) (if y nil t)))        (build.axiom (definition-of-iff)))

           ((v (= y nil)
               (= (iff x y) (if x (if y t nil) (if y nil t))))    (build.expansion (@formula (= y nil)) @-)   *1)

           ((= x x)                                               (build.reflexivity (@term x)))
           ((v (= y nil) (= x x))                                 (build.expansion (@formula (= y nil)) @-)   *2a)

           ((v (!= y nil) (= y nil))                              (build.propositional-schema (@formula (= y nil))))
           ((v (= y nil) (!= y nil))                              (build.commute-or @-))
           ((v (= y nil) (= (if y t nil) t))                      (build.disjoined-if-when-not-nil @- (@term t) (@term nil))  *2b)
           ((v (= y nil) (= (if y nil t) nil))                    (build.disjoined-if-when-not-nil @-- (@term nil) (@term t))  *2c)

           ((v (= y nil) (= (if x (if y t nil) (if y nil t))
                            (if x t nil)))                        (build.disjoined-pequal-by-args 'if
                                                                                                  (@formula (= y nil))
                                                                                                  (list *2a *2b *2c)))

           ((v (= y nil) (= (iff x y) (if x t nil)))              (build.disjoined-transitivity-of-pequal *1 @-)))

  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-iff-both-true
 :derive (v (= x nil) (v (= y nil) (= (iff x y) t)))
 :proof (@derive
         ((v (= x nil) (= (iff x y) (if y t nil)))                (build.theorem (theorem-iff-lhs-true)))
         ((v (v (= x nil) (= y nil)) (= (iff x y) (if y t nil)))  (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))) *1)
         ((v (= x nil) (= (if x y z) y))                          (build.axiom (axiom-if-when-not-nil)))
         ((v (= y nil) (= (if y t nil) t))                        (build.instantiation @- (@sigma (x . y) (y . t) (z . nil))))
         ((v (v (= x nil) (= y nil)) (= (if y t nil) t))          (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))))
         ((v (v (= x nil) (= y nil)) (= (iff x y) t))             (build.disjoined-transitivity-of-pequal *1 @-))
         ((v (= x nil) (v (= y nil) (= (iff x y) t)))             (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))

(deftheorem theorem-iff-both-false
 :derive (v (!= x nil) (v (!= y nil) (= (iff x y) t)))
 :proof (@derive
         ((v (!= x nil) (= (iff x y) (if y nil t)))                 (build.theorem (theorem-iff-lhs-false)))
         ((v (v (!= x nil) (!= y nil)) (= (iff x y) (if y nil t)))  (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))) *1)
         ((v (!= x nil) (= (if x y z) z))                           (build.axiom (axiom-if-when-nil)))
         ((v (!= y nil) (= (if y nil t) t))                         (build.instantiation @- (@sigma (x . y) (y . nil) (z . t))))
         ((v (v (!= x nil) (!= y nil)) (= (if y nil t) t))          (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))))
         ((v (v (!= x nil) (!= y nil)) (= (iff x y) t))             (build.disjoined-transitivity-of-pequal *1 @-))
         ((v (!= x nil) (v (!= y nil) (= (iff x y) t)))             (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))

(deftheorem theorem-iff-true-false
 :derive (v (= x nil) (v (!= y nil) (= (iff x y) nil)))
 :proof (@derive
         ((v (= x nil) (= (iff x y) (if y t nil)))                  (build.theorem (theorem-iff-lhs-true)))
         ((v (v (= x nil) (!= y nil)) (= (iff x y) (if y t nil)))   (build.multi-assoc-expansion @- (@formulas (= x nil) (!= y nil))) *1)
         ((v (= x nil) (= (if x y z) z))                            (build.axiom (axiom-if-when-nil)))
         ((v (!= y nil) (= (if y t nil) nil))                       (build.instantiation @- (@sigma (x . y) (y . t) (z . nil))))
         ((v (v (= x nil) (!= y nil)) (= (if y t nil) nil))         (build.multi-assoc-expansion @- (@formulas (= x nil) (!= y nil))))
         ((v (v (= x nil) (!= y nil)) (= (iff x y) nil))            (build.disjoined-transitivity-of-pequal *1 @-))
         ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))            (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))

(deftheorem theorem-iff-false-true
 :derive (v (!= x nil) (v (= y nil) (= (iff x y) nil)))
 :proof (@derive
         ((v (!= x nil) (= (iff x y) (if y nil t)))                (build.theorem (theorem-iff-lhs-false)))
         ((v (v (!= x nil) (= y nil)) (= (iff x y) (if y nil t)))  (build.multi-assoc-expansion @- (@formulas (!= x nil) (= y nil))) *1)
         ((v (= x nil) (= (if x y z) y))                           (build.axiom (axiom-if-when-not-nil)))
         ((v (= y nil) (= (if y nil t) nil))                       (build.instantiation @- (@sigma (x . y) (y . nil) (z . t))))
         ((v (v (!= x nil) (= y nil)) (= (if y nil t) nil))        (build.multi-assoc-expansion @- (@formulas (!= x nil) (= y nil))))
         ((v (v (!= x nil) (= y nil)) (= (iff x y) nil))           (build.disjoined-transitivity-of-pequal *1 @-))
         ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))           (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))




;; Yuck, I don't really want to have these.  The disjoined transitive if reduction rules might give me a
;; nice way around these.

(deftheorem theorem-iff-t-when-not-nil
  :derive (v (= x nil) (= (iff x t) t))
  :proof (@derive
          ((v (= x nil) (= (iff x y) (if y t nil)))   (build.theorem (theorem-iff-lhs-true)))
          ((v (= x nil) (= (iff x t) (if t t nil)))   (build.instantiation @- (@sigma (y . t))) *1)
          ((= (if t t nil) t)                         (build.if-of-t (@term t) (@term nil)))
          ((v (= x nil) (= (if t t nil) t))           (build.expansion (@formula (= x nil)) @-))
          ((v (= x nil) (= (iff x t) t))              (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (iff . 2)))

(defderiv build.iff-t-from-not-pequal-nil
  :derive (= (iff (? a) t) t)
  :from   ((proof x (!= (? a) nil)))
  :proof  (@derive
           ((v (= x nil) (= (iff x t) t))          (build.theorem (theorem-iff-t-when-not-nil)))
           ((v (= (? a) nil) (= (iff (? a) t) t))  (build.instantiation @- (@sigma (x . (? a)))))
           ((!= (? a) nil)                         (@given x))
           ((= (iff (? a) t) t)                    (build.modus-ponens-2 @- @--)))
  :minatbl ((iff . 2)))

(defderiv build.disjoined-iff-t-from-not-pequal-nil
  :derive (v P (= (iff (? a) t) t))
  :from   ((proof x (v P (!= (? a) nil))))
  :proof  (@derive
           ((v (= x nil) (= (iff x t) t))               (build.theorem (theorem-iff-t-when-not-nil)))
           ((v (= (? a) nil) (= (iff (? a) t) t))       (build.instantiation @- (@sigma (x . (? a)))))
           ((v P (v (= (? a) nil) (= (iff (? a) t) t))) (build.expansion (@formula P) @-))
           ((v P (!= (? a) nil))                        (@given x))
           ((v P (= (iff (? a) t) t))                   (build.disjoined-modus-ponens-2 @- @--)))
  :minatbl ((iff . 2)))



(deftheorem theorem-iff-t-when-nil
  :derive (v (!= x nil) (= (iff x t) nil))
  :proof (@derive
          ((v (!= x nil) (= (iff x y) (if y nil t)))  (build.theorem (theorem-iff-lhs-false)))
          ((v (!= x nil) (= (iff x t) (if t nil t)))  (build.instantiation @- (@sigma (y . t))) *1)
          ((= (if t nil nil) nil)                     (build.if-of-t (@term nil) (@term t)))
          ((v (!= x nil) (= (if t nil nil) nil))      (build.expansion (@formula (!= x nil)) @-))
          ((v (!= x nil) (= (iff x t) nil))           (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (iff . 2)))

(defderiv build.not-pequal-nil-from-iff-t
  :derive (!= (? a) nil)
  :from   ((proof x (!= (iff (? a) t) nil)))
  :proof  (@derive
           ((v (!= x nil) (= (iff x t) nil))          (build.theorem (theorem-iff-t-when-nil)))
           ((v (!= (? a) nil) (= (iff (? a) t) nil))  (build.instantiation @- (@sigma (x . (? a)))))
           ((v (= (iff (? a) t) nil) (!= (? a) nil))  (build.commute-or @-))
           ((!= (iff (? a) t) nil)                    (@given x))
           ((!= (? a) nil)                            (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-not-pequal-nil-from-iff-t
  :derive (v P (!= (? a) nil))
  :from   ((proof x (v P (!= (iff (? a) t) nil))))
  :proof  (@derive
           ((v (!= x nil) (= (iff x t) nil))                (build.theorem (theorem-iff-t-when-nil)))
           ((v (!= (? a) nil) (= (iff (? a) t) nil))        (build.instantiation @- (@sigma (x . (? a)))))
           ((v (= (iff (? a) t) nil) (!= (? a) nil))        (build.commute-or @-))
           ((v P (v (= (iff (? a) t) nil) (!= (? a) nil)))  (build.expansion (@formula P) @-))
           ((v P (!= (iff (? a) t) nil))                    (@given x))
           ((v P (!= (? a) nil))                            (build.disjoined-modus-ponens-2 @- @--))))


(deftheorem theorem-iff-nil-when-nil
 :derive (v (!= x nil) (= (iff x nil) t))
 :proof  (@derive
          ((v (!= x nil) (= (iff x y) (if y nil t)))     (build.theorem (theorem-iff-lhs-false)))
          ((v (!= x nil) (= (iff x nil) (if nil nil t))) (build.instantiation @- (@sigma (y . nil))) *1)
          ((= (if nil nil t) nil)                        (build.if-of-nil (@term nil) (@term t)))
          ((v (!= x nil) (= (if nil nil t) nil))         (build.expansion (@formula (!= x nil)) @-))
          ((v (!= x nil) (= (iff x nil) nil))            (build.disjoined-transitivity-of-pequal *1 @-)))
 :minatbl ((if . 3)
           (iff . 2)))

(deftheorem theorem-iff-nil-when-not-nil
  :derive (v (= x nil) (= (iff x nil) nil))
  :proof  (@derive
           ((v (= x nil) (= (iff x y) (if y t nil)))       (build.theorem (theorem-iff-lhs-true)))
           ((v (= x nil) (= (iff x nil) (if nil t nil)))   (build.instantiation @- (@sigma (y . nil))) *1)
           ((= (if nil t nil) nil)                         (build.if-of-nil (@term t) (@term nil)))
           ((v (= x nil) (= (if nil t nil) nil))           (build.expansion (@formula (= x nil)) @-))
           ((v (= x nil) (= (iff x nil) nil))              (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (iff . 2)))




;; EQUIVALENCE RULES.  (except transitivity)
;;
;; We now establish that iff is Boolean-valued, reflexive, and symmetric.  We
;; will do the transitivity proof later, after some additional rules about if.
;; As usual, we do the work in theorems which can later be instantiated to keep
;; proof sizes down.

(deftheorem theorem-iff-nil-or-t
  :derive (v (= (iff x y) nil)
             (= (iff x y) t))
  :proof (@derive
          ((v (= x nil) (v (= y nil) (= (iff x y) t)))     (build.theorem (theorem-iff-both-true)))
          ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))  (build.theorem (theorem-iff-false-true)))

          ((v (v (= y nil) (= (iff x y) t))
              (v (= y nil) (= (iff x y) nil)))             (build.cut @-- @-))

          ((v (= y nil)
              (v (= (iff x y) t)
                 (v (= y nil)
                    (= (iff x y) nil))))                   (build.right-associativity @-))

          ((v (= y nil)
              (v (= (iff x y) nil)
                 (= (iff x y) t)))                         (build.generic-subset (@formulas (= y nil)
                                                                                            (= (iff x y) t)
                                                                                            (= y nil)
                                                                                            (= (iff x y) nil))
                                                                                 (@formulas (= y nil)
                                                                                            (= (iff x y) nil)
                                                                                            (= (iff x y) t))
                                                                                 @-) *1)

          ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))  (build.theorem (theorem-iff-true-false)))
          ((v (!= x nil) (v (!= y nil) (= (iff x y) t)))   (build.theorem (theorem-iff-both-false)))

          ((v (v (!= y nil) (= (iff x y) nil))
              (v (!= y nil) (= (iff x y) t)))              (build.cut @-- @-))

          ((v (!= y nil)
              (v (= (iff x y) nil)
                 (v (!= y nil)
                    (= (iff x y) t))))                     (build.right-associativity @-))

          ((v (!= y nil)
              (v (= (iff x y) nil)
                 (= (iff x y) t)))                         (build.generic-subset (@formulas (!= y nil)
                                                                                            (= (iff x y) nil)
                                                                                            (!= y nil)
                                                                                            (= (iff x y) t))
                                                                                 (@formulas (!= y nil)
                                                                                            (= (iff x y) nil)
                                                                                            (= (iff x y) t))
                                                                                 @-))
          ((v (v (= (iff x y) nil) (= (iff x y) t))
              (v (= (iff x y) nil) (= (iff x y) t)))       (build.cut *1 @-))
          ((v (= (iff x y) nil) (= (iff x y) t))           (build.contraction @-)))

  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-reflexivity-of-iff
  :derive (= (iff x x) t)
  :proof  (@derive
           ((v (= x nil) (= (iff x y) (if y t nil)))                           (build.theorem (theorem-iff-lhs-true)))
           ((v (= x nil) (= (iff x x) (if x t nil)))                           (build.instantiation @- (@sigma (y . x)))  *1a)
           ((v (= x nil) (= (if x y z) y))                                     (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= (if x t nil) t))                                   (build.instantiation @- (@sigma (y . t) (z . nil))))
           ((v (= x nil) (= (iff x x) t))                                      (build.disjoined-transitivity-of-pequal *1a @-)  *1)
           ;; ---
           ((v (!= x nil) (= (iff x y) (if y nil t)))                          (build.theorem (theorem-iff-lhs-false)))
           ((v (!= x nil) (= (iff x x) (if x nil t)))                          (build.instantiation @- (@sigma (y . x)))  *2a)
           ((v (!= x nil) (= (if x y z) z))                                    (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= (if x nil t) t))                                  (build.instantiation @- (@sigma (y . nil) (z . t))))
           ((v (!= x nil) (= (iff x x) t))                                     (build.disjoined-transitivity-of-pequal *2a @-) *2)
           ;; ---
           ((v (= (iff x x) t) (= (iff x x) t))                                (build.cut *1 *2))
           ((= (iff x x) t)                                                    (build.contraction @-)))
  :minatbl ((if . 3)
            (iff . 2)))

(deftheorem theorem-symmetry-of-iff
  :derive (= (iff x y) (iff y x))
  :proof  (@derive
           ((v (= y nil) (= (iff x y) (if x t nil)))                           (build.theorem (theorem-iff-rhs-true)))
           ((v (= x nil) (= (iff y x) (if y t nil)))                           (build.instantiation @- (@sigma (x . y) (y . x))))
           ((v (= x nil) (= (if y t nil) (iff y x)))                           (build.disjoined-commute-pequal @-))
           ((v (= x nil) (= (iff x y) (if y t nil)))                           (build.theorem (theorem-iff-lhs-true)))
           ((v (= x nil) (= (iff x y) (iff y x)))                              (build.disjoined-transitivity-of-pequal @- @--)   *1)
           ;; ---
           ((v (!= y nil) (= (iff x y) (if x nil t)))                          (build.theorem (theorem-iff-rhs-false)))
           ((v (!= x nil) (= (iff y x) (if y nil t)))                          (build.instantiation @- (@sigma (x . y) (y . x))))
           ((v (!= x nil) (= (if y nil t) (iff y x)))                          (build.disjoined-commute-pequal @-))
           ((v (!= x nil) (= (iff x y) (if y nil t)))                          (build.theorem (theorem-iff-lhs-false)))
           ((v (!= x nil) (= (iff x y) (iff y x)))                             (build.disjoined-transitivity-of-pequal @- @--)   *2)
           ;; ---
           ((v (= (iff x y) (iff y x)) (= (iff x y) (iff y x)))                (build.cut *1 *2))
           ((= (iff x y) (iff y x))                                            (build.contraction @-)))
  :minatbl ((iff . 2)
            (if . 3)))

(defderiv build.iff-t-from-not-nil
 :derive (= (iff (? a) (? b)) t)
 :from   ((proof x (!= (iff (? a) (? b)) nil)))
 :proof  (@derive
          ((v (= (iff x y) nil) (= (iff x y) t))                                (build.theorem (theorem-iff-nil-or-t)))
          ((v (= (iff (? a) (? b)) nil) (= (iff (? a) (? b)) t))                (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
          ((!= (iff (? a) (? b)) nil)                                           (@given x))
          ((= (iff (? a) (? b)) t)                                              (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-iff-t-from-not-nil
 :derive (v P (= (iff (? a) (? b)) t))
 :from   ((proof x (v P (!= (iff (? a) (? b)) nil))))
 :proof  (@derive
          ((v (= (iff x y) nil) (= (iff x y) t))                                (build.theorem (theorem-iff-nil-or-t)))
          ((v (= (iff (? a) (? b)) nil) (= (iff (? a) (? b)) t))                (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
          ((v P (v (= (iff (? a) (? b)) nil) (= (iff (? a) (? b)) t)))          (build.expansion (@formula P) @-))
          ((v P (!= (iff (? a) (? b)) nil))                                     (@given x))
          ((v P (= (iff (? a) (? b)) t))                                        (build.disjoined-modus-ponens-2 @- @--))))

(defderiv build.iff-reflexivity
  :derive (= (iff (? a) (? a)) t)
  :from   ((term a (? a)))
  :proof  (@derive ((= (iff x x) t)          (build.theorem (theorem-reflexivity-of-iff)))
                   ((= (iff (? a) (? a)) t)  (build.instantiation @- (@sigma (x . (? a))))))
  :minatbl ((iff . 2)))

(defderiv build.commute-iff
  :derive (= (iff (? b) (? a)) t)
  :from   ((proof x (= (iff (? a) (? b)) t)))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use iff reflexivity.
                 (@derive ((= (iff (? b) (? a)) t)                              (build.iff-reflexivity (@term (? a))))))
                (t
                 (@derive ((= (iff x y) (iff y x))                              (build.theorem (theorem-symmetry-of-iff)))
                          ((= (iff (? b) (? a)) (iff (? a) (? b)))              (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                          ((= (iff (? a) (? b)) t)                              (@given x))
                          ((= (iff (? b) (? a)) t)                              (build.transitivity-of-pequal @-- @-)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (build.iff-reflexivity (@term (? a)))
                        (LOGIC.APPEAL 'BUILD.COMMUTE-IFF
                                      (@FORMULA (= (IFF (? B) (? A)) T))
                                      (LIST X)
                                      NIL)))

(defderiv build.disjoined-commute-iff
  :derive (v P (= (iff (? b) (? a)) t))
  :from   ((proof x (v P (= (iff (? a) (? b)) t))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use iff-reflexivity and expansion.
                 (@derive
                  ((= (iff (? b) (? a)) t)                                      (build.iff-reflexivity (@term (? a))))
                  ((v P (= (iff (? b) (? a)) t))                                (build.expansion (@formula P) @-))))
                (t
                 (@derive
                  ((= (iff x y) (iff y x))                                      (build.theorem (theorem-symmetry-of-iff)))
                  ((= (iff (? b) (? a)) (iff (? a) (? b)))                      (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                  ((v P (= (iff (? b) (? a)) (iff (? a) (? b))))                (build.expansion (@formula P) @-))
                  ((v P (= (iff (? a) (? b)) t))                                (@given x))
                  ((v P (= (iff (? b) (? a)) t))                                (build.disjoined-transitivity-of-pequal @-- @-)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (@derive ((= (iff (? b) (? a)) t)         (build.iff-reflexivity (@term (? a))))
                                   ((v P (= (iff (? b) (? a)) t))   (build.expansion (@formula P) @-)))
                        (LOGIC.APPEAL 'BUILD.DISJOINED-COMMUTE-IFF
                                      (@FORMULA (V P (= (IFF (? B) (? A)) T)))
                                      (LIST X)
                                      NIL)))



;; CONGRUENCE RULES.
;;
;; We now develop the classic "congruence rules" which say that when (iff x y),
;; we can replace
;;  - (if x a b) with (if y a b)
;;  - (iff x z) with (iff y z), and
;;  - (iff z x) with (iff z y).

(deftheorem theorem-iff-congruence-lemma
 :derive (v (= x nil) (v (= y nil) (= (if x a b) (if y a b))))
 :proof (@derive
         ((v (= x nil) (= (if x y z) z))                        (build.axiom (axiom-if-when-not-nil)))
         ((v (= x nil) (= (if x a b) b))                        (build.instantiation @- (@sigma (y . a) (z . b))))
         ((v (v (= x nil) (= y nil)) (= (if x a b) b))          (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))) *1)
         ((v (= y nil) (= (if y a b) b))                        (build.instantiation @-- (@sigma (x . y))))
         ((v (v (= x nil) (= y nil)) (= (if y a b) b))          (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))))
         ((v (v (= x nil) (= y nil)) (= b (if y a b)))          (build.disjoined-commute-pequal @-))
         ((v (v (= x nil) (= y nil)) (= (if x a b) (if y a b))) (build.disjoined-transitivity-of-pequal *1 @-))
         ((v (= x nil) (v (= y nil) (= (if x a b) (if y a b)))) (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))

(deftheorem theorem-iff-congruence-lemma-2
 :derive (v (!= x nil) (v (!= y nil) (= (if x a b) (if y a b))))
 :proof  (@derive
          ((v (!= x nil) (= (if x y z) y))                          (build.axiom (axiom-if-when-nil)))
          ((v (!= x nil) (= (if x a b) b))                          (build.instantiation @- (@sigma (y . a) (z . b))))
          ((v (v (!= x nil) (!= y nil)) (= (if x a b) b))           (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))) *1)

          ((v (!= y nil) (= (if y a b) b))                          (build.instantiation @-- (@sigma (x . y))))
          ((v (v (!= x nil) (!= y nil)) (= (if y a b) b))           (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))))
          ((v (v (!= x nil) (!= y nil)) (= b (if y a b)))           (build.disjoined-commute-pequal @-))
          ((v (v (!= x nil) (!= y nil)) (= (if x a b) (if y a b)))  (build.disjoined-transitivity-of-pequal *1 @-))

          ((v (!= x nil) (v (!= y nil) (!= (if x a b) (if y a b)))) (build.right-associativity @-)))
 :minatbl ((iff . 2)
           (if . 3)))

(deftheorem theorem-iff-congruent-if-1
  :derive (v (= (iff x y) nil)
             (= (if x a b) (if y a b)))
  :proof (@derive

          ((v (= x nil) (v (= y nil) (= (if x a b) (if y a b))))   (build.theorem (theorem-iff-congruence-lemma)))
          ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))          (build.theorem (theorem-iff-false-true)))

          ((v (v (= y nil) (= (if x a b) (if y a b)))
              (v (= y nil) (= (iff x y) nil)))                     (build.cut @-- @-))

          ((v (= y nil)
              (v (= (if x a b) (if y a b))
                 (v (= y nil)
                    (= (iff x y) nil))))                           (build.right-associativity @-))

          ((v (= y nil)
              (v (= (iff x y) nil)
                 (= (if x a b) (if y a b))))                       (build.generic-subset (@formulas (= y nil)
                                                                                                    (= (if x a b) (if y a b))
                                                                                                    (= y nil)
                                                                                                    (= (iff x y) nil))
                                                                                         (@formulas (= y nil)
                                                                                                    (= (iff x y) nil)
                                                                                                    (= (if x a b) (if y a b)))
                                                                                         @-)    *1)

          ;; ---------------

          ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))          (build.theorem (theorem-iff-true-false)))
          ((v (!= x nil) (v (!= y nil) (= (if x a b) (if y a b)))) (build.theorem (theorem-iff-congruence-lemma-2)))
          ((v (v (!= y nil) (= (iff x y) nil))
              (v (!= y nil) (= (if x a b) (if y a b))))            (build.cut @-- @-))

          ((v (!= y nil)
              (v (= (iff x y) nil)
                 (v (!= y nil)
                    (= (if x a b) (if y a b)))))                   (build.right-associativity @-))

          ((v (!= y nil)
              (v (= (iff x y) nil)
                 (= (if x a b) (if y a b))))                       (build.generic-subset (@formulas (!= y nil)
                                                                                                    (= (iff x y) nil)
                                                                                                    (!= y nil)
                                                                                                    (= (if x a b) (if y a b)))
                                                                                         (@formulas (!= y nil)
                                                                                                    (= (iff x y) nil)
                                                                                                    (= (if x a b) (if y a b)))
                                                                                         @-))

          ((v (v (= (iff x y) nil)
                 (= (if x a b) (if y a b)))
              (v (= (iff x y) nil)
                 (= (if x a b) (if y a b))))                       (build.cut *1 @-))

          ((v (= (iff x y) nil)
              (= (if x a b) (if y a b)))                        (build.contraction @-)))

  :minatbl ((iff . 2)
            (if . 3)))

(deftheorem theorem-iff-congruent-iff-2
  :derive (v (= (iff x y) nil)
             (= (iff z x) (iff z y)))
  :proof  (@derive

           ((v (= x nil) (= (iff x y) (if y t nil)))  (build.theorem (theorem-iff-lhs-true)))

           ((v (= z nil)
               (= (iff z x) (if x t nil)))            (build.instantiation @- (@sigma (x . z) (y . x)))    *1a)

           ((v (= z nil)
               (= (iff z y) (if y t nil)))            (build.instantiation @- (@sigma (x . y))))

           ((v (= z nil)
               (= (if y t nil) (iff z y)))            (build.disjoined-commute-pequal @-)                  *1b)

           ((v (= (iff x y) nil)
               (= (if x a b) (if y a b)))             (build.theorem (theorem-iff-congruent-if-1)))

           ((v (= (iff x y) nil)
               (= (if x nil t) (if y t nil)))         (build.instantiation @- (@sigma (a . t) (b . nil)))  *1c)

           ;; ---

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (iff z x) (if x t nil))))        (build.multi-assoc-expansion *1a (@formulas (= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (if x nil t) (if y t nil))))     (build.multi-assoc-expansion *1c (@formulas (= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (iff z x) (if y t nil))))        (build.disjoined-transitivity-of-pequal @-- @-))

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (if y t nil) (iff z y))))        (build.multi-assoc-expansion *1b (@formulas (= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (iff z x) (iff z y))))           (build.disjoined-transitivity-of-pequal @-- @-))

           ((v (= z nil)
               (v (= (iff x y) nil)
                  (= (iff z x) (iff z y))))           (build.right-associativity @-)     *1)

           ;; -------------

           ((v (!= x nil)
               (= (iff x y) (if y nil t)))            (build.theorem (theorem-iff-lhs-false)))

           ((v (!= z nil)
               (= (iff z x) (if x nil t)))            (build.instantiation @- (@sigma (x . z) (y . x)))   *2a)

           ((v (!= z nil)
               (= (iff z y) (if y nil t)))            (build.instantiation @- (@sigma (x . y))))

           ((v (!= z nil)
               (= (if y nil t) (iff z y)))            (build.disjoined-commute-pequal @-)               *2b)

           ((v (= (iff x y) nil)
               (= (if x a b) (if y a b)))             (build.theorem (theorem-iff-congruent-if-1)))

           ((v (= (iff x y) nil)
               (= (if x nil t) (if y nil t)))         (build.instantiation @- (@sigma (a . nil) (b . t)))  *2c)

           ;; ---

           ((v (v (!= z nil)
                  (= (iff x y) nil))
               (= (iff z x) (if x nil t)))            (build.multi-assoc-expansion *2a (@formulas (!= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (v (!= z nil)
                  (= (iff x y) nil))
               (= (if x nil t) (if y nil t)))         (build.multi-assoc-expansion *2c (@formulas (!= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (v (!= z nil)
                  (= (iff x y) nil))
               (= (iff z x) (if y nil t)))            (build.disjoined-transitivity-of-pequal @-- @-))

           ((v (v (!= z nil)
                  (= (iff x y) nil))
               (= (if y nil t) (iff z y)))            (build.multi-assoc-expansion *2b (@formulas (!= z nil)
                                                                                                  (= (iff x y) nil))))

           ((v (v (!= z nil)
                  (= (iff x y) nil))
               (= (iff z x) (iff z y)))               (build.disjoined-transitivity-of-pequal @-- @-))

           ((v (!= z nil)
               (v (= (iff x y) nil)
                  (= (iff z x) (iff z y))))           (build.right-associativity @-)  *2)

           ;; ------------------

           ((v (v (= (iff x y) nil)
                  (= (iff z x) (iff z y)))
               (v (= (iff x y) nil)
                  (= (iff z x) (iff z y))))           (build.cut *1 *2))

           ((v (= (iff x y) nil)
               (= (iff z x) (iff z y)))            (build.contraction @-)))

  :minatbl ((iff . 2)
            (if . 3)))

(deftheorem theorem-iff-congruent-iff-1
  :derive (v (= (iff x y) nil)
             (= (iff x z) (iff y z)))
  :proof (@derive
          ((= (iff x y) (iff y x))                         (build.theorem (theorem-symmetry-of-iff)))
          ((= (iff z y) (iff y z))                         (build.instantiation @- (@sigma (x . z) (y . y))))
          ((= (iff z x) (iff x z))                         (build.instantiation @-- (@sigma (x . z) (y . x))))
          ((v (= (iff x y) nil)
              (= (iff z y) (iff y z)))                     (build.expansion (@formula (= (iff x y) nil)) @--) *1a)
          ((v (= (iff x y) nil)
              (= (iff z x) (iff x z)))                     (build.expansion (@formula (= (iff x y) nil)) @--) *1b)
          ((v (= (iff x y) nil)
              (= (iff z x) (iff z y)))                     (build.theorem (theorem-iff-congruent-iff-2)))
          ((v (= (iff x y) nil)
              (= (iff z x) (iff y z)))                     (build.disjoined-transitivity-of-pequal @- *1a))
          ((v (= (iff x y) nil)
              (= (iff y z) (iff z x)))                     (build.disjoined-commute-pequal @-))
          ((v (= (iff x y) nil)
              (= (iff y z) (iff x z)))                     (build.disjoined-transitivity-of-pequal @- *1b))
          ((v (= (iff x y) nil)
              (= (iff x z) (iff y z)))                     (build.disjoined-commute-pequal @-)))
  :minatbl ((iff . 2)
            (if . 3)))



;; TRANSITIVITY.
;;
;; With these congruence rules in place, transitivity is straightforward.  As
;; usual we prove a theorem which we can just instantiate with modus ponens to
;; keep proof sizes down.

(deftheorem theorem-transitivity-of-iff
  :derive (v (!= (iff x y) t)
             (v (!= (iff y z) t)
                (= (iff x z) t)))
  :proof (@derive
          ((v (= (iff x y) nil) (= (iff x z) (iff y z)))    (build.theorem (theorem-iff-congruent-iff-1)))
          ((v (= (iff x z) (iff y z)) (= (iff x y) nil))    (build.commute-or @-))
          ((v (= (iff x z) (iff y z)) (!= (iff x y) t))     (build.disjoined-not-t-from-nil @-))
          ((v (!= (iff x y) t) (= (iff x z) (iff y z)))     (build.commute-or @-))

          ((v (v (!= (iff x y) t)
                 (!= (iff y z) t))
              (= (iff x z) (iff y z)))                      (build.multi-assoc-expansion @- (@formulas (!= (iff x y) t)
                                                                                                       (!= (iff y z) t))) *1)


          ((v (!= (iff y z) t) (= (iff y z) t))             (build.propositional-schema (@formula (= (iff y z) t))))

          ((v (v (!= (iff x y) t)
                 (!= (iff y z) t))
              (= (iff y z) t))                              (build.multi-assoc-expansion @- (@formulas (!= (iff x y) t)
                                                                                                       (!= (iff y z) t))))
          ((v (v (!= (iff x y) t)
                 (!= (iff y z) t))
              (= (iff x z) t))                              (build.disjoined-transitivity-of-pequal *1 @-))

          ((v (!= (iff x y) t)
              (v (!= (iff y z) t)
                 (= (iff x z) t)))                          (build.right-associativity @-)))

  :minatbl ((iff . 2)
            (if . 3)))

(defderiv build.transitivity-of-iff
 :derive (= (iff (? a) (? c)) t)
 :from   ((proof x (= (iff (? a) (? b)) t))
          (proof y (= (iff (? b) (? c)) t)))
 :proof  (@derive
          ((v (!= (iff x y) t)
              (v (!= (iff y z) t)
                 (= (iff x z) t)))            (build.theorem (theorem-transitivity-of-iff)))

          ((v (!= (iff (? a) (? b)) t)
              (v (!= (iff (? b) (? c)) t)
                 (= (iff (? a) (? c)) t)))    (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c))))   *1)

          ((= (iff (? a) (? b)) t)            (@given x))

          ((v (!= (iff (? b) (? c)) t)
              (= (iff (? a) (? c)) t))        (build.modus-ponens @- *1) *2)

          ((= (iff (? b) (? c)) t)            (@given y))

          ((= (iff (? a) (? c)) t)            (build.modus-ponens @- *2))))

(defderiv build.disjoined-transitivity-of-iff
 :derive (v P (= (iff (? a) (? c)) t))
 :from   ((proof x (v P (= (iff (? a) (? b)) t)))
          (proof y (v P (= (iff (? b) (? c)) t))))
 :proof  (@derive
          ((v (!= (iff x y) t)
              (v (!= (iff y z) t)
                 (= (iff x z) t)))                  (build.theorem (theorem-transitivity-of-iff)))

          ((v (!= (iff (? a) (? b)) t)
              (v (!= (iff (? b) (? c)) t)
                 (= (iff (? a) (? c)) t)))          (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))

          ((v P (v (!= (iff (? a) (? b)) t)
                   (v (!= (iff (? b) (? c)) t)
                      (= (iff (? a) (? c)) t))))    (build.expansion (@formula P) @-))

          ((v P (= (iff (? a) (? b)) t))            (@given x))

          ((v P (v (!= (iff (? b) (? c)) t)
                   (= (iff (? a) (? c)) t)))        (build.disjoined-modus-ponens @- @--))

          ((v P (= (iff (? b) (? c)) t))            (@given y))

          ((v P (!= (iff (? a) (? c)) t))           (build.disjoined-modus-ponens @- @--))))



;; REFINEMENT.
;;
;; A trivial consequence of reflexivity is that any time x = y, (iff x y) also
;; holds.  It is useful to be able to switch from an equality into an iff.
;; Similarly, if (equal x y) = t, then (iff x y) = t.

(deftheorem theorem-iff-from-pequal
 :derive (v (!= x y) (= (iff x y) t))
 :proof  (@derive
          ((= x x)                                                              (build.reflexivity 'x))
          ((v (!= x y) (= x x))                                                 (build.expansion (@formula (!= x y)) @-)        *1a)
          ((v (!= x y) (= x y))                                                 (build.propositional-schema (@formula (= x y))))
          ((v (!= x y) (= y x))                                                 (build.disjoined-commute-pequal @-)             *1b)
          ((v (!= x y) (= (iff x y) (iff x x)))                                 (build.disjoined-pequal-by-args 'iff
                                                                                                                (@formula (!= x y))
                                                                                                                (list *1a *1b))  *1)
          ((= (iff x x) t)                                                      (build.theorem (theorem-reflexivity-of-iff)))
          ((v (!= x y) (= (iff x x) t))                                         (build.expansion (@formula (!= x y)) @-))
          ((v (!= x y) (= (iff x y) t))                                         (build.disjoined-transitivity-of-pequal *1 @-)))
 :minatbl ((iff . 2)))

(defderiv build.iff-from-pequal
  :derive (= (iff (? a) (? b)) t)
  :from   ((proof x (= (? a) (? b))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use iff reflexivity.
                 (@derive
                  ((= (iff (? a) (? b)) t)                                      (build.iff-reflexivity (@term (? a))))))
                (t
                 (@derive
                  ((v (!= x y) (= (iff x y) t))                                 (build.theorem (theorem-iff-from-pequal)))
                  ((v (!= (? a) (? b)) (= (iff (? a) (? b)) t))                 (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                  ((= (? a) (? b))                                              (@given x))
                  ((= (iff (? a) (? b)) t)                                      (build.modus-ponens @- @--)))))
  :minatbl ((iff . 2))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (build.iff-reflexivity (@term (? a)))
                        (LOGIC.APPEAL 'BUILD.IFF-FROM-PEQUAL
                                      (@FORMULA (= (IFF (? A) (? B)) T))
                                      (LIST X)
                                      NIL)))

(defderiv build.disjoined-iff-from-pequal
 :derive (v P (= (iff (? a) (? b)) t))
 :from   ((proof x (v P (= (? a) (? b)))))
 :proof  (cond ((equal (@term (? a)) (@term (? b)))
                ;; Optimization.  We can just use iff-reflexivity and expansion.
                (@derive
                 ((= (iff (? a) (? b)) t)                                       (build.iff-reflexivity (@term (? a))))
                 ((v P (= (iff (? a) (? b)) t))                                 (build.expansion (@formula P) @-))))
               (t
                (@derive
                 ((v (!= x y) (= (iff x y) t))                                  (build.theorem (theorem-iff-from-pequal)))
                 ((v (!= (? a) (? b)) (= (iff (? a) (? b)) t))                  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                 ((v P (v (!= (? a) (? b)) (= (iff (? a) (? b)) t)))            (build.expansion (@formula P) @-))
                 ((v P (= (? a) (? b)))                                         (@given x))
                 ((v P (= (iff (? a) (? b)) t))                                 (build.disjoined-modus-ponens @- @--)))))
 :minatbl ((iff . 2))
 :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                         (@derive ((= (iff (? a) (? b)) t)           (build.iff-reflexivity (@term (? a))))
                                  ((v P (= (iff (? a) (? b)) t))     (build.expansion (@formula P) @-)))
                       (LOGIC.APPEAL 'BUILD.DISJOINED-IFF-FROM-PEQUAL
                                     (@FORMULA (V P (= (IFF (? A) (? B)) T)))
                                     (LIST X)
                                     NIL)))



(deftheorem theorem-iff-from-equal
  :derive (v (!= (equal x y) t) (= (iff x y) t))
  :proof  (@derive ((v (= x y) (= (equal x y) nil))                             (build.axiom (axiom-equal-when-diff)))
                   ((v (= x y) (!= (equal x y) t))                              (build.disjoined-not-t-from-nil @-))
                   ((v (!= x y) (= (iff x y) t))                                (build.theorem (theorem-iff-from-pequal)))
                   ((v (!= (equal x y) t) (= (iff x y) t))                      (build.cut @-- @-)))
  :minatbl ((iff . 2)
            (equal . 2)))

(defderiv build.iff-from-equal
 :derive (= (iff (? a) (? b)) t)
 :from   ((proof x (= (equal (? a) (? b)) t)))
 :proof  (cond ((equal (@term (? a)) (@term (? b)))
                ;; Optimization.  Just use iff reflexivity.
                (@derive ((= (iff (? a) (? b)) t)                               (build.iff-reflexivity (@term (? a))))))
               (t
                (@derive
                 ((v (!= (equal x y) t) (= (iff x y) t))                        (build.theorem (theorem-iff-from-equal)))
                 ((v (!= (equal (? a) (? b)) t) (= (iff (? a) (? b)) t))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                 ((= (equal (? a) (? b)) t)                                     (@given x))
                 ((= (iff (? a) (? b)) t)                                       (build.modus-ponens @- @--)))))
 :minatbl ((iff . 2))
 :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                         (build.iff-reflexivity (@term (? a)))
                       (LOGIC.APPEAL 'BUILD.IFF-FROM-EQUAL
                                     (@FORMULA (= (IFF (? A) (? B)) T))
                                     (LIST X)
                                     NIL)))

(defderiv build.disjoined-iff-from-equal
 :derive (v P (= (iff (? a) (? b)) t))
 :from   ((proof x (v P (= (equal (? a) (? b)) t))))
 :proof  (cond ((equal (@term (? a)) (@term (? b)))
                ;; Optimization.  We can just use iff-reflexivity and expansion.
                (@derive ((= (iff (? a) (? b)) t)                               (build.iff-reflexivity (@term (? a))))
                         ((v P (= (iff (? a) (? b)) t))                         (build.expansion (@formula P) @-))))
               (t
                (@derive
                 ((v (!= (equal x y) t) (= (iff x y) t))                        (build.theorem (theorem-iff-from-equal)))
                 ((v (!= (equal (? a) (? b)) t) (= (iff (? a) (? b)) t))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                 ((v P (v (!= (equal (? a) (? b)) t) (= (iff (? a) (? b)) t)))  (build.expansion (@formula P) @-))
                 ((v P (= (equal (? a) (? b)) t))                               (@given x))
                 ((v P (= (iff (? a) (? b)) t))                                 (build.disjoined-modus-ponens @- @--)))))
 :minatbl ((iff . 2))
 :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                         (@derive ((= (iff (? a) (? b)) t)         (build.iff-reflexivity (@term (? a))))
                                  ((v P (= (iff (? a) (? b)) t))   (build.expansion (@formula P) @-)))
                       (LOGIC.APPEAL 'BUILD.DISJOINED-IFF-FROM-EQUAL
                                     (@FORMULA (V P (= (IFF (? A) (? B)) T)))
                                     (LIST X)
                                     NIL)))




;; Note: we leave build.equiv-reflexivity enabled

(defun build.equiv-reflexivity (x iffp)
  (declare (xargs :guard (and (logic.termp x)
                              (booleanp iffp))))
  (if iffp
      (build.iff-reflexivity x)
    (build.equal-reflexivity x)))

(in-theory (disable (:executable-counterpart build.equiv-reflexivity)))

(defobligations build.equiv-reflexivity
  (build.iff-reflexivity build.equal-reflexivity))


(dd.close)




;; OLD JUNK ---------------------------------------













;; (deftheorem theorem-iff-lhs-t-base
;;   :derive (= (iff t x) (if x t nil))
;;   :proof  (@derive
;;            ((= (iff x y) (if x (if y t nil) (if y nil t)))                   (build.axiom (definition-of-iff)))
;;            ((= (iff t x) (if t (if x t nil) (if x nil t)))                   (build.instantiation @- (@sigma (x . t) (y . x))))
;;            ((= (if t (if x t nil) (if x nil t)) (if x t nil))                (build.if-of-t (@term (if x t nil)) (@term (if x nil t))))
;;            ((= (iff t x) (if x t nil))                                       (build.transitivity-of-pequal @-- @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (deftheorem theorem-iff-rhs-t-base
;;  :derive (= (iff x t) (if x t nil))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;           ((= (iff x t) (if x (if t t nil) (if t nil t)))                    (build.instantiation @- (@sigma (y . t)))   *1)
;;           ((= x x)                                                           (build.reflexivity (@term x))  *2a)
;;           ((= (if t t nil) t)                                                (build.if-of-t (@term t) (@term nil)) *2b)
;;           ((= (if t nil t) nil)                                              (build.if-of-t (@term nil) (@term t)) *2c)
;;           ((= (if x (if t t nil) (if t nil t)) (if x t nil))                 (build.pequal-by-args 'if (list *2a *2b *2c)))
;;           ((= (iff x t) (if x t nil))                                        (build.transitivity-of-pequal *1 @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-lhs-nil-base
;;   :derive (= (iff nil x) (if x nil t))
;;   :proof  (@derive
;;            ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;            ((= (iff nil x) (if nil (if x t nil) (if x nil t)))                (build.instantiation @- (@sigma (x . nil) (y . x))) *1)
;;            ((= (if nil (if x t nil) (if x nil t)) (if x nil t))               (build.if-of-nil (@term (if x t nil)) (@term (if x nil t))))
;;            ((= (if nil x) (if x nil t))                                       (build.transitivity-of-pequal @-- @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (deftheorem theorem-iff-rhs-nil-base
;;   :derive (= (iff x nil) (if x nil t))
;;   :proof (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;           ((= (iff x nil) (if x (if nil t nil) (if nil nil t)))              (build.instantiation @- (@sigma (y . nil)))   *1)
;;           ((= x x)                                                           (build.reflexivity (@term x))  *2a)
;;           ((= (if nil t nil) nil)                                            (build.if-of-nil (@term t) (@term nil)) *2b)
;;           ((= (if nil nil t) t)                                              (build.if-of-nil (@term nil) (@term t)) *2c)
;;           ((= (if x (if t t nil) (if t nil t)) (if x nil t))                 (build.pequal-by-args 'if (list *2a *2b *2c)))
;;           ((= (iff x nil) (if x nil t))                                      (build.transitivity-of-pequal *1 @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-move-t-right
;;   :derive (= (iff t x) (iff x t))
;;   :proof  (@derive
;;            ((= (iff x t) (if x t nil))    (build.theorem (theorem-iff-rhs-t-base)))
;;            ((= (if x t nil) (iff x t))    (build.commute-pequal @-))
;;            ((= (iff t x) (if x t nil))    (build.theorem (theorem-iff-lhs-t-base)))
;;            ((= (iff t x) (iff x t))       (build.transitivity-of-pequal @- @--)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (deftheorem theorem-iff-move-nil-right
;;   :derive (= (iff nil x) (iff x nil))
;;   :proof  (@derive
;;            ((= (iff x nil) (if x nil t))    (build.theorem (theorem-iff-rhs-nil-base)))
;;            ((= (if x nil t) (iff x nil))    (build.commute-pequal @-))
;;            ((= (iff nil x) (if x nil t))    (build.theorem (theorem-iff-lhs-nil-base)))
;;            ((= (iff nil x) (iff x nil))     (build.transitivity-of-pequal @- @--)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))














;; (deftheorem theorem-iff-lhs-t-1
;;   :derive (v (= x nil) (= (iff t x) t))
;;   :proof (@derive
;;           ((= (iff t x) (if x t nil))                                       (build.theorem (theorem-iff-lhs-t-base)))
;;           ((v (= x nil) (= (iff t x) (if x t nil)))                         (build.expansion (@formula (= x nil)) @-)  *1)
;;           ((v (!= x nil) (= x nil))                                         (build.propositional-schema (@formula (= x nil))))
;;           ((v (= x nil) (!= x nil))                                         (build.commute-or @-))
;;           ((v (= x nil) (= (if x t nil) t))                                 (build.disjoined-if-when-not-nil @- (@term t) (@term nil)))
;;           ((v (= x nil) (= (iff t x) t))                                    (build.disjoined-transitivity-of-pequal *1 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (deftheorem theorem-iff-rhs-t-1
;;   :derive (v (= x nil) (= (iff x t) t))
;;   :proof (@derive
;;           ((= (iff x t) (if x t nil))                                       (build.theorem (theorem-iff-rhs-t-base)))
;;           ((v (= x nil) (= (iff x t) (if x t nil)))                         (build.expansion (@formula (= x nil)) @-)  *1)
;;           ((v (!= x nil) (= x nil))                                         (build.propositional-schema (@formula (= x nil))))
;;           ((v (= x nil) (!= x nil))                                         (build.commute-or @-))
;;           ((v (= x nil) (= (if x t nil) t))                                 (build.disjoined-if-when-not-nil @- (@term t) (@term nil)))
;;           ((v (= x nil) (= (iff x t) t))                                    (build.disjoined-transitivity-of-pequal *1 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))


;; (deftheorem theorem-iff-lhs-t-2
;;   :derive (v (!= x nil) (= (iff t x) nil))
;;   :proof (@derive
;;           ((= (iff t x)  (if x t nil))                                       (build.theorem (theorem-iff-lhs-t-base)))
;;           ((v (!= x nil) (= (iff t x) (if x t nil)))                         (build.expansion (@formula (!= x nil)) @-)  *1)
;;           ((v (!= x nil) (= x nil))                                          (build.propositional-schema (@formula (= x nil))))
;;           ((v (!= x nil) (= (if x t nil) nil))                               (build.disjoined-if-when-nil @- (@term t) (@term nil)))
;;           ((v (!= x nil) (= (iff t x) nil))                                  (build.disjoined-transitivity-of-pequal *1 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (deftheorem theorem-iff-rhs-t-2
;;   :derive (v (!= x nil) (= (iff x t) nil))
;;   :proof (@derive
;;           ((= (iff x t) (if x t nil))                                        (build.theorem (theorem-iff-rhs-t-base)))
;;           ((v (!= x nil) (= (iff x t) (if x t nil)))                         (build.expansion (@formula (!= x nil)) @-)  *1)
;;           ((v (!= x nil) (= x nil))                                          (build.propositional-schema (@formula (= x nil))))
;;           ((v (!= x nil) (= (if x t nil) nil))                               (build.disjoined-if-when-nil @- (@term t) (@term nil)))
;;           ((v (!= x nil) (= (iff x t) nil))                                  (build.disjoined-transitivity-of-pequal *1 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))



;; (defderiv build.intro-iff-rhs-t-1
;;   :derive (= (iff (? a) t) t)
;;   :from   ((proof x (!= (? a) nil)))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x t) t))          (build.theorem (theorem-iff-rhs-t-1)))
;;            ((v (= (? a) nil) (= (iff (? a) t) t))  (build.instantiation @- (@sigma (x . (? a)))))
;;            ((!= (? a) nil)                         (@given x))
;;            ((= (iff (? a) t) t)                    (build.modus-ponens-2 @- @--)))
;;   :minatbl ((iff . 2)))

;; (defderiv build.disjoined-intro-iff-rhs-t-1
;;   :derive (v P (= (iff (? a) t) t))
;;   :from   ((proof x (v P (!= (? a) nil))))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x t) t))               (build.theorem (theorem-iff-rhs-t-1)))
;;            ((v (= (? a) nil) (= (iff (? a) t) t))       (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v P (v (= (? a) nil) (= (iff (? a) t) t))) (build.expansion (@formula P) @-))
;;            ((v P (!= (? a) nil))                        (@given x))
;;            ((v P (= (iff (? a) t) t))                   (build.disjoined-modus-ponens-2 @- @--)))
;;   :minatbl ((iff . 2)))

;; (defderiv build.elim-iff-rhs-t-2
;;   :derive (!= (? a) nil)
;;   :from   ((proof x (!= (iff (? a) t) nil)))
;;   :proof  (@derive
;;            ((v (!= x nil) (= (iff x t) nil))          (build.theorem (theorem-iff-rhs-t-2)))
;;            ((v (!= (? a) nil) (= (iff (? a) t) nil))  (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) t) nil) (!= (? a) nil))  (build.commute-or @-))
;;            ((!= (iff (? a) t) nil)                    (@given x))
;;            ((!= (? a) nil)                            (build.modus-ponens-2 @- @--))))

;; (defderiv build.disjoined-elim-iff-rhs-t-2
;;   :derive (v P (!= (? a) nil))
;;   :from   ((proof x (v P (!= (iff (? a) t) nil))))
;;   :proof  (@derive
;;            ((v (!= x nil) (= (iff x t) nil))                (build.theorem (theorem-iff-rhs-t-2)))
;;            ((v (!= (? a) nil) (= (iff (? a) t) nil))        (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) t) nil) (!= (? a) nil))        (build.commute-or @-))
;;            ((v P (v (= (iff (? a) t) nil) (!= (? a) nil)))  (build.expansion (@formula P) @-))
;;            ((v P (!= (iff (? a) t) nil))                    (@given x))
;;            ((v P (!= (? a) nil))                            (build.disjoined-modus-ponens-2 @- @--))))





;; (deftheorem theorem-iff-rhs-nil-1
;;    :derive (v (= x nil) (= (iff x nil) nil))
;;    :proof  (@derive
;;             ((= (iff x nil) (if x nil t))                   (build.theorem (theorem-iff-rhs-nil-base)))
;;             ((v (= x nil) (= (iff x nil) (if x nil t)))     (build.expansion (@formula (= x nil)) @-) *1)
;;             ((v (!= x nil) (= x nil))                       (build.propositional-schema (@formula (= x nil))))
;;             ((v (= x nil) (!= x nil))                       (build.commute-or @-))
;;             ((v (= x nil) (= (if x nil t) t))               (build.disjoined-if-when-not-nil @- (@term nil) (@term t)))
;;             ((v (= x nil) (= (iff x nil) t))                (build.disjoined-transitivity-of-pequal *1 @-)))
;;    :minatbl ((if . 3)
;;              (iff . 2)))

;; (deftheorem theorem-iff-rhs-nil-1
;;    :derive (v (= x nil) (= (iff x nil) nil))
;;    :proof  (@derive
;;             ((= (iff x nil) (if x nil t))                   (build.theorem (theorem-iff-rhs-nil-base)))
;;             ((v (= x nil) (= (iff x nil) (if x nil t)))     (build.expansion (@formula (= x nil)) @-) *1)
;;             ((v (!= x nil) (= x nil))                       (build.propositional-schema (@formula (= x nil))))
;;             ((v (= x nil) (!= x nil))                       (build.commute-or @-))
;;             ((v (= x nil) (= (if x nil t) t))               (build.disjoined-if-when-not-nil @- (@term nil) (@term t)))
;;             ((v (= x nil) (= (iff x nil) t))                (build.disjoined-transitivity-of-pequal *1 @-)))
;;    :minatbl ((if . 3)
;;              (iff . 2)))

;; (deftheorem theorem-iff-rhs-nil-2
;;    :derive (v (!= x nil) (= (iff x nil) t))
;;    :proof  (@derive
;;             ((= (iff x nil) (if x nil t))                   (build.theorem (theorem-iff-rhs-nil-base)))
;;             ((v (!= x nil) (= (iff x nil) (if x nil t)))    (build.expansion (@formula (!= x nil)) @-) *1)
;;             ((v (!= x nil) (= x nil))                       (build.propositional-schema (@formula (= x nil))))
;;             ((v (!= x nil) (= (if x nil t) t))              (build.disjoined-if-when-nil @- (@term nil) (@term t)))
;;             ((v (!= x nil) (= (iff x nil) t))               (build.disjoined-transitivity-of-pequal *1 @-)))
;;    :minatbl ((if . 3)
;;              (iff . 2)))


;; (defderiv build.elim-iff-rhs-nil-pequal-nil-from-iff-nil
;;   :derive (= (? a) nil)
;;   :from   ((proof x (!= (iff (? a) nil) nil)))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x nil) nil))          (build.theorem (theorem-iff-nil-when-not-nil)))
;;            ((v (= (? a) nil) (= (iff (? a) nil) nil))  (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) nil) nil) (= (? a) nil))  (build.commute-or @-))
;;            ((!= (iff (? a) nil) nil)                   (@given x))
;;            ((= (? a) nil)                              (build.modus-ponens-2 @- @--))))

;; (defderiv build.disjoined-pequal-nil-from-iff-nil
;;   :derive (v P (= (? a) nil))
;;   :from   ((proof x (v P (!= (iff (? a) nil) nil))))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x nil) nil))                 (build.theorem (theorem-iff-nil-when-not-nil)))
;;            ((v (= (? a) nil) (= (iff (? a) nil) nil))         (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) nil) nil) (= (? a) nil))         (build.commute-or @-))
;;            ((v P (v (= (iff (? a) nil) nil) (= (? a) nil)))   (build.expansion (@formula P) @-))
;;            ((v P (!= (iff (? a) nil) nil))                    (@given x))
;;            ((v P (= (? a) nil))                               (build.disjoined-modus-ponens-2 @- @--))))








;; (deftheorem theorem-iff-t-when-nil-rhs
;;   :derive (v (!= x nil) (= (iff x t) nil))
;;   :proof (@derive
;;           ((= (iff x nil)
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;           ((= (iff x t) (if x (if t t nil) (if t nil t)))                    (build.instantiation @- (@sigma (y . t)))   *1)
;;           ;; ---
;;           ((= x x)                                                           (build.reflexivity (@term x))  *2a)
;;           ((= (if t t nil) t)                                                (build.if-of-t (@term t) (@term nil)) *2b)
;;           ((= (if t nil t) nil)                                              (build.if-of-t (@term nil) (@term t)) *2c)
;;           ((= (if x (if t t nil) (if t nil t)) (if x t nil))                 (build.pequal-by-args 'if (list *2a *2b *2c)))
;;           ((= (iff x t) (if x t nil))                                        (build.transitivity-of-pequal *1 @-))
;;           ((v (!= x nil) (= (iff x t) (if x t nil)))                         (build.expansion (@formula (!= x nil)) @-)  *2)
;;           ;; ---
;;           ((v (!= x nil) (= x nil))                                          (build.propositional-schema (@formula (= x nil))))
;;           ((v (!= x nil) (= (if x t nil) nil))                               (build.disjoined-if-when-nil @- (@term t) (@term nil)))
;;           ((v (!= x nil) (= (iff x t) nil))                                  (build.disjoined-transitivity-of-pequal *2 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))


;;  :proof  (@derive
;;           ((v (= x nil) (= (if x y z) y))             (build.axiom (axiom-if-when-not-nil)))
;;           ((v (= x nil) (= (if x t nil) t))           (build.instantiation @- (@sigma (y . t) (z . nil))))
;;           ((v (= x nil) (= t (if x t nil)))           (build.disjoined-commute-pequal @-))
;;           ((v (= x nil) (= (iff x t) t))              (build.theorem (theorem-iff-t-when-not-nil)))
;;           ((v (= x nil) (= (iff x t) (if x t nil)))   (build.disjoined-transitivity-of-pequal @- @--)  *1)
;;           ;; ---
;;           ((v (!= x nil) (= (if x y z) z))            (build.axiom (axiom-if-when-nil)))
;;           ((v (!= x nil) (= (if x t nil) nil))        (build.instantiation @- (@sigma (y . t) (z . nil))))
;;           ((v (!= x nil) (= nil (if x t nil)))        (build.disjoined-commute-pequal @-))
;;           ((v (!= x nil) (= (iff x t) nil))           (build.theorem (theorem-iff-t-when-nil)))
;;           ((v (!= x nil) (= (iff x t) (if x t nil)))  (build.disjoined-transitivity-of-pequal @- @--)  *2)
;;           ;; ---
;;           ((v (= (iff x t) (if x t nil))
;;               (= (iff x t) (if x t nil)))             (build.cut *1 *2))
;;           ((= (iff x t) (if x t nil))                 (build.contraction @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-of-nil
;;  :derive (= (iff x nil) (equal x nil))
;;  :proof  (@derive
;;           ((v (= x y)   (= (equal x y) nil))             (build.axiom (axiom-equal-when-diff)))
;;           ((v (= x nil) (= (equal x nil) nil))           (build.instantiation @- (@sigma (y . nil))))
;;           ((v (= x nil) (= nil (equal x nil)))           (build.disjoined-commute-pequal @-))
;;           ((v (= x nil) (= (iff x nil) nil))             (build.theorem (theorem-iff-nil-when-not-nil)))
;;           ((v (= x nil) (= (iff x nil) (equal x nil)))   (build.disjoined-transitivity-of-pequal @- @--)  *1)
;;           ;; ---
;;           ((v (!= x y)   (= (equal x y) t))              (build.axiom (axiom-equal-when-same)))
;;           ((v (!= x nil) (= (equal x nil) t))            (build.instantiation @- (@sigma (y . nil))))
;;           ((v (!= x nil) (= t (equal x nil)))            (build.disjoined-commute-pequal @-))
;;           ((v (!= x nil) (= (iff x nil) t))              (build.theorem (theorem-iff-nil-when-nil)))
;;           ((v (!= x nil) (= (iff x nil) (equal x nil)))  (build.disjoined-transitivity-of-pequal @- @--)  *2)
;;           ;; ---
;;           ((v (= (iff x nil) (equal x nil))
;;               (= (iff x nil) (equal x nil)))             (build.cut *1 *2))
;;           ((= (iff x nil) (equal x nil))                 (build.contraction @-)))
;;  :minatbl ((equal . 2)
;;            (iff . 2)))






;; (deftheorem theorem-if-of-t
;; (= (iff x t) (if x t nil)


;; (deftheorem theorem-iff-t-when-nil
;;   :derive (v (!= x nil) (= (iff x t) nil))
;;   :proof (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;           ((= (iff x t) (if x (if t t nil) (if t nil t)))                    (build.instantiation @- (@sigma (y . t)))   *1)
;;           ;; ---
;;           ((= x x)                                                           (build.reflexivity (@term x))  *2a)
;;           ((= (if t t nil) t)                                                (build.if-of-t (@term t) (@term nil)) *2b)
;;           ((= (if t nil t) nil)                                              (build.if-of-t (@term nil) (@term t)) *2c)
;;           ((= (if x (if t t nil) (if t nil t)) (if x t nil))                 (build.pequal-by-args 'if (list *2a *2b *2c)))
;;           ((= (iff x t) (if x t nil))                                        (build.transitivity-of-pequal *1 @-))
;;           ((v (!= x nil) (= (iff x t) (if x t nil)))                         (build.expansion (@formula (!= x nil)) @-)  *2)
;;           ;; ---
;;           ((v (!= x nil) (= x nil))                                          (build.propositional-schema (@formula (= x nil))))
;;           ((v (!= x nil) (= (if x t nil) nil))                               (build.disjoined-if-when-nil @- (@term t) (@term nil)))
;;           ((v (!= x nil) (= (iff x t) nil))                                  (build.disjoined-transitivity-of-pequal *2 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))




;; (deftheorem theorem-iff-t-when-not-nil
;;   :derive (v (= x nil) (= (iff x t) t))
;;   :proof  (@derive
;;            ((= (iff x y) (if x (if y t nil) (if y nil t)))                    (build.axiom (definition-of-iff)))
;;            ((= (iff x t) (if x (if t t nil) (if t nil t)))                    (build.instantiation @- (@sigma (y . t))))
;;            ((v (= x nil) (= (iff x t) (if x (if t t nil) (if t nil t))))      (build.expansion (@formula (= x nil)) @-)                                *1)
;;            ;; ---
;;            ((v (= x nil) (= (if x y z) y))                                    (build.axiom (axiom-if-when-not-nil)))
;;            ((v (= x nil) (= (if x (if t t nil) (if t nil t)) (if t t nil)))   (build.instantiation @- (@sigma (y . (if t t nil)) (z . (if t nil t))))  *2)
;;            ;; ---
;;            ((= (if t y z) y)                                                  (build.theorem (theorem-if-redux-t)))
;;            ((= (if t t nil) t)                                                (build.instantiation @- (@sigma (y . t) (z . nil))))
;;            ((v (= x nil) (= (if t t nil) t))                                  (build.expansion (@formula (= x nil)) @-))
;;            ((v (= x nil) (= (if x (if t t nil) (if t nil t)) t))              (build.disjoined-transitivity-of-pequal *2 @-))
;;            ((v (= x nil) (= (iff x t) t))                                     (build.disjoined-transitivity-of-pequal *1 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))


;; (deftheorem theorem-iff-nil-when-nil
;;  :derive (v (!= x nil) (= (iff x nil) t))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                            (build.axiom (definition-of-iff)))
;;           ((= (iff x nil) (if x (if nil t nil) (if nil nil t)))                      (build.instantiation @- (@sigma (y . nil))))
;;           ((v (!= x nil) (= (iff x nil) (if x (if nil t nil) (if nil nil t))))       (build.expansion (@formula (!= x nil)) @-)                                   *1)
;;           ;; ---
;;           ((v (!= x nil) (= (if x y z) z))                                           (build.axiom (axiom-if-when-nil)))
;;           ((v (!= x nil) (= (if x (if nil t nil) (if nil nil t)) (if nil nil t)))    (build.instantiation @- (@sigma (y . (if nil t nil)) (z . (if nil nil t))))  *2)
;;           ;; ---
;;           ((= (if nil y z) z)                                                        (build.theorem (theorem-if-redux-nil)))
;;           ((= (if nil nil t) t)                                                      (build.instantiation @- (@sigma (y . nil) (z . t))))
;;           ((v (!= x nil) (= (if nil nil t) t))                                       (build.expansion (@formula (!= x nil)) @-))
;;           ((v (!= x nil) (= (if x (if nil t nil) (if nil nil t)) t))                 (build.disjoined-transitivity-of-pequal *2 @-))
;;           ((v (!= x nil) (= (iff x nil) t))                                          (build.disjoined-transitivity-of-pequal *1 @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-nil-when-not-nil
;;  :derive (v (= x nil) (= (iff x nil) nil))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                           (build.axiom (definition-of-iff)))
;;           ((= (iff x nil) (if x (if nil t nil) (if nil nil t)))                     (build.instantiation @- (@sigma (y . nil))))
;;           ((v (= x nil) (= (iff x nil) (if x (if nil t nil) (if nil nil t))))       (build.expansion (@formula (= x nil)) @-)                                    *1)
;;           ;; ---
;;           ((v (= x nil) (= (if x y z) y))                                           (build.axiom (axiom-if-when-not-nil)))
;;           ((v (= x nil) (= (if x (if nil t nil) (if nil nil t)) (if nil t nil)))    (build.instantiation @- (@sigma (y . (if nil t nil)) (z . (if nil nil t))))  *2)
;;           ;; ---
;;           ((= (if nil y z) z)                                                       (build.theorem (theorem-if-redux-nil)))
;;           ((= (if nil t nil) nil)                                                   (build.instantiation @- (@sigma (y . t) (z . nil))))
;;           ((v (= x nil) (= (if nil t nil) nil))                                     (build.expansion (@formula (= x nil)) @-))
;;           ((v (= x nil) (= (if x (if nil t nil) (if nil nil t)) nil))               (build.disjoined-transitivity-of-pequal *2 @-))
;;           ((v (= x nil) (= (iff x nil) nil))                                        (build.disjoined-transitivity-of-pequal *1 @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (defderiv build.pequal-nil-from-iff-nil
;;   :derive (= (? a) nil)
;;   :from   ((proof x (!= (iff (? a) nil) nil)))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x nil) nil))          (build.theorem (theorem-iff-nil-when-not-nil)))
;;            ((v (= (? a) nil) (= (iff (? a) nil) nil))  (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) nil) nil) (= (? a) nil))  (build.commute-or @-))
;;            ((!= (iff (? a) nil) nil)                   (@given x))
;;            ((= (? a) nil)                              (build.modus-ponens-2 @- @--))))

;; (defderiv build.disjoined-pequal-nil-from-iff-nil
;;   :derive (v P (= (? a) nil))
;;   :from   ((proof x (v P (!= (iff (? a) nil) nil))))
;;   :proof  (@derive
;;            ((v (= x nil) (= (iff x nil) nil))                 (build.theorem (theorem-iff-nil-when-not-nil)))
;;            ((v (= (? a) nil) (= (iff (? a) nil) nil))         (build.instantiation @- (@sigma (x . (? a)))))
;;            ((v (= (iff (? a) nil) nil) (= (? a) nil))         (build.commute-or @-))
;;            ((v P (v (= (iff (? a) nil) nil) (= (? a) nil)))   (build.expansion (@formula P) @-))
;;            ((v P (!= (iff (? a) nil) nil))                    (@given x))
;;            ((v P (= (? a) nil))                               (build.disjoined-modus-ponens-2 @- @--))))

;; (deftheorem theorem-iff-when-not-nil-and-not-nil
;;  :derive (v (= x nil) (v (= y nil) (= (iff x y) t)))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                     (build.axiom (definition-of-iff)))
;;           ((v (= x nil) (= (iff x y) (if x (if y t nil) (if y nil t))))       (build.expansion (@formula (= x nil)) @-)                                *1)
;;           ;; ---
;;           ((v (= x nil) (= (if x y z) y))                                     (build.axiom (axiom-if-when-not-nil))                                    *2)
;;           ((v (= x nil) (= (if x (if y t nil) (if y nil t)) (if y t nil)))    (build.instantiation @- (@sigma (y . (if y t nil)) (z . (if y nil t)))))
;;           ((v (= x nil) (= (iff x y) (if y t nil)))                           (build.disjoined-transitivity-of-pequal *1 @-))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) (if x t nil)))             (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil)))         *3)
;;           ;; ---
;;           ((v (= y nil) (= (if y t nil) t))                                   (build.instantiation *2 (@sigma (x . y) (y . t) (z . nil))))
;;           ((v (v (= x nil) (= y nil)) (= (if y t nil) t))                     (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) t))                        (build.disjoined-transitivity-of-pequal *3 @-))
;;           ((v (= x nil) (v (= y nil) (= (iff x y) t)))                        (build.right-associativity @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-when-not-nil-and-nil
;;  :derive (v (= x nil) (v (!= y nil) (= (iff x y) nil)))
;;  :proof (@derive
;;          ((= (iff x y) (if x (if y t nil) (if y nil t)))                     (build.axiom (definition-of-iff)))
;;          ((v (= x nil) (= (iff x y) (if x (if y t nil) (if y nil t))))       (build.expansion (@formula (= x nil)) @-)                                *1)
;;          ;; ---
;;          ((v (= x nil) (= (if x y z) y))                                     (build.axiom (axiom-if-when-not-nil)))
;;          ((v (= x nil) (= (if x (if y t nil) (if y nil t)) (if y t nil)))    (build.instantiation @- (@sigma (y . (if y t nil)) (z . (if y nil t)))))
;;          ((v (= x nil) (= (iff x y) (if y t nil)))                           (build.disjoined-transitivity-of-pequal *1 @-))
;;          ((v (v (= x nil) (!= y nil)) (= (iff x y) (if y t nil)))            (build.multi-assoc-expansion @- (@formulas (= x nil) (!= y nil)))        *2)
;;          ;; ---
;;          ((v (!= x nil) (= (if x y z) z))                                    (build.axiom (axiom-if-when-nil)))
;;          ((v (!= y nil) (= (if y t nil) nil))                                (build.instantiation @- (@sigma (x . y) (y . t) (z . nil))))
;;          ((v (v (= x nil) (!= y nil)) (= (if y t nil) nil))                  (build.multi-assoc-expansion @- (@formulas (= x nil) (!= y nil))))
;;          ((v (v (= x nil) (!= y nil)) (= (iff x y) nil))                     (build.disjoined-transitivity-of-pequal *2 @-))
;;          ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))                     (build.right-associativity @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-when-nil-and-not-nil
;;  :derive (v (!= x nil) (v (= y nil) (= (iff x y) nil)))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                      (build.axiom (definition-of-iff)))
;;           ((v (!= x nil) (= (iff x y) (if x (if y t nil) (if y nil t))))       (build.expansion (@formula (!= x nil)) @-)                               *1)
;;           ;; ---
;;           ((v (!= x nil) (= (if x y z) z))                                     (build.axiom (axiom-if-when-nil)))
;;           ((v (!= x nil) (= (if x (if y t nil) (if y nil t)) (if y nil t)))    (build.instantiation @- (@sigma (y . (if y t nil)) (z . (if y nil t)))))
;;           ((v (!= x nil) (= (iff x y) (if y nil t)))                           (build.disjoined-transitivity-of-pequal *1 @-))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) (if y nil t)))             (build.multi-assoc-expansion @- (@formulas (!= x nil) (= y nil)))        *2)
;;           ;; ---
;;           ((v (= x nil) (= (if x y z) y))                                      (build.axiom (axiom-if-when-not-nil)))
;;           ((v (= y nil) (= (if y nil t) nil))                                  (build.instantiation @- (@sigma (x . y) (y . nil) (z . t))))
;;           ((v (v (!= x nil) (= y nil)) (= (if y nil t) nil))                   (build.multi-assoc-expansion @- (@formulas (!= x nil) (= y nil))))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) nil))                      (build.disjoined-transitivity-of-pequal *2 @-))
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))                      (build.right-associativity @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-when-nil-and-nil
;;  :derive (v (!= x nil) (v (!= y nil) (= (iff x y) t)))
;;  :proof  (@derive
;;           ((= (iff x y) (if x (if y t nil) (if y nil t)))                      (build.axiom (definition-of-iff)))
;;           ((v (!= x nil) (= (iff x y) (if x (if y t nil) (if y nil t))))       (build.expansion (@formula (!= x nil)) @-)                               *1)
;;           ;; ---
;;           ((v (!= x nil) (= (if x y z) z))                                     (build.axiom (axiom-if-when-nil))                                        *2)
;;           ((v (!= x nil) (= (if x (if y t nil) (if y nil t)) (if y nil t)))    (build.instantiation @- (@sigma (y . (if y t nil)) (z . (if y nil t)))))
;;           ((v (!= x nil) (= (iff x y) (if y nil t)))                           (build.disjoined-transitivity-of-pequal *1 @-))
;;           ((v (v (!= x nil) (!= y nil)) (= (iff x y) (if y nil t)))            (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil)))       *3)
;;           ;; ---
;;           ((v (!= y nil) (= (if y nil t) t))                                   (build.instantiation *2 (@sigma (x . y) (y . nil) (z . t))))
;;           ((v (v (!= x nil) (!= y nil)) (= (if y nil t) t))                    (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))))
;;           ((v (v (!= x nil) (!= y nil)) (= (iff x y) t))                       (build.disjoined-transitivity-of-pequal *3 @-))
;;           ((v (!= x nil) (v (!= y nil) (= (iff x y) t)))                       (build.right-associativity @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-of-nil
;;  :derive (= (iff x nil) (equal x nil))
;;  :proof  (@derive
;;           ((v (= x y)   (= (equal x y) nil))             (build.axiom (axiom-equal-when-diff)))
;;           ((v (= x nil) (= (equal x nil) nil))           (build.instantiation @- (@sigma (y . nil))))
;;           ((v (= x nil) (= nil (equal x nil)))           (build.disjoined-commute-pequal @-))
;;           ((v (= x nil) (= (iff x nil) nil))             (build.theorem (theorem-iff-nil-when-not-nil)))
;;           ((v (= x nil) (= (iff x nil) (equal x nil)))   (build.disjoined-transitivity-of-pequal @- @--)  *1)
;;           ;; ---
;;           ((v (!= x y)   (= (equal x y) t))              (build.axiom (axiom-equal-when-same)))
;;           ((v (!= x nil) (= (equal x nil) t))            (build.instantiation @- (@sigma (y . nil))))
;;           ((v (!= x nil) (= t (equal x nil)))            (build.disjoined-commute-pequal @-))
;;           ((v (!= x nil) (= (iff x nil) t))              (build.theorem (theorem-iff-nil-when-nil)))
;;           ((v (!= x nil) (= (iff x nil) (equal x nil)))  (build.disjoined-transitivity-of-pequal @- @--)  *2)
;;           ;; ---
;;           ((v (= (iff x nil) (equal x nil))
;;               (= (iff x nil) (equal x nil)))             (build.cut *1 *2))
;;           ((= (iff x nil) (equal x nil))                 (build.contraction @-)))
;;  :minatbl ((equal . 2)
;;            (iff . 2)))

;; (deftheorem theorem-iff-of-t
;;  :derive (= (iff x t) (if x t nil))
;;  :proof  (@derive
;;           ((v (= x nil) (= (if x y z) y))             (build.axiom (axiom-if-when-not-nil)))
;;           ((v (= x nil) (= (if x t nil) t))           (build.instantiation @- (@sigma (y . t) (z . nil))))
;;           ((v (= x nil) (= t (if x t nil)))           (build.disjoined-commute-pequal @-))
;;           ((v (= x nil) (= (iff x t) t))              (build.theorem (theorem-iff-t-when-not-nil)))
;;           ((v (= x nil) (= (iff x t) (if x t nil)))   (build.disjoined-transitivity-of-pequal @- @--)  *1)
;;           ;; ---
;;           ((v (!= x nil) (= (if x y z) z))            (build.axiom (axiom-if-when-nil)))
;;           ((v (!= x nil) (= (if x t nil) nil))        (build.instantiation @- (@sigma (y . t) (z . nil))))
;;           ((v (!= x nil) (= nil (if x t nil)))        (build.disjoined-commute-pequal @-))
;;           ((v (!= x nil) (= (iff x t) nil))           (build.theorem (theorem-iff-t-when-nil)))
;;           ((v (!= x nil) (= (iff x t) (if x t nil)))  (build.disjoined-transitivity-of-pequal @- @--)  *2)
;;           ;; ---
;;           ((v (= (iff x t) (if x t nil))
;;               (= (iff x t) (if x t nil)))             (build.cut *1 *2))
;;           ((= (iff x t) (if x t nil))                 (build.contraction @-)))
;;  :minatbl ((if . 3)
;;            (iff . 2)))

;; (deftheorem theorem-iff-normalize-t
;;  :derive (v (= y nil) (= (iff x y) (if x t nil)))
;;  :proof  (@derive
;;           ((v (= x nil) (v (= y nil) (= (iff x y) t)))              (build.theorem (theorem-iff-when-not-nil-and-not-nil)))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) t))              (build.associativity @-)                                            *1a)
;;           ((v (= x nil) (= (iff x t) t))                            (build.theorem (theorem-iff-t-when-not-nil)))
;;           ((v (v (= x nil) (= y nil)) (= (iff x t) t))              (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))))
;;           ((v (v (= x nil) (= y nil)) (= t (iff x t)))              (build.disjoined-commute-pequal @-))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) (iff x t)))      (build.disjoined-transitivity-of-pequal *1a @-)                *1b)
;;           ((= (iff x t) (if x t nil))                               (build.theorem (theorem-iff-of-t)))
;;           ((v (v (= x nil) (= y nil)) (= (iff x t) (if x t nil)))   (build.expansion (@formula (v (= x nil) (= y nil))) @-))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) (if x t nil)))   (build.disjoined-transitivity-of-pequal *1b @-))
;;           ((v (= x nil) (v (= y nil) (= (iff x y) (if x t nil))))   (build.right-associativity @-)                                 *1)
;;           ;; ---
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))           (build.theorem (theorem-iff-when-nil-and-not-nil)))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) nil))           (build.associativity @-)                                            *2a)
;;           ((v (!= x nil) (= (iff x t) nil))                         (build.theorem (theorem-iff-t-when-nil)))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x t) nil))           (build.multi-assoc-expansion @- (@formulas (!= x nil) (= y nil))))
;;           ((v (v (!= x nil) (= y nil)) (= nil (iff x t)))           (build.disjoined-commute-pequal @-))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) (iff x t)))     (build.disjoined-transitivity-of-pequal *2a @-)                *2b)
;;           ((= (iff x t) (if x t nil))                               (build.theorem (theorem-iff-of-t)))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x t) (if x t nil)))  (build.expansion (@formula (v (!= x nil) (= y nil))) @-))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) (if x t nil)))  (build.disjoined-transitivity-of-pequal *2b @-))
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) (if x t nil))))  (build.right-associativity @-)                                 *2)
;;           ;; ---
;;           ((v (v (= y nil) (= (iff x y) (if x t nil)))
;;               (v (= y nil) (= (iff x y) (if x t nil))))             (build.cut *1 *2))
;;           ((v (= y nil) (= (iff x y) (if x t nil)))                 (build.contraction @-)))
;;  :minatbl ((iff . 2)
;;            (if . 3)))

;; (deftheorem theorem-iff-normalize-nil
;;  :derive (v (!= y nil) (= (iff x y) (equal x nil)))
;;  :proof (@derive
;;          ((= x x)                                        (build.reflexivity 'x))
;;          ((v (!= y nil) (= x x))                         (build.expansion (@formula (!= y nil)) @-))
;;          ((v (!= y nil) (= y nil))                       (build.propositional-schema (@formula (= y nil))))
;;          ((v (!= y nil) (= (iff x y) (iff x nil)))       (build.disjoined-pequal-by-args 'iff (@formula (!= y nil)) (list @-- @-)) *1)
;;          ((= (iff x nil) (equal x nil))                  (build.theorem (theorem-iff-of-nil)))
;;          ((v (!= y nil) (= (iff x nil) (equal x nil)))   (build.expansion (@formula (!= y nil)) @-))
;;          ((v (!= y nil) (= (iff x y) (equal x nil)))     (build.disjoined-transitivity-of-pequal *1 @-)))
;;  :minatbl ((iff . 2)
;;            (equal . 2)))

;; (deftheorem theorem-reflexivity-of-iff
;;   :derive (= (iff x x) t)
;;   :proof  (@derive
;;            ((v (= x nil) (= (if x y z) y))                                     (build.axiom (axiom-if-when-not-nil)))
;;            ((v (= x nil) (= (if x (if x t nil) (if x nil t)) (if x t nil)))    (build.instantiation @- (@sigma (y . (if x t nil)) (z . (if x nil t)))))
;;            ((v (= x nil) (= (if x t nil) t))                                   (build.instantiation @-- (@sigma (y . t) (z . nil))))
;;            ((v (= x nil) (= (if x (if x t nil) (if x nil t)) t))               (build.disjoined-transitivity-of-pequal @-- @-)                           *1)
;;            ;; ---
;;            ((v (!= x nil) (= (if x y z) z))                                    (build.axiom (axiom-if-when-nil)))
;;            ((v (!= x nil) (= (if x (if x t nil) (if x nil t)) (if x nil t)))   (build.instantiation @- (@sigma (y . (if x t nil)) (z . (if x nil t)))))
;;            ((v (!= x nil) (= (if x nil t) t))                                  (build.instantiation @-- (@sigma (y . nil) (z . t))))
;;            ((v (!= x nil) (= (if x (if x t nil) (if x nil t)) t))              (build.disjoined-transitivity-of-pequal @-- @-)                           *2)
;;            ;; ---
;;            ((= (iff x y) (if x (if y t nil) (if y nil t)))                     (build.axiom (definition-of-iff)))
;;            ((= (iff x x) (if x (if x t nil) (if x nil t)))                     (build.instantiation @- (@sigma (y . x)))                                 *3)
;;            ((v (= (if x (if x t nil) (if x nil t)) t)
;;                (= (if x (if x t nil) (if x nil t)) t))                         (build.cut *1 *2))
;;            ((= (if x (if x t nil) (if x nil t)) t)                             (build.contraction @-))
;;            ((= (iff x x) t)                                                    (build.transitivity-of-pequal *3 @-)))
;;   :minatbl ((if . 3)
;;             (iff . 2)))

;; (defderiv build.iff-reflexivity
;;   :derive (= (iff (? a) (? a)) t)
;;   :from   ((term a (? a)))
;;   :proof  (@derive ((= (iff x x) t)          (build.theorem (theorem-reflexivity-of-iff)))
;;                    ((= (iff (? a) (? a)) t)  (build.instantiation @- (@sigma (x . (? a))))))
;;   :minatbl ((iff . 2)))



;; BOZO This is never used anywhere.  Get rid of it.
;; (defund build.iff-reflexivity-list (x)
;;   (declare (xargs :guard (logic.term-listp x)))
;;   (if (consp x)
;;       (cons (build.iff-reflexivity (car x))
;;             (build.iff-reflexivity-list (cdr x)))
;;     nil))

;; (defobligations build.iff-reflexivity-list
;;   (build.iff-reflexivity))

;; (encapsulate
;;  ()
;;  (local (in-theory (enable build.iff-reflexivity-list)))

;;  (defthm len-of-build.iff-reflexivity-list
;;    (equal (len (build.iff-reflexivity-list x))
;;           (len x)))

;;  (defthm forcing-logic.appeal-listp-of-build.iff-reflexivity-list
;;    (implies (force (logic.term-listp x))
;;             (equal (logic.appeal-listp (build.iff-reflexivity-list x))
;;                    t)))

;;  (defthm forcing-logic.strip-conclusions-of-build.iff-reflexivity-list
;;    (implies (force (logic.term-listp x))
;;             (equal (logic.strip-conclusions (build.iff-reflexivity-list x))
;;                    (logic.pequal-list (logic.function-list 'iff (list2-list x x))
;;                                       (repeat ''t (len x)))))
;;    :rule-classes ((:rewrite :backchain-limit-lst 0)))

;;  (defthm@ forcing-logic.proof-listp-of-build.iff-reflexivity-list
;;    (implies (force (and (logic.term-listp x)
;;                         ;; ---
;;                         (logic.term-list-atblp x atbl)
;;                         (equal (cdr (lookup 'iff atbl)) 2)
;;                         (@obligations build.iff-reflexivity-list)))
;;             (equal (logic.proof-listp (build.iff-reflexivity-list x) axioms thms atbl)
;;                    t))))






;; (defderiv build.not-equal-from-not-iff
;;   :derive (!= (equal (? a) (? b)) t)
;;   :from   ((proof x (!= (iff (? a) (? b)) t)))
;;   :proof  (@derive ((v (!= (equal x y) t) (= (iff x y) t))                      (build.theorem (theorem-iff-from-equal)))
;;                    ((v (= (iff x y) t) (!= (equal x y) t))                      (build.commute-or @-))
;;                    ((v (= (iff (? a) (? b)) t) (!= (equal (? a) (? b)) t))      (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
;;                    ((!= (iff (? a) (? b)) t)                                    (@given x))
;;                    ((!= (equal (? a) (? b)) t)                                  (build.modus-ponens-2 @- @--)))
;;   :minatbl ((equal . 2)))

;; (defderiv build.disjoined-not-equal-from-not-iff
;;  :derive (v P (!= (equal (? a) (? b)) t))
;;  :from   ((proof x (v P (!= (iff (? a) (? b)) t))))
;;  :proof  (@derive
;;           ((v (!= (equal x y) t) (= (iff x y) t))                               (build.theorem (theorem-iff-from-equal)))
;;           ((v (= (iff x y) t) (!= (equal x y) t))                               (build.commute-or @-))
;;           ((v (= (iff (? a) (? b)) t) (!= (equal (? a) (? b)) t))               (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
;;           ((v P (v (= (iff (? a) (? b)) t) (!= (equal (? a) (? b)) t)))         (build.expansion (@formula P) @-))
;;           ((v P (!= (iff (? a) (? b)) t))                                       (@given x))
;;           ((v P (!= (equal (? a) (? b)) t))                                     (build.disjoined-modus-ponens-2 @- @--)))
;;  :minatbl ((iff . 2)
;;            (equal . 2)))

;; (deftheorem theorem-iff-with-nil-or-t
;;   :derive (v (= (iff x nil) t) (= (iff x t) t))
;;   :proof  (@derive ((v (= x nil) (= (iff x t) t))                               (build.theorem (theorem-iff-t-when-not-nil)))
;;                    ((v (!= x nil) (= (iff x nil) t))                            (build.theorem (theorem-iff-nil-when-nil)))
;;                    ((v (= (iff x t) t) (= (iff x nil) t))                       (build.cut @-- @-))
;;                    ((v (= (iff x nil) t) (= (iff x t) t))                       (build.commute-or @-)))
;;   :minatbl ((iff . 2)))

;; (deftheorem theorem-iff-nil-or-t
;;   :derive (v (= (iff x y) nil)
;;              (= (iff x y) t))
;;   :proof (@derive
;;           ((v (= x nil) (v (= y nil) (= (iff x y) t)))                          (build.theorem (theorem-iff-when-not-nil-and-not-nil)))
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))                       (build.theorem (theorem-iff-when-nil-and-not-nil)))
;;           ((v (v (= y nil) (= (iff x y) t)) (v (= y nil) (= (iff x y) nil)))    (build.cut @-- @-))
;;           ((v (= y nil) (v (= (iff x y) t) (v (= y nil) (= (iff x y) nil))))    (build.right-associativity @-))
;;           ((v (= y nil) (v (v (= y nil) (= (iff x y) nil)) (= (iff x y) t)))    (build.disjoined-commute-or @-))
;;           ((v (= y nil) (v (= y nil) (v (= (iff x y) nil) (= (iff x y) t))))    (build.disjoined-right-associativity @-))
;;           ((v (v (= y nil) (= y nil)) (v (= (iff x y) nil) (= (iff x y) t)))    (build.associativity @-))
;;           ((v (v (= (iff x y) nil) (= (iff x y) t)) (v (= y nil) (= y nil)))    (build.commute-or @-))
;;           ((v (v (= (iff x y) nil) (= (iff x y) t)) (= y nil))                  (build.disjoined-contraction @-))
;;           ((v (= y nil) (v (= (iff x y) nil) (= (iff x y) t)))                  (build.commute-or @-)                              *1)
;;           ;; ---
;;           ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))                       (build.theorem (theorem-iff-when-not-nil-and-nil)))
;;           ((v (!= x nil) (v (!= y nil) (= (iff x y) t)))                        (build.theorem (theorem-iff-when-nil-and-nil)))
;;           ((v (v (!= y nil) (= (iff x y) nil)) (v (!= y nil) (= (iff x y) t)))  (build.cut @-- @-))
;;           ((v (!= y nil) (v (= (iff x y) nil) (v (!= y nil) (= (iff x y) t))))  (build.right-associativity @-))
;;           ((v (!= y nil) (v (v (!= y nil) (= (iff x y) t)) (= (iff x y) nil)))  (build.disjoined-commute-or @-))
;;           ((v (!= y nil) (v (!= y nil) (v (= (iff x y) t) (= (iff x y) nil))))  (build.disjoined-right-associativity @-))
;;           ((v (v (!= y nil) (!= y nil)) (v (= (iff x y) t) (= (iff x y) nil)))  (build.associativity @-))
;;           ((v (v (= (iff x y) t) (= (iff x y) nil)) (v (!= y nil) (!= y nil)))  (build.commute-or @-))
;;           ((v (v (= (iff x y) t) (= (iff x y) nil)) (!= y nil))                 (build.disjoined-contraction @-))
;;           ((v (!= y nil) (v (= (iff x y) t) (= (iff x y) nil)))                 (build.commute-or @-))
;;           ((v (!= y nil) (v (= (iff x y) nil) (= (iff x y) t)))                 (build.disjoined-commute-or @-)                   *2)
;;           ;; ---
;;           ((v (v (= (iff x y) nil) (= (iff x y) t))
;;               (v (= (iff x y) nil) (= (iff x y) t)))                            (build.cut *1 *2))
;;           ((v (= (iff x y) nil) (= (iff x y) t))                                (build.contraction @-)))
;;   :minatbl ((iff . 2)))


;; (defderiv build.iff-nil-from-not-t
;;  :derive (= (iff (? a) (? b)) nil)
;;  :from   ((proof x (!= (iff (? a) (? b)) t)))
;;  :proof  (@derive ((v (= (iff x y) nil) (= (iff x y) t))                        (build.theorem (theorem-iff-nil-or-t)))
;;                   ((v (= (iff x y) t) (= (iff x y) nil))                        (build.commute-or @-))
;;                   ((v (= (iff (? a) (? b)) t) (= (iff (? a) (? b)) nil))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
;;                   ((!= (iff (? a) (? b)) t)                                     (@given x))
;;                   ((= (iff (? a) (? b)) nil)                                    (build.modus-ponens-2 @- @--))))

;; (defderiv build.disjoined-iff-nil-from-not-t
;;  :derive (v P (= (iff (? a) (? b)) nil))
;;  :from   ((proof x (v P (!= (iff (? a) (? b)) t))))
;;  :proof  (@derive
;;           ((v (= (iff x y) nil) (= (iff x y) t))                                (build.theorem (theorem-iff-nil-or-t)))
;;           ((v (= (iff x y) t) (= (iff x y) nil))                                (build.commute-or @-))
;;           ((v (= (iff (? a) (? b)) t) (= (iff (? a) (? b)) nil))                (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
;;           ((v P (v (= (iff (? a) (? b)) t) (= (iff (? a) (? b)) nil)))          (build.expansion (@formula P) @-))
;;           ((v P (!= (iff (? a) (? b)) t))                                       (@given x))
;;           ((v P (= (iff (? a) (? b)) nil))                                      (build.disjoined-modus-ponens-2 @- @--))))

;; (deftheorem theorem-symmetry-of-iff
;;   :derive (= (iff x y) (iff y x))
;;   :proof (@derive
;;           ((v (= x nil) (v (= y nil) (= (iff x y) t)))                          (build.theorem (theorem-iff-when-not-nil-and-not-nil)))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) t))                          (build.associativity @-)                                    *1a)
;;           ((v (v (= y nil) (= x nil)) (= (iff y x) t))                          (build.instantiation @- (@sigma (x . y) (y . x))))
;;           ((v (= (iff y x) t) (v (= y nil) (= x nil)))                          (build.commute-or @-))
;;           ((v (= (iff y x) t) (v (= x nil) (= y nil)))                          (build.disjoined-commute-or @-))
;;           ((v (v (= x nil) (= y nil)) (= (iff y x) t))                          (build.commute-or @-))
;;           ((v (v (= x nil) (= y nil)) (= t (iff y x)))                          (build.disjoined-commute-pequal @-))
;;           ((v (v (= x nil) (= y nil)) (= (iff x y) (iff y x)))                  (build.disjoined-transitivity-of-pequal *1a @-))
;;           ((v (= x nil) (v (= y nil) (= (iff x y) (iff y x))))                  (build.right-associativity @-)                              *1)
;;           ;; ---
;;           ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))                       (build.theorem (theorem-iff-when-not-nil-and-nil)))
;;           ((v (v (= x nil) (!= y nil)) (= (iff x y) nil))                       (build.associativity @-)                                    *2a)
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))                       (build.theorem (theorem-iff-when-nil-and-not-nil)))
;;           ((v (!= y nil) (v (= x nil) (= (iff y x) nil)))                       (build.instantiation @- (@sigma (x . y) (y . x))))
;;           ((v (v (!= y nil) (= x nil)) (= (iff y x) nil))                       (build.associativity @-))
;;           ((v (= (iff y x) nil) (v (!= y nil) (= x nil)))                       (build.commute-or @-))
;;           ((v (= (iff y x) nil) (v (= x nil) (!= y nil)))                       (build.disjoined-commute-or @-))
;;           ((v (v (= x nil) (!= y nil)) (= (iff y x) nil))                       (build.commute-or @-))
;;           ((v (v (= x nil) (!= y nil)) (= nil (iff y x)))                       (build.disjoined-commute-pequal @-))
;;           ((v (v (= x nil) (!= y nil)) (= (iff x y) (iff y x)))                 (build.disjoined-transitivity-of-pequal *2a @-))
;;           ((v (= x nil) (v (!= y nil) (= (iff x y) (iff y x))))                 (build.right-associativity @-)                              *2)
;;           ;; ---
;;           ((v (= y nil) (v (!= x nil) (= (iff y x) (iff x y))))                 (build.instantiation @- (@sigma (x . y) (y . x))))
;;           ((v (v (= y nil) (!= x nil)) (= (iff y x) (iff x y)))                 (build.associativity @-))
;;           ((v (v (= y nil) (!= x nil)) (= (iff x y) (iff y x)))                 (build.disjoined-commute-pequal @-))
;;           ((v (= (iff x y) (iff y x)) (v (= y nil) (!= x nil)))                 (build.commute-or @-))
;;           ((v (= (iff x y) (iff y x)) (v (!= x nil) (= y nil)))                 (build.disjoined-commute-or @-))
;;           ((v (v (!= x nil) (= y nil)) (= (iff x y) (iff y x)))                 (build.commute-or @-))
;;           ((v (!= x nil) (v (= y nil) (= (iff x y) (iff y x))))                 (build.right-associativity @-)                              *3)
;;           ;; ---
;;           ((v (!= x nil) (v (!= y nil) (= (iff x y) t)))                        (build.theorem (theorem-iff-when-nil-and-nil)))
;;           ((v (v (!= x nil) (!= y nil)) (= (iff x y) t))                        (build.associativity @-)                                    *4a)
;;           ((v (v (!= y nil) (!= x nil)) (= (iff y x) t))                        (build.instantiation @- (@sigma (x . y) (y . x))))
;;           ((v (= (iff y x) t) (v (!= y nil) (!= x nil)))                        (build.commute-or @-))
;;           ((v (= (iff y x) t) (v (!= x nil) (!= y nil)))                        (build.disjoined-commute-or @-))
;;           ((v (v (!= x nil) (!= y nil)) (= (iff y x) t))                        (build.commute-or @-))
;;           ((v (v (!= x nil) (!= y nil)) (= t (iff y x)))                        (build.disjoined-commute-pequal @-))
;;           ((v (v (!= x nil) (!= y nil)) (= (iff x y) (iff y x)))                (build.disjoined-transitivity-of-pequal *4a @-))
;;           ((v (!= x nil) (v (!= y nil) (= (iff x y) (iff y x))))                (build.right-associativity @-)                              *4)
;;           ;; ---
;;           ((v (v (= y nil) (= (iff x y) (iff y x)))
;;               (v (= y nil) (= (iff x y) (iff y x))))                            (build.cut *1 *3))
;;           ((v (= y nil) (= (iff x y) (iff y x)))                                (build.contraction @-)                                      *5a)
;;           ((v (v (!= y nil) (= (iff x y) (iff y x)))
;;               (v (!= y nil) (= (iff x y) (iff y x))))                           (build.cut *2 *4))
;;           ((v (!= y nil) (= (iff x y) (iff y x)))                               (build.contraction @-))
;;           ((v (= (iff x y) (iff y x)) (= (iff x y) (iff y x)))                  (build.cut *5a @-))
;;           ((= (iff x y) (iff y x))                                              (build.contraction @-)))
;;   :minatbl ((iff . 2)))


;; (deftheorem theorem-transitivity-two-of-iff
;;   :derive (v (= (iff x y) nil)
;;              (= (iff x z) (iff y z)))
;;   :proof  (@derive
;;            ((= (iff x y) (iff y x))                                        (build.theorem (theorem-symmetry-of-iff)))
;;            ((= (iff y x) (iff x y))                                        (build.instantiation @- (@sigma (x . y) (y . x)))                         *1a)
;;            ((v (= y nil) (= (iff y x) (iff x y)))                          (build.expansion (@formula (= y nil)) @-))
;;            ((v (= y nil) (= (iff x y) (if x t nil)))                       (build.theorem (theorem-iff-normalize-t)))
;;            ((v (= y nil) (= (iff y x) (if x t nil)))                       (build.disjoined-transitivity-of-pequal @-- @-))
;;            ((v (= x nil) (= (iff x y) (if y t nil)))                       (build.instantiation @- (@sigma (x . y) (y . x)))                         *1)
;;            ;; ---
;;            ((v (= x nil) (= (iff x z) (if z t nil)))                       (build.instantiation *1 (list (cons 'y 'z))))
;;            ((v (v (= x nil) (= y nil)) (= (iff x z) (if z t nil)))         (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil)))          *3a)
;;            ((v (= y nil) (= (iff y z) (if z t nil)))                       (build.instantiation *1 (list (cons 'x 'y) (cons 'y 'z))))
;;            ((v (v (= x nil) (= y nil)) (= (iff y z) (if z t nil)))         (build.multi-assoc-expansion @- (@formulas (= x nil) (= y nil))))
;;            ((v (v (= x nil) (= y nil)) (= (if z t nil) (iff y z)))         (build.disjoined-commute-pequal @-))
;;            ((v (v (= x nil) (= y nil)) (= (iff x z) (iff y z)))            (build.disjoined-transitivity-of-pequal *3a @-))
;;            ((v (= x nil) (v (= y nil) (= (iff x z) (iff y z))))            (build.right-associativity @-))
;;            ((v (!= x nil) (v (= y nil) (= (iff x y) nil)))                 (build.theorem (theorem-iff-when-nil-and-not-nil)))
;;            ((v (v (= y nil) (= (iff x z) (iff y z)))
;;                (v (= y nil) (= (iff x y) nil)))                            (build.cut @-- @-))
;;            ((v (= y nil) (v (= (iff x z) (iff y z))
;;                             (v (= y nil) (= (iff x y) nil))))              (build.right-associativity @-))
;;            ((v (= y nil) (v (v (= y nil) (= (iff x y) nil))
;;                             (= (iff x z) (iff y z))))                      (build.disjoined-commute-or @-))
;;            ((v (= y nil) (v (= y nil) (v (= (iff x y) nil)
;;                                          (= (iff x z) (iff y z)))))        (build.disjoined-right-associativity @-))
;;            ((v (v (= y nil) (= y nil))
;;                (v (= (iff x y) nil) (= (iff x z) (iff y z))))              (build.associativity @-))
;;            ((v (v (= (iff x y) nil) (= (iff x z) (iff y z)))
;;                (v (= y nil) (= y nil)))                                    (build.commute-or @-))
;;            ((v (v (= (iff x y) nil) (= (iff x z) (iff y z))) (= y nil))    (build.disjoined-contraction @-))
;;            ((v (= y nil) (v (= (iff x y) nil) (= (iff x z) (iff y z))))    (build.commute-or @-)                                                     *5)
;;            ;; ---
;;            ((v (!= y nil) (= (iff y x) (iff x y)))                         (build.expansion (@formula (!= y nil)) *1a))
;;            ((v (!= y nil) (= (iff x y) (equal x nil)))                     (build.theorem (theorem-iff-normalize-nil)))
;;            ((v (!= y nil) (= (iff y x) (equal x nil)))                     (build.disjoined-transitivity-of-pequal @-- @-))
;;            ((v (!= x nil) (= (iff x y) (equal y nil)))                     (build.instantiation @- (@sigma (x . y) (y . x)))                         *2)
;;            ;; ---
;;            ((v (!= x nil) (= (iff x z) (equal z nil)))                     (build.instantiation *2 (@sigma (y . z))))
;;            ((v (v (!= x nil) (!= y nil)) (= (iff x z) (equal z nil)))      (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil)))        *4a)
;;            ((v (!= y nil) (= (iff y z) (equal z nil)))                     (build.instantiation *2 (@sigma (x . y) (y . z))))
;;            ((v (v (!= x nil) (!= y nil)) (= (iff y z) (equal z nil)))      (build.multi-assoc-expansion @- (@formulas (!= x nil) (!= y nil))))
;;            ((v (v (!= x nil) (!= y nil)) (= (equal z nil) (iff y z)))      (build.disjoined-commute-pequal @-))
;;            ((v (v (!= x nil) (!= y nil)) (= (iff x z) (iff y z)))          (build.disjoined-transitivity-of-pequal *4a @-))
;;            ((v (!= x nil) (v (!= y nil) (= (iff x z) (iff y z))))          (build.right-associativity @-))
;;            ((v (= x nil) (v (!= y nil) (= (iff x y) nil)))                 (build.theorem (theorem-iff-when-not-nil-and-nil)))
;;            ((v (v (!= y nil) (= (iff x y) nil))
;;                (v (!= y nil) (= (iff x z) (iff y z))))                     (build.cut @- @--))
;;            ((v (!= y nil) (v (= (iff x y) nil)
;;                              (v (!= y nil) (= (iff x z) (iff y z)))))      (build.right-associativity @-))
;;            ((v (!= y nil) (v (v (!= y nil) (= (iff x z) (iff y z)))
;;                              (= (iff x y) nil)))                           (build.disjoined-commute-or @-))
;;            ((v (!= y nil) (v (!= y nil) (v (= (iff x z) (iff y z))
;;                                            (= (iff x y) nil))))            (build.disjoined-right-associativity @-))
;;            ((v (v (!= y nil) (!= y nil))
;;                (v (= (iff x z) (iff y z)) (= (iff x y) nil)))              (build.associativity @-))
;;            ((v (v (= (iff x z) (iff y z)) (= (iff x y) nil))
;;                (v (!= y nil) (!= y nil)))                                  (build.commute-or @-))
;;            ((v (v (= (iff x z) (iff y z)) (= (iff x y) nil))
;;                (!= y nil))                                                 (build.disjoined-contraction @-))
;;            ((v (!= y nil) (v (= (iff x z) (iff y z)) (= (iff x y) nil)))   (build.commute-or @-))
;;            ((v (!= y nil) (v (= (iff x y) nil) (= (iff x z) (iff y z))))   (build.disjoined-commute-or @-))
;;            ;; ---
;;            ((v (v (= (iff x y) nil) (= (iff x z) (iff y z)))
;;                (v (= (iff x y) nil) (= (iff x z) (iff y z))))              (build.cut *5 @-))
;;            ((v (= (iff x y) nil) (= (iff x z) (iff y z)))                  (build.contraction @-)))
;;            :minatbl ((iff . 2)
;;                      (equal . 2)
;;                      (if . 3)))

;; (deftheorem theorem-transitivity-of-iff
;;  :derive (v (= (iff x y) nil) (v (= (iff y z) nil) (= (iff x z) t)))
;;  :proof  (@derive
;;           ((v (= (iff x y) nil) (= (iff x z) (iff y z)))                          (build.theorem (theorem-transitivity-two-of-iff)))
;;           ((v (v (= (iff x y) nil) (= (iff y z) nil)) (= (iff x z) (iff y z)))    (build.multi-assoc-expansion @- (@formulas (= (iff x y) nil) (= (iff y z) nil)))   *1)
;;           ((v (= (iff x y) nil) (= (iff x y) t))                                  (build.theorem (theorem-iff-nil-or-t)))
;;           ((v (= (iff y z) nil) (= (iff y z) t))                                  (build.instantiation @- (list (cons 'x 'y) (cons 'y 'z))))
;;           ((v (v (= (iff x y) nil) (= (iff y z) nil)) (= (iff y z) t))            (build.multi-assoc-expansion @- (@formulas (= (iff x y) nil) (= (iff y z) nil))))
;;           ((v (v (= (iff x y) nil) (= (iff y z) nil)) (= (iff x z) t))            (build.disjoined-transitivity-of-pequal *1 @-))
;;           ((v (= (iff x y) nil) (v (= (iff y z) nil) (= (iff x z) t)))            (build.right-associativity @-)))
;;  :minatbl ((iff . 2)))

;; (defderiv build.transitivity-of-iff
;;  :derive (= (iff (? a) (? c)) t)
;;  :from   ((proof x (= (iff (? a) (? b)) t))
;;           (proof y (= (iff (? b) (? c)) t)))
;;  :proof  (@derive
;;           ((v (= (iff x y) nil) (v (= (iff y z) nil) (= (iff x z) t)))                          (build.theorem (theorem-transitivity-of-iff)))
;;           ((v (= (iff (? a) (? b)) nil) (v (= (iff (? b) (? c)) nil) (= (iff (? a) (? c)) t)))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c))))   *1)
;;           ((= (iff (? a) (? b)) t)                                                              (@given x))
;;           ;; BOZO we can avoid this if we change the theorem.
;;           ((!= (iff (? a) (? b)) nil)                                                           (build.not-nil-from-t @-))
;;           ((v (= (iff (? b) (? c)) nil) (= (iff (? a) (? c)) t))                                (build.modus-ponens-2 @- *1) *2)
;;           ((= (iff (? b) (? c)) t)                                                              (@given y))
;;           ;; BOZO we can avoid this if we change the theorem.
;;           ((!= (iff (? b) (? c)) nil)                                                           (build.not-nil-from-t @-))
;;           ((= (iff (? a) (? c)) t)                                                              (build.modus-ponens-2 @- *2))))

;; (defderiv build.disjoined-transitivity-of-iff
;;  :derive (v P (= (iff (? a) (? c)) t))
;;  :from   ((proof x (v P (= (iff (? a) (? b)) t)))
;;           (proof y (v P (= (iff (? b) (? c)) t))))
;;  :proof  (@derive
;;           ((v (= (iff x y) nil) (v (= (iff y z) nil) (= (iff x z) t)))                                (build.theorem (theorem-transitivity-of-iff)))
;;           ((v (= (iff (? a) (? b)) nil) (v (= (iff (? b) (? c)) nil) (= (iff (? a) (? c)) t)))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
;;           ((v P (v (= (iff (? a) (? b)) nil) (v (= (iff (? b) (? c)) nil) (= (iff (? a) (? c)) t))))  (build.expansion (@formula P) @-)                         *1)
;;           ((v P (= (iff (? a) (? b)) t))                                                              (@given x))
;;           ;; BOZO we can remove this if we change the theorem.
;;           ((v P (!= (iff (? a) (? b)) nil))                                                           (build.disjoined-not-nil-from-t @-))
;;           ((v P (v (= (iff (? b) (? c)) nil) (= (iff (? a) (? c)) t)))                                (build.disjoined-modus-ponens-2 @- *1) *2)
;;           ((v P (= (iff (? b) (? c)) t))                                                              (@given y))
;;           ;; BOZO we can remove this if we change the theorem.
;;           ((v P (!= (iff (? b) (? c)) nil))                                                           (build.disjoined-not-nil-from-t @-))
;;           ((v P (= (iff (? a) (? c)) t))                                                              (build.disjoined-modus-ponens-2 @- *2))))


