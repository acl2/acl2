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
(include-book "prop")
(include-book "aux-split")
(include-book "basic-bldrs")
(include-book "../build/iff")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (clause.aux-split-bldr todo done proofs)
;;
;; Proofs should established every clause resulting from the split.  We build
;; a proof whose conclusion depends on whether todo and done are empty:
;;
;;       Todo        Done        Goal
;;   ---------------------------------------------------------------
;;       nonempty    nonempty    (t1 v ... v tn) v (d1 v ... v dm)
;;       nonempty    empty       (t1 v ... v tn)
;;       empty       nonempty    (d1 v ... v dm)
;;       empty       empty       [error]
;;
;; To manage these cases, we split the proof into many auxilliary lemmas, which
;; we will introduce first.



;; Builders for the (not (not x)) case.

(defderiv clause.aux-split-double-negate-lemma1-bldr
  :derive (v (v (!= (? a) nil) P) Q)
  :from   ((proof x (v (v (!= (? b) nil) P) Q))
           (proof y (= (iff (? a) (? b)) t)))
  :proof  (@derive
           ((v (v (!= (? b) nil) P) Q)            (@given x))
           ((v (!= (? b) nil) (v P Q))            (build.right-associativity @-))
           ((v (v P Q) (!= (? b) nil))            (build.commute-or @-)   *1)
           ((= (iff (? a) (? b)) t)               (@given y))
           ((v (v P Q) (= (iff (? a) (? b)) t))   (build.expansion (@formula (v P Q)) @-))
           ((v (v P Q) (!= (? a) nil))            (clause.disjoined-substitute-iff-into-literal-bldr *1 @-))
           ((v (!= (? a) nil) (v P Q))            (build.commute-or @-))
           ((v (v (!= (? a) nil) P) Q)            (build.associativity @-))))

(defderiv clause.aux-split-double-negate-lemma2-bldr
  :derive (v (!= (? a) nil) P)
  :from   ((proof x (v (!= (? b) nil) P))
           (proof y (= (iff (? a) (? b)) t)))
  :proof  (@derive
           ((v (!= (? b) nil) P)                 (@given x))
           ((v P (!= (? b) nil))                 (build.commute-or @-)   *1)
           ((= (iff (? a) (? b)) t)              (@given y))
           ((v P (= (iff (? a) (? b)) t))        (build.expansion (@formula P) @-))
           ((v P (!= (? a) nil))                 (clause.disjoined-substitute-iff-into-literal-bldr *1 @-))
           ((v (!= (? a) nil) P)                 (build.commute-or @-))))




;; Builders for the positive (if a b c) case.

(deftheorem clause.theorem-aux-split-positive
  :derive (v (! (v (!= (not x) nil) (!= y nil)))
             (v (! (v (!= x nil) (!= z nil)))
                (!= (if x y z) nil)))
  :proof  (let ((p (@formula (v (!= (not x) nil) (!= y nil))))
                (q (@formula (v (!= x nil) (!= z nil)))))
            (@derive
             ((v (= x nil) (= (if x y z) y))                (build.axiom (axiom-if-when-not-nil)))
             ((v (! P) (v (= x nil) (= (if x y z) y)))      (build.expansion (logic.pnot p) @-))
             ((v (v (! P) (= x nil)) (= (if x y z) y))      (build.associativity @-)                             *1a)
             ((v (! P) (v (!= (not x) nil) (!= y nil)))     (build.propositional-schema p))
             ((v (! P) (v (!= y nil) (!= (not x) nil)))     (build.disjoined-commute-or @-))
             ((v (v (! P) (!= y nil)) (!= (not x) nil))     (build.associativity @-))
             ((v (v (! P) (!= y nil)) (= x nil))            (build.disjoined-pequal-nil-from-negative-lit @-))
             ((v (! P) (v (!= y nil) (= x nil)))            (build.right-associativity @-))
             ((v (! P) (v (= x nil) (!= y nil)))            (build.disjoined-commute-or @-))
             ((v (v (! P) (= x nil)) (!= y nil))            (build.associativity @-))
             ((v (v (! P) (= x nil)) (!= (if x y z) nil))   (build.disjoined-substitute-into-not-pequal @- *1a))
             ((v (!= (if x y z) nil) (v (! P) (= x nil)))   (build.commute-or @-))
             ((v (!= (if x y z) nil) (v (= x nil) (! P)))   (build.disjoined-commute-or @-))
             ((v (v (= x nil) (! P)) (!= (if x y z) nil))   (build.commute-or @-))
             ((v (= x nil) (v (! P) (!= (if x y z) nil)))   (build.right-associativity @-)                       *1)
             ;; ---
             ((v (!= x nil) (= (if x y z) z))               (build.axiom (axiom-if-when-nil)))
             ((v (! Q) (v (!= x nil) (= (if x y z) z)))     (build.expansion (logic.pnot q) @-))
             ((v (v (! Q) (!= x nil)) (= (if x y z) z))     (build.associativity @-)                             *2a)
             ((v (! Q) (v (!= x nil) (!= z nil)))           (build.propositional-schema q))
             ((v (v (! Q) (!= x nil)) (!= z nil))           (build.associativity @-))
             ((v (v (! Q) (!= x nil)) (!= (if x y z) nil))  (build.disjoined-substitute-into-not-pequal @- *2a))
             ((v (!= (if x y z) nil) (v (! Q) (!= x nil)))  (build.commute-or @-))
             ((v (!= (if x y z) nil) (v (!= x nil) (! Q)))  (build.disjoined-commute-or @-))
             ((v (v (!= x nil) (! Q)) (!= (if x y z) nil))  (build.commute-or @-))
             ((v (!= x nil) (v (! Q) (!= (if x y z) nil)))  (build.right-associativity @-)                       *2)
             ;; ---
             ((v (v (! P) (!= (if x y z) nil))
                 (v (! Q) (!= (if x y z) nil)))             (build.cut *1 *2))
             ((v (! P) (v (! Q) (!= (if x y z) nil)))       (clause.aux-split-twiddle @-))))
  :minatbl ((if . 3)
            (not . 1)))

(defderiv clause.aux-split-positive-bldr
  :derive (!= (if (? a) (? b) (? c)) nil)
  :from   ((proof x (v (!= (not (? a)) nil) (!= (? b) nil)))
           (proof y (v (!= (? a) nil) (!= (? c) nil))))
  :proof  (@derive
           ((v (! (v (!= (not x) nil) (!= y nil)))
               (v (! (v (!= x nil) (!= z nil)))
                  (!= (if x y z) nil)))                      (build.theorem (clause.theorem-aux-split-positive)))
           ((v (! (v (!= (not (? a)) nil) (!= (? b) nil)))
               (v (! (v (!= (? a) nil) (!= (? c) nil)))
                  (!= (if (? a) (? b) (? c)) nil)))          (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
           ((v (!= (not (? a)) nil) (!= (? b) nil))          (@given x))
           ((v (! (v (!= (? a) nil) (!= (? c) nil)))
               (!= (if (? a) (? b) (? c)) nil))              (build.modus-ponens @- @--))
           ((v (!= (? a) nil) (!= (? c) nil))                (@given y))
           ((!= (if (? a) (? b) (? c)) nil)                  (build.modus-ponens @- @--)))
  :minatbl ((if . 3)))

(defderiv clause.disjoined-aux-split-positive-bldr
  :derive (v P (!= (if (? a) (? b) (? c)) nil))
  :from   ((proof x (v P (v (!= (not (? a)) nil) (!= (? b) nil))))
           (proof y (v P (v (!= (? a) nil) (!= (? c) nil)))))
  :proof  (@derive
           ((v (! (v (!= (not x) nil) (!= y nil)))
               (v (! (v (!= x nil) (!= z nil)))
                  (!= (if x y z) nil)))                            (build.theorem (clause.theorem-aux-split-positive)))
           ((v (! (v (!= (not (? a)) nil) (!= (? b) nil)))
               (v (! (v (!= (? a) nil) (!= (? c) nil)))
                  (!= (if (? a) (? b) (? c)) nil)))                (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
           ((v P (v (! (v (!= (not (? a)) nil) (!= (? b) nil)))
                    (v (! (v (!= (? a) nil) (!= (? c) nil)))
                       (!= (if (? a) (? b) (? c)) nil))))          (build.expansion (@formula P) @-))
           ((v P (v (!= (not (? a)) nil) (!= (? b) nil)))          (@given x))
           ((v P (v (! (v (!= (? a) nil) (!= (? c) nil)))
                    (!= (if (? a) (? b) (? c)) nil)))              (build.disjoined-modus-ponens @- @--))
           ((v P (v (!= (? a) nil) (!= (? c) nil)))                (@given y))
           ((v P (!= (if (? a) (? b) (? c)) nil))                  (build.disjoined-modus-ponens @- @--)))
  :minatbl ((if . 3)))

(defderiv clause.aux-split-positive-1-bldr
  :derive (v (v (!= (if (? a) (? b) (? c)) nil) P) Q)
  :from   ((proof x (v (v (!= (not (? a)) nil) (v (!= (? b) nil) P)) Q))
           (proof y (v (v (!= (? a) nil) (v (!= (? c) nil) P)) Q)))
  :proof (@derive
          ((v (v (!= (not (? a)) nil) (v (!= (? b) nil) P)) Q)    (@given x))
          ((v (v P Q) (v (!= (not (? a)) nil) (!= (? b) nil)))    (clause.aux-split-twiddle2 @-)  *1)
          ((v (v (!= (? a) nil) (v (!= (? c) nil) P)) Q)          (@given y))
          ((v (v P Q) (v (!= (? a) nil) (!= (? c) nil)))          (clause.aux-split-twiddle2 @-)  *2)
          ((v (v P Q) (!= (if (? a) (? b) (? c)) nil))            (clause.disjoined-aux-split-positive-bldr *1 *2))
          ((v (!= (if (? a) (? b) (? c)) nil) (v P Q))            (build.commute-or @-))
          ((v (v (!= (if (? a) (? b) (? c)) nil) P) Q)            (build.associativity @-)))
  :minatbl ((if . 3)))

(defderiv clause.aux-split-positive-2-bldr
  :derive (v (!= (if (? a) (? b) (? c)) nil) P)
  :from   ((proof x (v (v (!= (not (? a)) nil) (!= (? b) nil)) P))
           (proof y (v (v (!= (? a) nil) (!= (? c) nil)) P)))
  :proof (@derive
          ((v (v (!= (not (? a)) nil) (!= (? b) nil)) P)    (@given x))
          ((v P (v (!= (not (? a)) nil) (!= (? b) nil)))    (build.commute-or @-)      *1)
          ((v (v (!= (? a) nil) (!= (? c) nil)) P)          (@given y))
          ((v P (v (!= (? a) nil) (!= (? c) nil)))          (build.commute-or @-)      *2)
          ((v P (!= (if (? a) (? b) (? c)) nil))            (clause.disjoined-aux-split-positive-bldr *1 *2))
          ((v (!= (if (? a) (? b) (? c)) nil) P)            (build.commute-or @-)))
  :minatbl ((if . 3)))




;; Builders for the (not (if a b c)) case.

(deftheorem clause.theorem-aux-split-negative
  :derive (v (! (v (!= (not x) nil) (!= (not y) nil)))
             (v (! (v (!= x nil) (!= (not z) nil)))
                (!= (not (if x y z)) nil)))
  :proof  (let ((p (@formula (v (!= (not x) nil) (!= (not y) nil))))
                (q (@formula (v (!= x nil) (!= (not z) nil)))))
            (@derive
             ((v (= x nil) (= (if x y z) y))                       (build.axiom (axiom-if-when-not-nil)))
             ((v (! P) (v (= x nil) (= (if x y z) y)))             (build.expansion (logic.pnot p) @-))
             ((v (v (! P) (= x nil)) (= (if x y z) y))             (build.associativity @-)                          *1a)
             ((v (! P) (v (!= (not x) nil) (!= (not y) nil)))      (build.propositional-schema p))
             ((v (v (! P) (!= (not x) nil)) (!= (not y) nil))      (build.associativity @-))
             ((v (v (! P) (!= (not x) nil)) (= y nil))             (build.disjoined-pequal-nil-from-negative-lit @-))
             ((v (! P) (v (!= (not x) nil) (= y nil)))             (build.right-associativity @-))
             ((v (! P) (v (= y nil) (!= (not x) nil)))             (build.disjoined-commute-or @-))
             ((v (v (! P) (= y nil)) (!= (not x) nil))             (build.associativity @-))
             ((v (v (! P) (= y nil)) (= x nil))                    (build.disjoined-pequal-nil-from-negative-lit @-))
             ((v (! P) (v (= y nil) (= x nil)))                    (build.right-associativity @-))
             ((v (! P) (v (= x nil) (= y nil)))                    (build.disjoined-commute-or @-))
             ((v (v (! P) (= x nil)) (= y nil))                    (build.associativity @-))
             ((v (v (! P) (= x nil)) (= (if x y z) nil))           (build.disjoined-transitivity-of-pequal *1a @-))
             ((v (v (! P) (= x nil)) (!= (not (if x y z)) nil))    (build.disjoined-negative-lit-from-pequal-nil @-))
             ((v (!= (not (if x y z)) nil) (v (! P) (= x nil)))    (build.commute-or @-))
             ((v (v (!= (not (if x y z)) nil) (! P)) (= x nil))    (build.associativity @-))
             ((v (= x nil) (v (!= (not (if x y z)) nil) (! P)))    (build.commute-or @-))
             ((v (= x nil) (v (! P) (!= (not (if x y z)) nil)))    (build.disjoined-commute-or @-)                   *1)
             ;; ---
             ((v (!= x nil) (= (if x y z) z))                      (build.axiom (axiom-if-when-nil)))
             ((v (! Q) (v (!= x nil) (= (if x y z) z)))            (build.expansion (logic.pnot q) @-))
             ((v (v (! Q) (!= x nil)) (= (if x y z) z))            (build.associativity @-)                          *2a)
             ((v (! Q) (v (!= x nil) (!= (not z) nil)))            (build.propositional-schema q))
             ((v (v (! Q) (!= x nil)) (!= (not z) nil))            (build.associativity @-))
             ((v (v (! Q) (!= x nil)) (= z nil))                   (build.disjoined-pequal-nil-from-negative-lit @-))
             ((v (v (! Q) (!= x nil)) (= (if x y z) nil))          (build.disjoined-transitivity-of-pequal *2a @-))
             ((v (v (! Q) (!= x nil)) (!= (not (if x y z)) nil))   (build.disjoined-negative-lit-from-pequal-nil @-))
             ((v (!= (not (if x y z)) nil) (v (! Q) (!= x nil)))   (build.commute-or @-))
             ((v (!= (not (if x y z)) nil) (v (!= x nil) (! Q)))   (build.disjoined-commute-or @-))
             ((v (v (!= x nil) (! Q)) (!= (not (if x y z)) nil))   (build.commute-or @-))
             ((v (!= x nil) (v (! Q) (!= (not (if x y z)) nil)))   (build.right-associativity @-)                    *2)
             ;; ---
             ((v (v (! P) (!= (not (if x y z)) nil))
                 (v (! Q) (!= (not (if x y z)) nil)))              (build.cut *1 *2))
             ((v (! P) (v (! Q) (!= (not (if x y z)) nil)))        (clause.aux-split-twiddle @-))))
  :minatbl ((if . 3)
            (not . 1)))

(defderiv clause.aux-split-negative-bldr
  :derive (!= (not (if (? a) (? b) (? c))) nil)
  :from   ((proof x (v (!= (not (? a)) nil) (!= (not (? b)) nil)))
           (proof y (v (!= (? a) nil) (!= (not (? c)) nil))))
  :proof  (@derive
           ((v (! (v (!= (not x) nil) (!= (not y) nil)))
               (v (! (v (!= x nil) (!= (not z) nil)))
                  (!= (not (if x y z)) nil)))                      (build.theorem (clause.theorem-aux-split-negative)))
           ((v (! (v (!= (not (? a)) nil) (!= (not (? b)) nil)))
               (v (! (v (!= (? a) nil) (!= (not (? c)) nil)))
                  (!= (not (if (? a) (? b) (? c))) nil)))          (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
           ((v (!= (not (? a)) nil) (!= (not (? b)) nil))          (@given x))
           ((v (! (v (!= (? a) nil) (!= (not (? c)) nil)))
               (!= (not (if (? a) (? b) (? c))) nil))              (build.modus-ponens @- @--))
           ((v (!= (? a) nil) (!= (not (? c)) nil))                (@given y))
           ((!= (not (if (? a) (? b) (? c))) nil)                  (build.modus-ponens @- @--)))
  :minatbl ((if . 3)))

(defderiv clause.disjoined-aux-split-negative-bldr
  :derive (v P (!= (not (if (? a) (? b) (? c))) nil))
  :from   ((proof x (v P (v (!= (not (? a)) nil) (!= (not (? b)) nil))))
           (proof y (v P (v (!= (? a) nil) (!= (not (? c)) nil)))))
  :proof  (@derive
           ((v (! (v (!= (not x) nil) (!= (not y) nil)))
               (v (! (v (!= x nil) (!= (not z) nil)))
                  (!= (not (if x y z)) nil)))                            (build.theorem (clause.theorem-aux-split-negative)))
           ((v (! (v (!= (not (? a)) nil) (!= (not (? b)) nil)))
               (v (! (v (!= (? a) nil) (!= (not (? c)) nil)))
                  (!= (not (if (? a) (? b) (? c))) nil)))                (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
           ((v P (v (! (v (!= (not (? a)) nil) (!= (not (? b)) nil)))
                    (v (! (v (!= (? a) nil) (!= (not (? c)) nil)))
                       (!= (not (if (? a) (? b) (? c))) nil))))          (build.expansion (@formula P) @-))
           ((v P (v (!= (not (? a)) nil) (!= (not (? b)) nil)))          (@given x))
           ((v P (v (! (v (!= (? a) nil) (!= (not (? c)) nil)))
                    (!= (not (if (? a) (? b) (? c))) nil)))              (build.disjoined-modus-ponens @- @--))
           ((v P (v (!= (? a) nil) (!= (not (? c)) nil)))                (@given y))
           ((v P (!= (not (if (? a) (? b) (? c))) nil))                  (build.disjoined-modus-ponens @- @--)))
  :minatbl ((if . 3)))


(defderiv clause.aux-split-negative-1-bldr-lemma-1
  :derive (v (v P Q) (!= (not (if (? a) (? b) (? c))) nil))
  :from   ((proof x (v (v (!= (not (? a)) nil) (v (!= (not (? b)) nil) P)) Q))
           (proof y (v (v (!= (? a) nil) (v (!= (not (? c)) nil) P)) Q)))
  :proof  (@derive
           ((v (v (!= (not (? a)) nil) (v (!= (not (? b)) nil) P)) Q)   (@given x))
           ((v (v P Q) (v (!= (not (? a)) nil) (!= (not (? b)) nil)))   (clause.aux-split-twiddle2 @-)  *1)
           ((v (v (!= (? a) nil) (v (!= (not (? c)) nil) P)) Q)         (@given y))
           ((v (v P Q) (v (!= (? a) nil) (!= (not (? c)) nil)))         (clause.aux-split-twiddle2 @-))
           ((v (v P Q) (!= (not (if (? a) (? b) (? c))) nil))           (clause.disjoined-aux-split-negative-bldr *1 @-)))
  :minatbl ((if . 3)))

(encapsulate
 ()
 (defthmd equal-when-logic.functionp-and-logic.functionp
   (implies (and (logic.functionp x)
                 (logic.functionp y))
            (equal (equal x y)
                   (and (equal (logic.function-name x) (logic.function-name y))
                        (equal (logic.function-args x) (logic.function-args y)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable logic.functionp logic.function-name logic.function-args))))

 (defthmd equal-of-one-tuples
   (implies (and (equal (len x) 1)
                 (equal (len y) 1)
                 (true-listp x)
                 (true-listp y))
            (equal (equal x y)
                   (equal (first x) (first y))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthmd equal-of-logic.function-args-and-logic.function-args-when-one-tuples
   (implies (and (equal (len (logic.function-args x)) 1)
                 (equal (len (logic.function-args y)) 1)
                 (force (logic.functionp x))
                 (force (logic.functionp y))
                 (force (logic.termp x))
                 (force (logic.termp y)))
            (equal (equal (logic.function-args x)
                          (logic.function-args y))
                   (equal (first (logic.function-args x))
                          (first (logic.function-args y)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance equal-of-one-tuples
                                   (x (logic.function-args x))
                                   (y (logic.function-args y)))))))

 (local (in-theory (enable equal-when-logic.functionp-and-logic.functionp
                           equal-of-one-tuples
                           equal-of-logic.function-args-and-logic.function-args-when-one-tuples)))

 (defderiv clause.aux-split-negative-1-bldr-lemma-2
   :derive (v (v (!= (? t1) nil) P) Q)
   :from   ((proof x (v (v P Q) (!= (not (? a)) nil)))
            (proof y (= (? t1) (not (? a)))))
   :proof  (@derive
            ((v (v P Q) (!= (not (? a)) nil))     (@given x) *1)
            ((= (? t1) (not (? a)))               (@given y))
            ((v (v P Q) (= (? t1) (not (? a))))   (build.expansion (@formula (v P Q)) @-))
            ((v (v P Q) (!= (? t1) nil))          (build.disjoined-substitute-into-not-pequal *1 @-))
            ((v (!= (? t1) nil) (v P Q))          (build.commute-or @-))
            ((v (v (!= (? t1) nil) P) Q)          (build.associativity @-)))))

(defderiv clause.aux-split-negative-1-bldr
  :derive (v (v (!= (? t1) nil) P) Q)
  :from   ((proof x (v (v (!= (not (? a)) nil) (v (!= (not (? b)) nil) P)) Q))
           (proof y (v (v (!= (? a) nil) (v (!= (not (? c)) nil) P)) Q))
           (proof z (= (? t1) (not (if (? a) (? b) (? c))))))
  :proof (@derive
          ((v (v (!= (not (? a)) nil) (v (!= (not (? b)) nil) P)) Q)   (@given x))
          ((v (v (!= (? a) nil) (v (!= (not (? c)) nil) P)) Q)         (@given y))
          ((v (v P Q) (!= (not (if (? a) (? b) (? c))) nil))           (clause.aux-split-negative-1-bldr-lemma-1 @-- @-))
          ((= (? t1) (not (if (? a) (? b) (? c))))                     (@given z))
          ((v (v (!= (? t1) nil) P) Q)                                 (clause.aux-split-negative-1-bldr-lemma-2 @-- @-))))


(defderiv clause.aux-split-negative-2-bldr-lemma-1
  :derive (v P (!= (not (if (? a) (? b) (? c))) nil))
  :from   ((proof x (v (v (!= (not (? a)) nil) (!= (not (? b)) nil)) P))
           (proof y (v (v (!= (? a) nil) (!= (not (? c)) nil)) P)))
  :proof  (@derive
           ((v (v (!= (not (? a)) nil) (!= (not (? b)) nil)) P)         (@given x))
           ((v P (v (!= (not (? a)) nil) (!= (not (? b)) nil)))         (build.commute-or @-)       *1)
           ((v (v (!= (? a) nil) (!= (not (? c)) nil)) P)               (@given y))
           ((v P (v (!= (? a) nil) (!= (not (? c)) nil)))               (build.commute-or @-)       *2)
           ((v P (!= (not (if (? a) (? b) (? c))) nil))                 (clause.disjoined-aux-split-negative-bldr *1 *2)))
  :minatbl ((if . 3)))

(encapsulate
 ()
 (local (in-theory (enable equal-when-logic.functionp-and-logic.functionp
                           equal-of-logic.function-args-and-logic.function-args-when-one-tuples)))

 (defderiv clause.aux-split-negative-2-bldr-lemma-2
   :derive (v (!= (? t1) nil) P)
   :from   ((proof x (= (? t1) (not (? a))))
            (proof y (v P (!= (not (? a)) nil))))
   :proof  (@derive
            ((= (? t1) (not (? a)))           (@given x))
            ((v P (= (? t1) (not (? a))))     (build.expansion (@formula P) @-))
            ((v P (!= (not (? a)) nil))       (@given y))
            ((v P (!= (? t1) nil))            (build.disjoined-substitute-into-not-pequal @- @--))
            ((v (!= (? t1) nil) P)            (build.commute-or @-)))))

(defderiv clause.aux-split-negative-2-bldr
  :derive (v (!= (? t1) nil) P)
  :from   ((proof x (v (v (!= (not (? a)) nil) (!= (not (? b)) nil)) P))
           (proof y (v (v (!= (? a) nil) (!= (not (? c)) nil)) P))
           (proof z (= (? t1) (not (if (? a) (? b) (? c))))))
  :proof  (@derive
           ((v (v (!= (not (? a)) nil) (!= (not (? b)) nil)) P)         (@given x))
           ((v (v (!= (? a) nil) (!= (not (? c)) nil)) P)               (@given y))
           ((v P (!= (not (if (? a) (? b) (? c))) nil))                 (clause.aux-split-negative-2-bldr-lemma-1 @-- @-))
           ((= (? t1) (not (if (? a) (? b) (? c))))                     (@given z))
           ((v (!= (? t1) nil) P)                                       (clause.aux-split-negative-2-bldr-lemma-2 @- @--))))



;; Builders for the default case.

(defderiv clause.aux-split-default-1-bldr
  :derive (v (v (!= (? a) nil) P) Q)
  :from   ((proof x (v P (v (!= (? b) nil) Q)))
           (proof y (= (? a) (? b))))
  :proof  (@derive
           ((v P (v (!= (? b) nil) Q))   (@given x))
           ((v (v P (!= (? b) nil)) Q)   (build.associativity @-))
           ((v Q (v P (!= (? b) nil)))   (build.commute-or @-))
           ((v (v Q P) (!= (? b) nil))   (build.associativity @-)  *1)
           ((= (? a) (? b))              (@given y))
           ((v (v Q P) (= (? a) (? b)))  (build.expansion (@formula (v Q P)) @-))
           ((v (v Q P) (!= (? a) nil))   (build.disjoined-substitute-into-not-pequal *1 @-))
           ((v (!= (? a) nil) (v Q P))   (build.commute-or @-))
           ((v (!= (? a) nil) (v P Q))   (build.disjoined-commute-or @-))
           ((v (v (!= (? a) nil) P) Q)   (build.associativity @-))))

(defderiv clause.aux-split-default-2-bldr
  :derive (v (!= (? a) nil) P)
  :from   ((proof x (v P (!= (? b) nil)))
           (proof y (= (? a) (? b))))
  :proof  (@derive
           ((= (? a) (? b))       (@given y))
           ((v P (= (? a) (? b))) (build.expansion (@formula P) @-))
           ((v P (!= (? b) nil))  (@given x))
           ((v P (!= (? a) nil))  (build.disjoined-substitute-into-not-pequal @- @--))
           ((v (!= (? a) nil) P)  (build.commute-or @-))))



;; Originally I didn't bother to introduce clause.aux-split-goal and the other supporting
;; functions based on it below.  This approach worked fine in the ACL2 model, but I wasn't
;; able to handle the complexity of the proof during bootstrapping.  The new approach has
;; many more functions, but they are all comparatively simple and hence the work can be
;; broken up a lot better.  The key to doing this splitting is to introduce something like
;; clause.aux-split-goal, so the case-split about what kind of formula is being proven
;; can be contained.

(definlined clause.aux-split-double-negate (t1 t2-tn done proof)
  (declare (xargs :guard (and (logic.termp t1)
                              (clause.negative-termp t1)
                              (clause.negative-termp (clause.negative-term-guts t1))
                              (logic.term-listp t2-tn)
                              (logic.term-listp done)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.aux-split-goal (cons (clause.negative-term-guts
                                                                   (clause.negative-term-guts t1))
                                                                  t2-tn)
                                                            done)))
                  :verify-guards nil))
  (let ((lemma (clause.standardize-double-negative-term-under-iff-bldr t1)))
    (if (consp t2-tn)
        (if (consp done)
            (clause.aux-split-double-negate-lemma1-bldr proof lemma)
          (clause.aux-split-double-negate-lemma2-bldr proof lemma))
      (if (consp done)
          (clause.aux-split-double-negate-lemma2-bldr proof lemma)
        (clause.substitute-iff-into-literal-bldr proof lemma)))))

(defobligations clause.aux-split-double-negate
  (clause.standardize-double-negative-term-under-iff-bldr
   clause.aux-split-double-negate-lemma1-bldr
   clause.aux-split-double-negate-lemma2-bldr
   clause.substitute-iff-into-literal-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-goal
                           clause.aux-split-double-negate
                           logic.term-formula)))

 (verify-guards clause.aux-split-double-negate)

 (defthm forcing-logic.appealp-of-clause.aux-split-double-negate
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (clause.negative-termp (clause.negative-term-guts t1))
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal (cons (clause.negative-term-guts
                                                             (clause.negative-term-guts t1))
                                                            t2-tn)
                                                      done))))
            (equal (logic.appealp (clause.aux-split-double-negate t1 t2-tn done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-split-double-negate
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (clause.negative-termp (clause.negative-term-guts t1))
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal (cons (clause.negative-term-guts
                                                             (clause.negative-term-guts t1))
                                                            t2-tn)
                                                      done))))
            (equal (logic.conclusion (clause.aux-split-double-negate t1 t2-tn done proof))
                   (clause.aux-split-goal (cons t1 t2-tn) done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-double-negate
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (clause.negative-termp (clause.negative-term-guts t1))
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal (cons (clause.negative-term-guts
                                                             (clause.negative-term-guts t1))
                                                            t2-tn)
                                                      done))
                        ;; ---
                        (logic.term-atblp t1 atbl)
                        (logic.proofp proof axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.aux-split-double-negate)))
            (equal (logic.proofp (clause.aux-split-double-negate t1 t2-tn done proof) axioms thms atbl)
                   t))))







(definlined clause.aux-split-negated-if (t1 t2-tn done proof1 proof2)
  (declare (xargs :guard (and (logic.termp t1)
                              (clause.negative-termp t1)
                              (logic.functionp (clause.negative-term-guts t1))
                              (equal (logic.function-name (clause.negative-term-guts t1)) 'if)
                              (equal (len (logic.function-args (clause.negative-term-guts t1))) 3)
                              (logic.term-listp t2-tn)
                              (logic.term-listp done)
                              (logic.appealp proof1)
                              (logic.appealp proof2)
                              (equal (logic.conclusion proof1)
                                     (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts t1)))))
                                                                  (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts t1)))))
                                                                        t2-tn))
                                                            done))
                              (equal (logic.conclusion proof2)
                                     (clause.aux-split-goal (cons (first (logic.function-args (clause.negative-term-guts t1)))
                                                                  (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts t1)))))
                                                                        t2-tn))
                                                            done)))
                  :verify-guards nil))
  ;; Matched a negated term of the form (if a b c)
  ;; Goal:   (t1 != nil [v T2...Tn]) [v D1...Dm]
  ;; Lemma:  t1 = (not (if a b c))
  ;; Proof1: ((not a) != nil v (not b) != nil [v T2...Tn]) [v D1...Dm]
  ;; Proof2: (a != nil v (not c) != nil [v T2...Tn]) [v D1...Dm]
  (let ((lemma (clause.standardize-negative-term-bldr t1)))
    (if (consp t2-tn)
        (if (consp done)
            (clause.aux-split-negative-1-bldr proof1 proof2 lemma)
          (clause.aux-split-negative-2-bldr (build.associativity proof1)
                                            (build.associativity proof2)
                                            lemma))
      (if (consp done)
          (clause.aux-split-negative-2-bldr proof1 proof2 lemma)
        (build.substitute-into-not-pequal (clause.aux-split-negative-bldr proof1 proof2)
                                          lemma)))))

(defobligations clause.aux-split-negated-if
  (clause.standardize-negative-term-bldr
   clause.aux-split-negative-1-bldr
   clause.aux-split-negative-2-bldr
   clause.aux-split-negative-bldr
   build.substitute-into-not-pequal))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-goal
                           clause.aux-split-negated-if
                           logic.term-formula)))

 (defthm len-when-not-consp-of-cdr-cheap
   ;; BOZO move to utilities
   (implies (not (consp (cdr x)))
            (equal (len x)
                   (if (consp x)
                       1
                     0)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (verify-guards clause.aux-split-negated-if)

 (defthm forcing-logic.appealp-of-clause.aux-split-negated-if
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.functionp (clause.negative-term-guts t1))
                        (equal (logic.function-name (clause.negative-term-guts t1)) 'if)
                        (equal (len (logic.function-args (clause.negative-term-guts t1))) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts t1)))))
                                                            (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args (clause.negative-term-guts t1)))
                                                            (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))))
            (equal (logic.appealp (clause.aux-split-negated-if t1 t2-tn done proof1 proof2))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-split-negated-if
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.functionp (clause.negative-term-guts t1))
                        (equal (logic.function-name (clause.negative-term-guts t1)) 'if)
                        (equal (len (logic.function-args (clause.negative-term-guts t1))) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts t1)))))
                                                            (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args (clause.negative-term-guts t1)))
                                                            (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))))
            (equal (logic.conclusion (clause.aux-split-negated-if t1 t2-tn done proof1 proof2))
                   (clause.aux-split-goal (cons t1 t2-tn) done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-negated-if
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.functionp (clause.negative-term-guts t1))
                        (equal (logic.function-name (clause.negative-term-guts t1)) 'if)
                        (equal (len (logic.function-args (clause.negative-term-guts t1))) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args (clause.negative-term-guts t1)))))
                                                            (cons (logic.function 'not (list (second (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args (clause.negative-term-guts t1)))
                                                            (cons (logic.function 'not (list (third (logic.function-args (clause.negative-term-guts t1)))))
                                                                  t2-tn))
                                                      done))
                        ;; ---
                        (logic.term-atblp t1 atbl)
                        (logic.proofp proof1 axioms thms atbl)
                        (logic.proofp proof2 axioms thms atbl)
                        (@obligations clause.aux-split-negated-if)))
            (equal (logic.proofp (clause.aux-split-negated-if t1 t2-tn done proof1 proof2) axioms thms atbl)
                   t))))




(definlined clause.aux-split-positive-if (t1 t2-tn done proof1 proof2)
  (declare (xargs :guard (and (logic.termp t1)
                              (logic.functionp t1)
                              (equal (logic.function-name t1) 'if)
                              (equal (len (logic.function-args t1)) 3)
                              (logic.term-listp t2-tn)
                              (logic.term-listp done)
                              (logic.appealp proof1)
                              (logic.appealp proof2)
                              (equal (logic.conclusion proof1)
                                     (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args t1))))
                                                                  (cons (second (logic.function-args t1))
                                                                        t2-tn))
                                                            done))
                              (equal (logic.conclusion proof2)
                                     (clause.aux-split-goal (cons (first (logic.function-args t1))
                                                                  (cons (third (logic.function-args t1))
                                                                        t2-tn))
                                                            done)))
                  :verify-guards nil)
           (ignore t1))
  ;; Matched a positive term of the form (if a b c)
  ;; Goal: (t1 != nil [v T2...Tn]) [v D1...Dm]
  ;; Proof1: ((not a) != nil v b != nil [v T2...Tn]) [v D1...Dm]
  ;; Proof2: (a != nil v c != nil [v T2...Tn]) [v D1...Dm]
  (if (consp t2-tn)
      (if (consp done)
          (clause.aux-split-positive-1-bldr proof1 proof2)
        (clause.aux-split-positive-2-bldr (build.associativity proof1)
                                          (build.associativity proof2)))
    (if (consp done)
        (clause.aux-split-positive-2-bldr proof1 proof2)
      (clause.aux-split-positive-bldr proof1 proof2))))

(defobligations clause.aux-split-positive-if
  (clause.aux-split-positive-1-bldr
   clause.aux-split-positive-2-bldr
   clause.aux-split-positive-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-goal
                           clause.aux-split-positive-if
                           logic.term-formula)))

 (verify-guards clause.aux-split-positive-if)

 (defthm forcing-logic.appealp-of-clause.aux-split-positive-if
   (implies (force (and (logic.termp t1)
                        (logic.functionp t1)
                        (equal (logic.function-name t1) 'if)
                        (equal (len (logic.function-args t1)) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args t1))))
                                                            (cons (second (logic.function-args t1))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args t1))
                                                            (cons (third (logic.function-args t1))
                                                                  t2-tn))
                                                      done))))
            (equal (logic.appealp (clause.aux-split-positive-if t1 t2-tn done proof1 proof2))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-split-positive-if
   (implies (force (and (logic.termp t1)
                        (logic.functionp t1)
                        (equal (logic.function-name t1) 'if)
                        (equal (len (logic.function-args t1)) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args t1))))
                                                            (cons (second (logic.function-args t1))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args t1))
                                                            (cons (third (logic.function-args t1))
                                                                  t2-tn))
                                                      done))))
            (equal (logic.conclusion (clause.aux-split-positive-if t1 t2-tn done proof1 proof2))
                   (clause.aux-split-goal (cons t1 t2-tn) done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-positive-if
   (implies (force (and (logic.termp t1)
                        (logic.functionp t1)
                        (equal (logic.function-name t1) 'if)
                        (equal (len (logic.function-args t1)) 3)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof1)
                        (logic.appealp proof2)
                        (equal (logic.conclusion proof1)
                               (clause.aux-split-goal (cons (logic.function 'not (list (first (logic.function-args t1))))
                                                            (cons (second (logic.function-args t1))
                                                                  t2-tn))
                                                      done))
                        (equal (logic.conclusion proof2)
                               (clause.aux-split-goal (cons (first (logic.function-args t1))
                                                            (cons (third (logic.function-args t1))
                                                                  t2-tn))
                                                      done))
                        ;; ---
                        (logic.term-atblp t1 atbl)
                        (logic.proofp proof1 axioms thms atbl)
                        (logic.proofp proof2 axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (@obligations clause.aux-split-positive-if)))
            (equal (logic.proofp (clause.aux-split-positive-if t1 t2-tn done proof1 proof2) axioms thms atbl)
                   t))))





(definlined clause.aux-split-negative-default (t1 t2-tn done proof)
  (declare (xargs :guard (and (logic.termp t1)
                              (clause.negative-termp t1)
                              (logic.term-listp t2-tn)
                              (logic.term-listp done)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.aux-split-goal t2-tn
                                                            (cons (logic.function 'not (list (clause.negative-term-guts t1)))
                                                                  done))))
                  :verify-guards nil))
  ;; Matched a negative term of some non-if form.
  ;; Goal is (t1 != nil [v T2...Tn]) [v D1...Dm]
  ;; Proof is [T2...Tn v] ((not guts) != nil [v D1...Dm])
  ;; Lemma is t1 = (not guts)
  (let ((lemma (clause.standardize-negative-term-bldr t1)))
    (if (consp t2-tn)
        (if (consp done)
            (clause.aux-split-default-1-bldr proof lemma)
          (clause.aux-split-default-2-bldr proof lemma))
      (if (consp done)
          (clause.aux-split-default-2-bldr (build.commute-or proof) lemma)
        (build.substitute-into-not-pequal proof lemma)))))

(defobligations clause.aux-split-negative-default
  (clause.standardize-negative-term-bldr
   clause.aux-split-default-1-bldr
   clause.aux-split-default-2-bldr
   build.substitute-into-not-pequal
   build.commute-or))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-goal
                           clause.aux-split-negative-default
                           logic.term-formula)))

 (verify-guards clause.aux-split-negative-default)

 (defthm forcing-logic.appealp-of-clause.aux-split-negative-default
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn
                                                      (cons (logic.function 'not (list (clause.negative-term-guts t1)))
                                                            done)))))
            (equal (logic.appealp (clause.aux-split-negative-default t1 t2-tn done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-split-negative-default
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn
                                                      (cons (logic.function 'not (list (clause.negative-term-guts t1)))
                                                            done)))))
            (equal (logic.conclusion (clause.aux-split-negative-default t1 t2-tn done proof))
                   (clause.aux-split-goal (cons t1 t2-tn) done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-negative-default
   (implies (force (and (logic.termp t1)
                        (clause.negative-termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn
                                                      (cons (logic.function 'not (list (clause.negative-term-guts t1)))
                                                            done)))
                        ;; ---
                        (logic.term-atblp t1 atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations clause.aux-split-negative-default)))
            (equal (logic.proofp (clause.aux-split-negative-default t1 t2-tn done proof) axioms thms atbl)
                   t))))




(definlined clause.aux-split-positive-default (t1 t2-tn done proof)
  (declare (xargs :guard (and (logic.termp t1)
                              (logic.term-listp t2-tn)
                              (logic.term-listp done)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (clause.aux-split-goal t2-tn (cons t1 done))))
                  :verify-guards nil)
           (ignore t1))
  ;; Matched a positive term of some non-if form.
  ;; Goal is (t1 != nil [v T2...Tn]) [v D1...Dm]
  ;; Proof is [T2...Tn v] (t1 != nil [v D1...Dm])
  (if (consp t2-tn)
      (if (consp done)
          (clause.aux-split-default-3-bldr proof)
        (build.commute-or proof))
    proof))

(defobligations clause.aux-split-positive-default
  (clause.aux-split-default-3-bldr
   build.commute-or))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-goal
                           clause.aux-split-positive-default
                           logic.term-formula)))

 (verify-guards clause.aux-split-positive-default)

 (defthm forcing-logic.appealp-of-clause.aux-split-positive-default
   (implies (force (and (logic.termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn (cons t1 done)))))
            (equal (logic.appealp (clause.aux-split-positive-default t1 t2-tn done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-split-positive-default
   (implies (force (and (logic.termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn (cons t1 done)))))
            (equal (logic.conclusion (clause.aux-split-positive-default t1 t2-tn done proof))
                   (clause.aux-split-goal (cons t1 t2-tn) done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-split-positive-default
   (implies (force (and (logic.termp t1)
                        (logic.term-listp t2-tn)
                        (logic.term-listp done)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (clause.aux-split-goal t2-tn (cons t1 done)))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)
                        (@obligations clause.aux-split-positive-default)))
            (equal (logic.proofp (clause.aux-split-positive-default t1 t2-tn done proof) axioms thms atbl)
                   t))))






