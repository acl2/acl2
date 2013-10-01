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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "prop.tex")

(defderiv build.commute-or
  :from   ((proof x (v A B)))
  :derive (v B A)
  :proof  (@derive ((v A B)               (@given x))
                   ((v (! A) A)           (build.propositional-schema (@formula A)))
                   ((v B A)               (build.cut @-- @-))))

(defderiv build.right-expansion
  :from   ((proof x A)
           (formula b B))
  :derive (v A B)
  :proof  (@derive ((v A B)               (@given x))
                   ((v B A)               (build.expansion b @-))
                   ((v A B)               (build.commute-or @-))))

(defderiv build.modus-ponens
  :from   ((proof x A)
           (proof y (v (! A) B)))
  :derive B
  :proof  (@derive (A                     (@given x))
                   ((v A B)               (build.right-expansion @- (@formula B)))
                   ((v (! A) B)           (@given y))
                   ((v B B)               (build.cut @-- @-))
                   (B                     (build.contraction @-))))

(defderiv build.modus-ponens-2
  :from   ((proof x (! A))
           (proof y (v A B)))
  :derive B
  :proof  (@derive ((! A)                 (@given x))
                   ((v (! A) B)           (build.right-expansion @- (@formula B)))
                   ((v A B)               (@given y))
                   ((v B B)               (build.cut @- @--))
                   (B                     (build.contraction @-))))

(defderiv build.right-associativity
  :from   ((proof x (v (v A B) C)))
  :derive (v A (v B C))
  :proof  (@derive ((v (v A B) C)         (@given x))
                   ((v C (v A B))         (build.commute-or @-))
                   ((v (v C A) B)         (build.associativity @-))
                   ((v B (v C A))         (build.commute-or @-))
                   ((v (v B C) A)         (build.associativity @-))
                   ((v A (v B C))         (build.commute-or @-))))

(defderiv build.disjoined-left-expansion
  :from   ((proof x (v P A))
           (formula b B))
  :derive (v P (v B A))
  :proof  (@derive ((v P A)               (@given x))
                   ((v A P)               (build.commute-or @-))
                   ((v B (v A P))         (build.expansion (@formula B) @-))
                   ((v (v B A) P)         (build.associativity @-))
                   ((v P (v B A))         (build.commute-or @-))))

(defderiv build.disjoined-right-expansion
  :from   ((proof x (v P A))
           (formula b B))
  :derive (v P (v A B))
  :proof  (@derive ((v P A)               (@given x))
                   ((v B (v P A))         (build.expansion (@formula B) @-))
                   ((v (v B P) A)         (build.associativity @-))
                   ((v A (v B P))         (build.commute-or @-))
                   ((v (v A B) P)         (build.associativity @-))
                   ((v P (v A B))         (build.commute-or @-))))

(defderiv build.disjoined-contraction
  :from   ((proof x (v P (v A A))))
  :derive (v P A)
  :proof  (@derive ((v P (v A A))         (@given x))
                   ((v (v P A) A)         (build.associativity @-))
                   ((v A (v P A))         (build.commute-or @-))
                   ((v P (v A (v P A)))   (build.expansion (@formula P) @-))
                   ((v (v P A) (v P A))   (build.associativity @-))
                   ((v P A)               (build.contraction @-))))

(defderiv build.cancel-neg-neg
  :from   ((proof x (! (! A))))
  :derive A
  :proof  (@derive ((! (! A))             (@given x))
                   ((v (! A) A)           (build.propositional-schema (@formula A)))
                   (A                     (build.modus-ponens-2 @-- @-))))

(defderiv build.insert-neg-neg
  :from   ((proof x A))
  :derive (! (! A))
  :proof  (@derive ((v (! (! A)) (! A))   (build.propositional-schema (@formula (! A))))
                   ((v (! A) (! (! A)))   (build.commute-or @-))
                   (A                     (@given x))
                   ((! (! A))             (build.modus-ponens @- @--))))

(defderiv build.lhs-insert-neg-neg
  :from   ((proof x (v A B)))
  :derive (v (! (! A)) B)
  :proof  (@derive ((v (! (! A)) (! A))   (build.propositional-schema (@formula (! A))))
                   ((v (! A) (! (! A)))   (build.commute-or @-))
                   ((v A B)               (@given x))
                   ((v B (! (! A)))       (build.cut @- @--))
                   ((v (! (! A)) B)       (build.commute-or @-))))

(defderiv build.lhs-cancel-neg-neg
  :from   ((proof x (v (! (! A)) B)))
  :derive (v A B)
  :proof  (@derive ((v (! A) A)           (build.propositional-schema (@formula A)))
                   ((v (! (! A)) B)       (@given x))
                   ((v A B)               (build.cut @-- @-))))

(defderiv build.merge-negatives
  :from   ((proof x (! A))
           (proof y (! B)))
  :derive (! (v A B))
  :proof  (@derive ((v (! (v A B)) (v A B))   (build.propositional-schema (@formula (v A B))))
                   ((v (v (! (v A B)) A) B)   (build.associativity @-))
                   ((v B (v (! (v A B)) A))   (build.commute-or @-))
                   ((! B)                     (@given y))
                   ((v (! (v A B)) A)         (build.modus-ponens-2 @- @--))
                   ((v A (! (v A B)))         (build.commute-or @-))
                   ((! A)                     (@given x))
                   ((! (v A B))               (build.modus-ponens-2 @- @--))))

(defderiv build.merge-implications-lemma-1
  :from   ((proof x (v (! B) C))
           (formula a A))
  :derive (v A (v C (! (v A B))))
  :proof  (@derive ((v (! (v A B)) (v A B))   (build.propositional-schema (@formula (v A B))))
                   ((v (v (! (v A B)) A) B)   (build.associativity @-))
                   ((v B (v (! (v A B)) A))   (build.commute-or @-))
                   ((v (! B) C)               (@given x))
                   ((v (v (! (v A B)) A) C)   (build.cut @-- @-))
                   ((v C (v (! (v A B)) A))   (build.commute-or @-))
                   ((v (v C (! (v A B))) A)   (build.associativity @-))
                   ((v A (v C (! (v A B))))   (build.commute-or @-))))

(defderiv build.merge-implications-lemma-2
  :from   ((proof x (v A (v C D)))
           (proof y (v (! A) C)))
  :derive (v D C)
  :proof  (@derive ((v A (v C D))   (@given x))
                   ((v (! A) C)     (@given y))
                   ((v (v C D) C)   (build.cut @-- @-))
                   ((v C (v C D))   (build.commute-or @-))
                   ((v (v C C) D)   (build.associativity @-))
                   ((v D (v C C))   (build.commute-or @-))
                   ((v D C)         (build.disjoined-contraction @-))))

(defderiv build.merge-implications
  :from   ((proof x (v (! A) C))
           (proof y (v (! B) C)))
  :derive (v (! (v A B)) C)
  :proof  (@derive
           ((v (! B) C)                 (@given y))
           ((v A (v C (! (v A B))))     (build.merge-implications-lemma-1 @- (@formula A)))
           ((v (! A) C)                 (@given x))
           ((v (! (v A B)) C)           (build.merge-implications-lemma-2 @-- @-))))

(defderiv build.disjoined-commute-or-lemma-1
  :from   ((proof x (v P (v A B))))
  :derive (v A (v (v B A) P))
  :proof  (@derive ((v P (v A B))               (@given x))
                   ((v (v P A) B)               (build.associativity @-))
                   ((v A (v (v P A) B))         (build.expansion (@formula A) @-))
                   ((v (v A (v P A)) B)         (build.associativity @-))
                   ((v B (v A (v P A)))         (build.commute-or @-))
                   ((v (v B A) (v P A))         (build.associativity @-))
                   ((v (v (v B A) P) A)         (build.associativity @-))
                   ((v A (v (v B A) P))         (build.commute-or @-))))

(defderiv build.disjoined-commute-or
  :from   ((proof x (v P (v A B))))
  :derive (v P (v B A))
  :proof  (@derive
           ((v P (v A B))               (@given x))
           ((v A (v (v B A) P))         (build.disjoined-commute-or-lemma-1 @-))
           ((v B (v A (v (v B A) P)))   (build.expansion (@formula B) @-))
           ((v (v B A) (v (v B A) P))   (build.associativity @-))
           ((v (v (v B A) (v B A)) P)   (build.associativity @-))
           ((v P (v (v B A) (v B A)))   (build.commute-or @-))
           ((v P (v B A))               (build.disjoined-contraction @-))))

(defderiv build.disjoined-assoc-lemma-1a
  :from   ((formula b B)
           (formula c C)
           (proof x (v P (v A D))))
  :derive (v A (v B (v (v C D) P)))
  :proof  (@derive ((v P (v A D))               (@given x))
                   ((v (v P A) D)               (build.associativity @-))
                   ((v D (v P A))               (build.commute-or @-))
                   ((v C (v D (v P A)))         (build.expansion (@formula C) @-))
                   ((v (v C D) (v P A))         (build.associativity @-))
                   ((v (v (v C D) P) A)         (build.associativity @-))
                   ((v B (v (v (v C D) P) A))   (build.expansion (@formula B) @-))
                   ((v (v B (v (v C D) P)) A)   (build.associativity @-))
                   ((v A (v B (v (v C D) P)))   (build.commute-or @-))))

(defderiv build.disjoined-assoc-lemma-1
  :from   ((formula a A)
           (formula b B)
           (formula c C)
           (formula d D))
  :derive (v (! (v A D)) (v (v A B) (v C D)))
  :proof  (@derive ((v (! (v A D)) (v A D))               (build.propositional-schema (@formula (v A D))))
                   ((v A (v B (v (v C D) (! (v A D)))))   (build.disjoined-assoc-lemma-1a (@formula B) (@formula C) @-))
                   ((v (v A B) (v (v C D) (! (v A D))))   (build.associativity @-))
                   ((v (v (v A B) (v C D)) (! (v A D)))   (build.associativity @-))
                   ((v (! (v A D)) (v (v A B) (v C D)))   (build.commute-or @-))))

(defderiv build.disjoined-assoc-lemma-2a
  :from   ((formula a A)
           (formula d D)
           (proof x (v P (v B C))))
  :derive (v A (v B (v (v C D) P)))
  :proof  (@derive ((v P (v B C))              (@given x))
                   ((v (v P B) C)              (build.associativity @-))
                   ((v D (v (v P B) C))        (build.expansion (@formula D) @-))
                   ((v (v D (v P B)) C)        (build.associativity @-))
                   ((v C (v D (v P B)))        (build.commute-or @-))
                   ((v (v C D) (v P B))        (build.associativity @-))
                   ((v (v (v C D) P) B)        (build.associativity @-))
                   ((v B (v (v C D) P))        (build.commute-or @-))
                   ((v A (v B (v (v C D) P)))  (build.expansion (@formula A) @-))))

(defderiv build.disjoined-assoc-lemma-2
  :from   ((formula a A)
           (formula b B)
           (formula c C)
           (formula d D))
  :derive (v (! (v B C)) (v (v A B) (v C D)))
  :proof  (@derive ((v (! (v B C)) (v B C))               (build.propositional-schema (@formula (v B C))))
                   ((v A (v B (v (v C D) (! (v B C)))))   (build.disjoined-assoc-lemma-2a (@formula A) (@formula D) @-))
                   ((v (v A B) (v (v C D) (! (v B C))))   (build.associativity @-))
                   ((v (v (v A B) (v C D)) (! (v B C)))   (build.associativity @-))
                   ((v (! (v B C)) (v (v A B) (v C D)))   (build.commute-or @-))))

(defderiv build.disjoined-assoc-lemma-3a
  :from   ((formula a A)
           (formula b B)
           (formula c C)
           (formula d D))
  :derive (v (! (v (v A D) (v B C))) (v (v A B) (v C D)))
  :proof  (@derive ((v (! (v A D)) (v (v A B) (v C D)))              (build.disjoined-assoc-lemma-1 (@formula A) (@formula B) (@formula C) (@formula D)))
                   ((v (! (v B C)) (v (v A B) (v C D)))              (build.disjoined-assoc-lemma-2 (@formula A) (@formula B) (@formula C) (@formula D)))
                   ((v (! (v (v A D) (v B C))) (v (v A B) (v C D)))  (build.merge-implications @-- @-))))

(defderiv build.disjoined-assoc-lemma-3
  :from   ((proof x (v (v A D) (v B C))))
  :derive (v (v A B) (v C D))
  :proof  (@derive ((v (! (v (v A D) (v B C))) (v (v A B) (v C D)))  (build.disjoined-assoc-lemma-3a (@formula A) (@formula B) (@formula C) (@formula D)))
                   ((v (v A D) (v B C))                              (@given x))
                   ((v (v A B) (v C D))                              (build.modus-ponens @- @--))))

(defderiv build.disjoined-right-associativity
  :from   ((proof x (v P (v (v A B) C))))
  :derive (v P (v A (v B C)))
  :proof  (@derive ((v P (v (v A B) C))   (@given x))
                   ((v P (v C (v A B)))   (build.disjoined-commute-or @-))
                   ((v (v P C) (v A B))   (build.associativity @-))
                   ((v (v P A) (v B C))   (build.disjoined-assoc-lemma-3 @-))
                   ((v P (v A (v B C)))   (build.right-associativity @-))))


(defderiv build.disjoined-assoc-lemma-4
  :from   ((proof x (v (v P A) (v B C))))
  :derive (v (v P C) (v A B))
  :proof  (@derive ((v (v P A) (v B C))   (@given x))
                   ((v (v P A) (v C B))   (build.disjoined-commute-or @-))
                   ((v (v P C) (v B A))   (build.disjoined-assoc-lemma-3 @-))
                   ((v (v P C) (v A B))   (build.disjoined-commute-or @-))))

(defderiv build.disjoined-associativity
  :from   ((proof x (v P (v A (v B C)))))
  :derive (v P (v (v A B) C))
  :proof  (@derive ((v P (v A (v B C)))   (@given x))
                   ((v (v P A) (v B C))   (build.associativity @-))
                   ((v (v P C) (v A B))   (build.disjoined-assoc-lemma-4 @-))
                   ((v P (v C (v A B)))   (build.right-associativity @-))
                   ((v P (v (v A B) C))   (build.disjoined-commute-or @-))))

(defderiv build.disjoined-cut-lemma-1
  :from   ((proof x (v P (v A B)))
           (proof y (v P (v (! A) C))))
  :derive (v (v B P) (v C P))
  :proof  (@derive ((v P (v A B))         (@given x))
                   ((v (v A B) P)         (build.commute-or @-))
                   ((v A (v B P))         (build.right-associativity @-) *1)
                   ((v P (v (! A) C))     (@given y))
                   ((v (v (! A) C) P)     (build.commute-or @-))
                   ((v (! A) (v C P))     (build.right-associativity @-))
                   ((v (v B P) (v C P))   (build.cut *1 @-))))

(defderiv build.disjoined-cut-lemma-2
  :from   ((proof x (v P (v A B)))
           (proof y (v P (v (! A) C))))
  :derive (v (v B C) (v P P))
  :proof  (@derive
           ((v P (v A B))         (@given x))
           ((v P (v (! A) C))     (@given y))
           ((v (v B P) (v C P))   (build.disjoined-cut-lemma-1 @-- @-))
           ((v (v B C) (v P P))   (build.disjoined-assoc-lemma-3 @-))))

(defderiv build.disjoined-cut
  :from   ((proof x (v P (v A B)))
           (proof y (v P (v (! A) C))))
  :derive (v P (v B C))
  :proof  (@derive ((v P (v A B))         (@given x))
                   ((v P (v (! A) C))     (@given y))
                   ((v (v B C) (v P P))   (build.disjoined-cut-lemma-2 @-- @-))
                   ((v (v B C) P)         (build.disjoined-contraction @-))
                   ((v P (v B C))         (build.commute-or @-))))

(defderiv build.disjoined-modus-ponens
  :from   ((proof x (v P A))
           (proof y (v P (v (! A) B))))
  :derive (v P B)
  :proof  (@derive ((v P A)               (@given x))
                   ((v B (v P A))         (build.expansion (@formula B) @-))
                   ((v (v B P) A)         (build.associativity @-))
                   ((v A (v B P))         (build.commute-or @-) *1)
                   ((v P (v (! A) B))     (@given y))
                   ((v (v P (! A)) B)     (build.associativity @-))
                   ((v B (v P (! A)))     (build.commute-or @-))
                   ((v (v B P) (! A))     (build.associativity @-))
                   ((v (! A) (v B P))     (build.commute-or @-))
                   ((v (v B P) (v B P))   (build.cut *1 @-))
                   ((v B P)               (build.contraction @-))
                   ((v P B)               (build.commute-or @-))))

(defderiv build.disjoined-modus-ponens-2
  :from   ((proof x (v P (! A)))
           (proof y (v P (v A B))))
  :derive (v P B)
  :proof  (@derive ((v P (v A B))         (@given y))
                   ((v (v P A) B)         (build.associativity @-))
                   ((v B (v P A))         (build.commute-or @-))
                   ((v (v B P) A)         (build.associativity @-))
                   ((v A (v B P))         (build.commute-or @-)   *1)
                   ((v P (! A))           (@given x))
                   ((v B (v P (! A)))     (build.expansion (@formula B) @-))
                   ((v (v B P) (! A))     (build.associativity @-))
                   ((v (! A) (v B P))     (build.commute-or @-))
                   ((v (v B P) (v B P))   (build.cut *1 @-))
                   ((v B P)               (build.contraction @-))
                   ((v P B)               (build.commute-or @-))))




;; (defderiv build.first-negated-disjunct
;;   :from   ((proof x (! (v A B))))
;;   :derive (! A)
;;   :proof  (@derive ((v (! A) A)         (build.propositional-schema (@formula A)))
;;                    ((v B (v (! A) A))   (build.expansion (@formula B) @-))
;;                    ((v (v B (! A)) A)   (build.associativity @-))
;;                    ((v A (v B (! A)))   (build.commute-or @-))
;;                    ((v (v A B) (! A))   (build.associativity @-))
;;                    ((! (v A B))         (@given x))
;;                    ((! A)               (build.modus-ponens-2 @- @--))))

;; (defderiv build.second-negated-disjunct
;;   :from   ((proof x (! (v A B))))
;;   :derive (! B)
;;   :proof  (@derive ((v (! B) B)          (build.propositional-schema (@formula B)))
;;                    ((v B (! B))          (build.commute-or @-))
;;                    ((v A (v B (! B)))    (build.expansion (@formula A) @-))
;;                    ((v (v A B) (! B))    (build.associativity @-))
;;                    ((! (v A B))          (@given x))
;;                    ((! B)                (build.modus-ponens-2 @- @--))))

(dd.close)