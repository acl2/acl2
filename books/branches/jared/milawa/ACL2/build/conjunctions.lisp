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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "conjunctions.tex")

(dd.subsection "Conjunction rules")

(dd.write "These builders act as $\\wedge$ introduction and elimination rules.
We typically avoid using conjunctions and instead build both proofs separately
to avoid the conversion overhead.")

(defderiv build.conjoin
 :derive (! (v (! A) (! B)))
 :from   ((proof x A)
          (proof y B))
 :proof  (@derive ((v (! (v (! A) (! B))) (v (! A) (! B)))   (build.propositional-schema (@formula (v (! A) (! B)))))
                  ((v (v (! (v (! A) (! B))) (! A)) (! B))   (build.associativity @-))
                  ((v (! B) (v (! (v (! A) (! B))) (! A)))   (build.commute-or @-))
                  (B                                         (@given y))
                  ((v (! (v (! A) (! B))) (! A))             (build.modus-ponens @- @--))
                  ((v (! A) (! (v (! A) (! B))))             (build.commute-or @-))
                  (A                                         (@given x))
                  ((! (v (! A) (! B)))                       (build.modus-ponens @- @--))))

(defderiv build.first-conjunct
 :derive A
 :from   ((proof x (! (v (! A) (! B)))))
 :proof  (@derive ((v (! A) A)             (build.propositional-schema (@formula A)))
                  ((v A (! A))             (build.commute-or @-))
                  ((v (! B) (v A (! A)))   (build.expansion (@formula (! B)) @-))
                  ((v (v (! B) A) (! A))   (build.associativity @-))
                  ((v (! A) (v (! B) A))   (build.commute-or @-))
                  ((v (v (! A) (! B)) A)   (build.associativity @-))
                  ((! (v (! A) (! B)))     (@given x))
                  (A                       (build.modus-ponens-2 @- @--))))

(defderiv build.second-conjunct
 :derive B
 :from   ((proof x (! (v (! A) (! B)))))
 :proof  (@derive ((v (! B) B)             (build.propositional-schema (@formula B)))
                  ((v (! A) (v (! B) B))   (build.expansion (@formula (! A)) @-))
                  ((v (v (! A) (! B)) B)   (build.associativity @-))
                  ((! (v (! A) (! B)))     (@given x))
                  (B                       (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-conjoin
 :derive (v P (! (v (! A) (! B))))
 :from   ((proof x (v P A))
          (proof y (v P B)))
 :proof  (@derive ((v (! (v (! A) (! B))) (v (! A) (! B)))   (build.propositional-schema (@formula (v (! A) (! B)))))
                  ((v (v (! (v (! A) (! B))) (! A)) (! B))   (build.associativity @-))
                  ((v (! B) (v (! (v (! A) (! B))) (! A)))   (build.commute-or @-)  *1)
                  ((v P B)                                   (@given y))
                  ((v B P)                                   (build.commute-or @-))
                  ((v P (v (! (v (! A) (! B))) (! A)))       (build.cut @- *1))
                  ((v P (v (! A) (! (v (! A) (! B)))))       (build.disjoined-commute-or @-))
                  ((v P A)                                   (@given x))
                  ((v P (! (v (! A) (! B))))                 (build.disjoined-modus-ponens @- @--))))

(defderiv build.disjoined-first-conjunct
 :derive (v P A)
 :from   ((proof x (v P (! (v (! A) (! B))))))
 :proof  (@derive ((v (! A) A)                 (build.propositional-schema (@formula A)))
                  ((v A (! A))                 (build.commute-or @-))
                  ((v (! B) (v A (! A)))       (build.expansion (@formula (! B)) @-))
                  ((v (v (! B) A) (! A))       (build.associativity @-))
                  ((v (! A) (v (! B) A))       (build.commute-or @-))
                  ((v (v (! A) (! B)) A)       (build.associativity @-)                   *1)
                  ((v P (! (v (! A) (! B))))   (@given x))
                  ((v (! (v (! A) (! B))) P)   (build.commute-or @-))
                  ((v A P)                     (build.cut *1 @-))
                  ((v P A)                     (build.commute-or @-))))

(defderiv build.disjoined-second-conjunct
 :derive (v P B)
 :from   ((proof x (v P (! (v (! A) (! B))))))
 :proof  (@derive ((v (! B) B)                 (build.propositional-schema (@formula B)))
                  ((v (! A) (v (! B) B))       (build.expansion (@formula (! A)) @-))
                  ((v (v (! A) (! B)) B)       (build.associativity @-)                    *1)
                  ((v P (! (v (! A) (! B))))   (@given x))
                  ((v (! (v (! A) (! B))) P)   (build.commute-or @-))
                  ((v B P)                     (build.cut *1 @-))
                  ((v P B)                     (build.commute-or @-))))

(dd.close)