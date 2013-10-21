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
(include-book "formulas")
(%interactive)

(%autoadmit logic.disjoin-formulas)

(defmacro %logic.disjoin-formulas-induction (x)
  `(%induct (rank ,x)
            ((or (not (consp ,x))
                 (not (consp (cdr ,x))))
             nil)
            ((and (consp ,x)
                  (consp (cdr ,x)))
             (((,x (cdr ,x)))))))

(defsection logic.disjoin-formulas-when-not-consp
  ;; BOZO add to acl2?  This lets us avoid many expand hints below
  (%prove (%rule logic.disjoin-formulas-when-not-consp
                 :hyps (list (%hyp (not (consp x))))
                 :lhs (logic.disjoin-formulas x)
                 :rhs nil))
  (local (%restrict default logic.disjoin-formulas (equal x 'x)))
  (%auto)
  (%qed)
  (%enable default logic.disjoin-formulas-when-not-consp))

(%autoprove logic.disjoin-formulas-when-singleton-list
            (%restrict default logic.disjoin-formulas (equal x 'x)))

(%autoprove logic.disjoin-formulas-of-cons-onto-consp
            (%restrict default logic.disjoin-formulas (equal x '(cons a x))))

(%autoprove logic.disjoin-formulas-of-list-fix
            (%logic.disjoin-formulas-induction x)
            (%disable default
                      forcing-logic.formulap-of-logic.por
                      aggressive-equal-of-logic.pors
                      forcing-equal-of-logic.por-rewrite
                      forcing-equal-of-logic.por-rewrite-two))

(%autoprove forcing-logic.formulap-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x)
            (%enable default logic.formulap-of-logic.por-expensive))

(%autoprove logic.formula-atblp-of-logic.por-expensive
            (%restrict default logic.formula-atblp (equal x '(logic.por x y))))

(%autoprove forcing-logic.formula-atblp-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x)
            (%enable default logic.formula-atblp-of-logic.por-expensive))

(%autoprove logic.formula-listp-when-logic.formulap-of-logic.disjoin-formulas-free)

(%autoprove logic.formula-list-atblp-when-logic.formula-atblp-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.fmtype-of-logic.disjoin-formulas
            (%logic.disjoin-formulas-induction x))

(%autoprove forcing-logic.vlhs-of-logic.disjoin-formulas)

(%autoprove forcing-logic.vrhs-of-logic.disjoin-formulas)

(%autoprove forcing-logic.fmtype-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.vlhs-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.vrhs-of-logic.disjoin-formulas-free)

(%autoprove forcing-logic.disjoin-formulas-of-two-element-list)

(%autoprove equal-of-logic.disjoin-formulas-and-logic.disjoin-formulas-when-same-len
            (%induct (rank x)
                     ((or (not (consp x))
                          (not (consp y))
                          (not (consp (cdr x)))
                          (not (consp (cdr y))))
                      nil)
                     ((and (consp x)
                           (consp (cdr x))
                           (consp y)
                           (consp (cdr y)))
                      (((x (cdr x))
                        (y (cdr y))))))
            ;; these cause loops after some rewriter changes.  taking them out.
            (%disable default
                      forcing-logic.fmtype-of-logic.disjoin-formulas-free
                      consp-of-cdr-with-len-free))

(encapsulate
 ()
 (local (%disable default EQUAL-OF-LOGIC.DISJOIN-FORMULAS-AND-LOGIC.DISJOIN-FORMULAS-WHEN-SAME-LEN))
 (%defprojection :list (logic.disjoin-each-formula-list x)
                 :element (logic.disjoin-formulas x)
                 :nil-preservingp t))

(%autoprove forcing-logic.formula-listp-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove forcing-logic.formula-list-atblp-of-logic.disjoin-each-formula-list
            (%cdr-induction x))

(%autoprove logic.disjoin-each-formula-list-of-listify-each
            (%cdr-induction x))

(%ensure-exactly-these-rules-are-missing "../../logic/disjoin-formulas")

