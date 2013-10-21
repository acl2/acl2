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
(include-book "worldp")
(include-book "skeletonp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; BOZO find us a home.

(defthm rw.theory-list-atblp-of-range-of-clean-update
  (implies (force (and (rw.theory-list-atblp (range theories) atbl)
                       (rw.theory-atblp val atbl)))
           (rw.theory-list-atblp (range (clean-update theoryname val theories)) atbl))
  :hints(("Goal"
          :induct (clean-update theoryname val theories)
          :in-theory (enable (:induction clean-update)))))

(defthm rw.theory-list-env-okp-of-range-of-clean-update
  (implies (force (and (rw.theory-list-env-okp (range theories) thms)
                       (rw.theory-env-okp val thms)))
           (rw.theory-list-env-okp (range (clean-update theoryname val theories)) thms))
  :hints(("Goal"
          :induct (clean-update theoryname val theories)
          :in-theory (enable (:induction clean-update)))))




(defund tactic.find-theory (name world)
  (declare (xargs :guard (tactic.worldp world)))
  (lookup name (tactic.world->theories world)))

(defthm rw.theoryp-of-tactic.find-theory
  (implies (force (tactic.worldp world))
           (equal (rw.theoryp (cdr (tactic.find-theory name world)))
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-theory))))

(defthm rw.theory-atblp-of-tactic.find-theory
  (implies (force (tactic.world-atblp world atbl))
           (equal (rw.theory-atblp (cdr (tactic.find-theory name world)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-theory))))

(defthm rw.theory-env-okp-of-tactic.find-theory
  (implies (force (tactic.world-env-okp world axioms thms))
           (equal (rw.theory-env-okp (cdr (tactic.find-theory name world)) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-theory))))



(defund tactic.find-rule (name world)
  (declare (xargs :guard (and (symbolp name)
                              (tactic.worldp world))))
  (rw.rule-list-lookup name (tactic.world->allrules world)))

(defthm rw.rulep-of-tactic.find-rule
  (implies (force (tactic.worldp world))
           (equal (rw.rulep (tactic.find-rule name world))
                  (if (tactic.find-rule name world)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable tactic.find-rule))))

(defthm rw.rule-atblp-of-tactic.find-rule
  (implies (force (tactic.world-atblp world atbl))
           (equal (rw.rule-atblp (tactic.find-rule name world) atbl)
                  (if (tactic.find-rule name world)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable tactic.find-rule))))

(defthm rw.rule-env-okp-of-tactic.find-rule
  (implies (and (force (tactic.find-rule name world))
                (force (tactic.world-env-okp world axioms thms)))
           (equal (rw.rule-env-okp (tactic.find-rule name world) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.find-rule))))



;; CREATING THEORIES

(defund tactic.create-theory (newtheoryname copyofname world)
  ;; Enables, Disables are collection specifiers
  ;; We enable all the rules indicated by enables, and remove all the rules indicated
  ;; by Disables, into the theory indicated by theoryname.
  (declare (xargs :guard (and (tactic.worldp world)
                              (symbolp newtheoryname)
                              (symbolp copyofname))))
  (let ((theory (tactic.find-theory newtheoryname world))
        (copy   (tactic.find-theory copyofname world)))
    (tactic.increment-world-index
     (if theory
         (ACL2::prog2$
          (ACL2::cw "Warning: theory ~s0 is already defined.  Not doing anything.~%")
          world)
       (change-tactic.world
        world
        :theories (clean-update newtheoryname
                                (ACL2::prog2$
                                 (if (and copyofname (not copy))
                                     (ACL2::cw "Warning: theory ~s0 is not defined; not importing anything.~%")
                                   nil)
                                 (cdr copy))
                                (tactic.world->theories world)))))))

(defthm tactic.worldp-of-tactic.create-theory
  (implies (force (and (tactic.worldp world)
                       (symbolp newtheoryname)
                       (symbolp copyofname)))
           (equal (tactic.worldp (tactic.create-theory newtheoryname copyofname world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory))))

(defthm tactic.worldp-atblp-of-tactic.create-theory
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (symbolp newtheoryname)
                       (symbolp copyofname)))
           (equal (tactic.world-atblp (tactic.create-theory newtheoryname copyofname world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory))))

(defthm tactic.world-env-okp-of-tactic.create-theory
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (symbolp newtheoryname)
                       (symbolp copyofname)))
           (equal (tactic.world-env-okp (tactic.create-theory newtheoryname copyofname world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory))))

(defthm tactic.world->index-of-tactic.create-theory
  (equal (tactic.world->index (tactic.create-theory newtheoryname copyofname world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.create-theory))))





(defund tactic.create-theory-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'create-theory)
         (equal goals (tactic.skeleton->goals history))
         (tuplep 2 extras)
         (symbolp (first extras))  ;; the newtheoryname
         (symbolp (second extras)) ;; the copyofname
         )))

(defthm booleanp-of-tactic.create-theory-okp
  (equal (booleanp (tactic.create-theory-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.create-theory-okp))))

(defthm tactic.skeleton->goals-when-tactic.create-theory-okp
  (implies (tactic.create-theory-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.create-theory-okp))))



(defund tactic.create-theory-tac (x newtheoryname copyofname)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp newtheoryname)
                              (symbolp copyofname))))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'create-theory
                          (list newtheoryname copyofname)
                          x))

(defthm tactic.skeletonp-of-tactic.create-theory-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.create-theory-tac x newtheoryname copyofname))
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory-tac))))

(defthm tactic.create-theory-okp-of-tactic.create-theory-tac
  (implies (force (and (tactic.skeletonp x)
                       (symbolp newtheoryname)
                       (symbolp copyofname)))
           (equal (tactic.create-theory-okp (tactic.create-theory-tac x newtheoryname copyofname))
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory-tac
                                    tactic.create-theory-okp))))



(defund tactic.create-theory-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.create-theory-okp x)
                              (tactic.worldp world))
                  :guard-hints(("Goal" :in-theory (enable tactic.create-theory-okp)))))
  (let ((extras (tactic.skeleton->extras x)))
    (tactic.create-theory (first extras)
                          (second extras)
                          world)))

(defthm tactic.worldp-of-tactic.create-theory-compile-world
  (implies (force (and (tactic.worldp world)
                       (tactic.create-theory-okp x)))
           (equal (tactic.worldp (tactic.create-theory-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory-compile-world
                                    tactic.create-theory-okp))))

(defthm tactic.world-atblp-of-tactic.create-theory-compile-world
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.create-theory-okp x)))
           (equal (tactic.world-atblp (tactic.create-theory-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory-compile-world
                                    tactic.create-theory-okp))))

(defthm tactic.world-env-okp-of-tactic.create-theory-compile-world
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.create-theory-okp x)))
           (equal (tactic.world-env-okp (tactic.create-theory-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.create-theory-compile-world
                                    tactic.create-theory-okp))))







;; ENABLING AND DISABLING RULES
;;
;; We specify the rules to add and remove using "collection specifiers".  Each
;; collection specifier is either:
;;
;;   - A plain symbol, which is interpreted as the name of a rule in allrules,
;;     or a theory in theories.  In effect, these share a namespace.
;;
;;   - (gather <CRITERIA>).  Here, we gather up all the rules in allrules which
;;     satisfy the criteria--a term that may involve the variables: name, type,
;;     equiv, lhs, rhs, hyps, syntax, and crithyps. For example, (equal name
;;     'booleanp-of-consp) will gather up all rules whose names are
;;     booleanp-of-consp from the implicit global scope.
;;
;;   - (gather from <THEORY> <CRITERIA>).  This is like (gather <CRITERIA>),
;;     except that instead of looking in allrules, we only look at the rules
;;     in the named theory.  For example,
;;
;;         (gather from default
;;           (equal (logic.function-name lhs) 'consp))
;;
;;     Will collect up all of the rules "about" consp in the DEFAULT theory,
;;     but will skip any rules about consp which aren't currently enabled in
;;     DEFAULT.

(defund tactic.collect-rules (x world acc)
  ;; X is a list of collection specifiers.  We add all of their rules to acc.
  (declare (xargs :guard (and (tactic.worldp world)
                              (rw.rule-listp acc)
                              (true-listp acc))
                  :verify-guards nil))
  (if (consp x)
      (cond ((symbolp (car x))
             (let ((theory (tactic.find-theory (car x) world)))
               (if theory
                   (tactic.collect-rules (cdr x) world (rw.fast-theory-all-rules (cdr theory) acc))
                 (let ((rule (tactic.find-rule (car x) world)))
                   (if rule
                       (tactic.collect-rules (cdr x) world (cons rule acc))
                     (ACL2::prog2$ (ACL2::er hard? 'tactic.collect-rules
                                             "~x0 is not the name of a defined rule or a theory.~%"
                                             (car x))
                                   acc))))))

            ((and (consp (car x))
                  (equal (first (car x)) 'gather))
             (let ((length (len (car x))))
               (cond ((not (or (equal length 2)
                               (and (equal (second (car x)) 'from)
                                    (equal length 4))))
                      (ACL2::prog2$
                       (ACL2::er hard? 'tactic.collect-rules "The valid forms are (gather <criteria>) and ~
                            (gather from <theoryname> <criteria>).  Hence, a call to gather ~
                            with with ~n0 arguments, such as ~x1, is invalid.~%" length (car x))
                       acc))

                      (t
                       (let* ((criteria       (if (equal length 2) (second (car x)) (fourth (car x))))
                              (criteria-trans (logic.translate criteria)))
                         (cond ((not (logic.termp criteria-trans))
                                (ACL2::prog2$
                                 (ACL2::er hard? 'tactic.collect-rules "We failed to translate the following <criteria> ~
                                     for (gather ...) into a term: ~x0.~%" criteria)
                                 acc))
                               ((not (subsetp (logic.term-vars criteria-trans) (rw.rule-components)))
                                (ACL2::prog2$
                                 (ACL2::er hard? 'tactic.collect-rules "The <criteria> for (gather ...) inappropriately ~
                                     mentions the variable(s) ~&0.  The only valid variables in <criteria> ~
                                     are ~&1.~%"
                                           (remove-duplicates (difference (logic.term-vars criteria-trans)
                                                                          (rw.rule-components)))
                                           (rw.rule-components))
                                 acc))
                               ((equal length 2)
                                (tactic.collect-rules (cdr x)
                                                      world
                                                      (rw.gather-rules-from-list (tactic.world->allrules world)
                                                                                 criteria-trans
                                                                                 (tactic.world->defs world)
                                                                                 acc)))
                               (t
                                (rw.gather-rules-from-theory (cdr (tactic.find-theory (third (car x)) world))
                                                             criteria-trans
                                                             (tactic.world->defs world)
                                                             acc))))))))
             (t
              (ACL2::prog2$
               (ACL2::er hard? 'tactic.collect-rules "Each collection specifier must be the name of a rule, ~
                  the name of a theory, or an appropriate (gather ...) command.  Hence, ~x0 is invalid.~%" (car x))
               acc)))
    acc))

(defthm true-listp-of-tactic.collect-rules
  (implies (force (true-listp acc))
           (equal (true-listp (tactic.collect-rules x world acc))
                  t))
  :hints(("Goal"
          :in-theory (enable tactic.collect-rules)
          :induct (tactic.collect-rules x world acc))))

(defthm rw.rule-listp-of-tactic.collect-rules
  (implies (force (and (tactic.worldp world)
                       (rw.rule-listp acc)
                       (true-listp acc)))
           (equal (rw.rule-listp (tactic.collect-rules x world acc))
                  t))
  :hints(("Goal" :in-theory (enable tactic.collect-rules))))

(defthm rw.rule-list-atblp-of-tactic.collect-rules
  (implies (force (and (tactic.world-atblp world atbl)
                       (rw.rule-list-atblp acc atbl)
                       (tactic.worldp world)
                       (rw.rule-listp acc)
                       (true-listp acc)))
           (equal (rw.rule-list-atblp (tactic.collect-rules x world acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.collect-rules))))

(defthm rw.rule-list-env-okp-of-tactic.collect-rules
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (rw.rule-list-env-okp acc thms)
                       (tactic.worldp world)
                       (rw.rule-listp acc)
                       (true-listp acc)))
           (equal (rw.rule-list-env-okp (tactic.collect-rules x world acc) thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.collect-rules))))

(verify-guards tactic.collect-rules)




(defund tactic.e/d (theoryname enables disables world)
  ;; Enables, Disables are collection specifiers
  ;; We enable all the rules indicated by enables, and remove all the rules indicated
  ;; by Disables, into the theory indicated by theoryname.
  (declare (xargs :guard (and (tactic.worldp world)
                              (symbolp theoryname))))
  (let ((theory (tactic.find-theory theoryname world)))
    (tactic.increment-world-index
     (if (not theory)
         (ACL2::prog2$
          (ACL2::cw "Warning: unknown theory ~x0.  Not enabling or disabling any rules.~%"
                    theoryname)
          world)
       (let ((erules (tactic.collect-rules enables world nil))
             (drules (tactic.collect-rules disables world nil)))
         (ACL2::prog2$
          (ACL2::cw (cond ((and (not erules)
                                (not drules))
                           "Warning: enable/disable with no rules specified.~%")
                          (erules
                           "Adding ~x1 rules to ~s0.~%")
                          (drules
                           "Removing ~x2 rules from ~s0.~%")
                          (t
                           "Adding ~x1 rules and removing ~x2 rules from ~s0.~%"))
                    theoryname
                    (len erules)
                    (len drules))
          (change-tactic.world world
                               :theories (clean-update
                                          theoryname
                                          (rw.theory-insert-list erules
                                           (rw.theory-delete-list drules (cdr theory)))
                                          (tactic.world->theories world)))))))))

(defthm tactic.worldp-of-tactic.e/d
  (implies (force (and (tactic.worldp world)
                       (symbolp theoryname)))
           (equal (tactic.worldp (tactic.e/d theoryname enables disables world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d))))


(defthm tactic.worldp-atblp-of-tactic.e/d
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (symbolp theoryname)))
           (equal (tactic.world-atblp (tactic.e/d theoryname enables disables world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d))))

(defthm tactic.world-env-okp-of-tactic.e/d
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)))
           (equal (tactic.world-env-okp (tactic.e/d theoryname enables disables world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d))))

(defthm tactic.world->index-of-tactic.e/d
  (equal (tactic.world->index (tactic.e/d theoryname enables disables world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.e/d))))






(defund tactic.e/d-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'e/d)
         (equal goals (tactic.skeleton->goals history))
         (tuplep 3 extras)
         (symbolp (first extras)) ;; the theoryname
         ;; (second extras) holds the enables
         ;; (third extras) holds the disables
         )))

(defthm booleanp-of-tactic.e/d-okp
  (equal (booleanp (tactic.e/d-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.e/d-okp))))

(defthm tactic.skeleton->goals-when-tactic.e/d-okp
  (implies (tactic.e/d-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.e/d-okp))))



(defund tactic.e/d-tac (x theoryname enables disables)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname))))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'e/d
                          (list theoryname enables disables)
                          x))

(defthm tactic.skeletonp-of-tactic.e/d-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.e/d-tac x theoryname enables disables))
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d-tac))))

(defthm tactic.e/d-okp-of-tactic.e/d-tac
  (implies (force (and (tactic.skeletonp x)
                       (symbolp theoryname)))
           (equal (tactic.e/d-okp (tactic.e/d-tac x theoryname enables disables))
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d-tac
                                    tactic.e/d-okp))))



(defund tactic.e/d-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.e/d-okp x)
                              (tactic.worldp world))
                  :guard-hints(("Goal" :in-theory (enable tactic.e/d-okp)))))
  (let ((extras (tactic.skeleton->extras x)))
    (tactic.e/d (first extras)
                (second extras)
                (third extras)
                world)))

(defthm tactic.worldp-of-tactic.e/d-compile-world
  (implies (force (and (tactic.worldp world)
                       (tactic.e/d-okp x)))
           (equal (tactic.worldp (tactic.e/d-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d-compile-world
                                    tactic.e/d-okp))))

(defthm tactic.world-atblp-of-tactic.e/d-compile-world
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.e/d-okp x)))
           (equal (tactic.world-atblp (tactic.e/d-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d-compile-world
                                    tactic.e/d-okp))))

(defthm tactic.world-env-okp-of-tactic.e/d-compile-world
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.e/d-okp x)))
           (equal (tactic.world-env-okp (tactic.e/d-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.e/d-compile-world
                                    tactic.e/d-okp))))





;; Adding additional syntactic restrictions to rules

(defund tactic.restrict (theoryname rulename syntax world)
  ;; The caller will want to translate syntax beforehand.
  (declare (xargs :guard (and (tactic.worldp world)
                              (symbolp theoryname)
                              (symbolp rulename)
                              (logic.term-listp syntax))))
  (let ((theory (tactic.find-theory theoryname world))
        (rule   (tactic.find-rule rulename world)))
    (tactic.increment-world-index
     (cond ((not theory)
            (ACL2::prog2$
             (ACL2::cw "Warning: unknown theory ~x0.  Not restricting anything.~%"
                       theoryname)
             world))
           ((not rule)
            (ACL2::prog2$
             (ACL2::cw "Warning: unknown rule ~x0.  Not restricting anything.~%"
                       theoryname)
             world))
           (t
            (let* ((new-rule (rw.rule (rw.rule->name rule)
                                      (rw.rule->type rule)
                                      (rw.rule->hyps rule)
                                      (rw.rule->equiv rule)
                                      (rw.rule->lhs rule)
                                      (rw.rule->rhs rule)
                                      (app syntax (rw.rule->syntax rule))
                                      (rw.rule->crithyps rule)))
                   (theory1  (rw.theory-delete rule (cdr theory)))
                   (theory2  (rw.theory-insert new-rule theory1)))
              (change-tactic.world world
                                   :theories (clean-update theoryname
                                                           theory2
                                                           (tactic.world->theories world)))))))))

(defthm tactic.worldp-of-tactic.restrict
  (implies (force (and (tactic.worldp world)
                       (symbolp theoryname)
                       (logic.term-listp syntax)))
           (equal (tactic.worldp (tactic.restrict theoryname rulename syntax world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict))))

(defthm tactic.worldp-atblp-of-tactic.restrict
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (symbolp theoryname)
                       (logic.term-listp syntax)))
           (equal (tactic.world-atblp (tactic.restrict theoryname rulename syntax world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict))))

(defthm lemma-for-tactic.world-env-okp-of-tactic.restrict
  (equal (rw.rule-env-okp (rw.rule (rw.rule->name rule)
                                   (rw.rule->type rule)
                                   (rw.rule->hyps rule)
                                   (rw.rule->equiv rule)
                                   (rw.rule->lhs rule)
                                   (rw.rule->rhs rule)
                                   (app restrictions (rw.rule->syntax rule))
                                   (rw.rule->crithyps rule))
                          thms)
         (rw.rule-env-okp rule thms))
  :hints(("Goal" :in-theory (enable rw.rule-env-okp
                                    rw.rule-clause))))

(defthm tactic.world-env-okp-of-tactic.restrict
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (symbolp theoryname)
                       (logic.term-listp syntax)))
           (equal (tactic.world-env-okp (tactic.restrict theoryname rulename syntax world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict))))

(defthm tactic.world->index-of-tactic.restrict
  (equal (tactic.world->index (tactic.restrict theoryname rulename syntax world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.restrict))))




(defund tactic.restrict-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'restrict)
         (equal goals (tactic.skeleton->goals history))
         (tuplep 3 extras)
         (symbolp (first extras)) ;; the theoryname
         (symbolp (second extras)) ;; the rulename
         (logic.term-listp (third extras)) ;; the restrictions
         )))

(defthm booleanp-of-tactic.restrict-okp
  (equal (booleanp (tactic.restrict-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.restrict-okp))))

(defthm tactic.skeleton->goals-when-tactic.restrict-okp
  (implies (tactic.restrict-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.restrict-okp))))



(defund tactic.restrict-tac (x theoryname rulename syntax)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname)
                              (symbolp rulename)
                              (logic.term-listp syntax))))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'restrict
                          (list theoryname rulename syntax)
                          x))

(defthm tactic.skeletonp-of-tactic.restrict-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.restrict-tac x theoryname rulename syntax))
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict-tac))))

(defthm tactic.restrict-okp-of-tactic.restrict-tac
  (implies (force (and (tactic.skeletonp x)
                       (symbolp theoryname)
                       (symbolp rulename)
                       (logic.term-listp syntax)))
           (equal (tactic.restrict-okp (tactic.restrict-tac x theoryname rulename syntax))
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict-tac
                                    tactic.restrict-okp))))



(defund tactic.restrict-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.restrict-okp x)
                              (tactic.worldp world))
                  :guard-hints(("Goal" :in-theory (enable tactic.restrict-okp)))))
  (let ((extras (tactic.skeleton->extras x)))
    (tactic.restrict (first extras)
                (second extras)
                (third extras)
                world)))

(defthm tactic.worldp-of-tactic.restrict-compile-world
  (implies (force (and (tactic.worldp world)
                       (tactic.restrict-okp x)))
           (equal (tactic.worldp (tactic.restrict-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict-compile-world
                                    tactic.restrict-okp))))

(defthm tactic.world-atblp-of-tactic.restrict-compile-world
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.restrict-okp x)))
           (equal (tactic.world-atblp (tactic.restrict-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict-compile-world
                                    tactic.restrict-okp))))

(defthm tactic.world-env-okp-of-tactic.restrict-compile-world
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.restrict-okp x)))
           (equal (tactic.world-env-okp (tactic.restrict-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.restrict-compile-world
                                    tactic.restrict-okp))))







;; Managing the noexec list

(defund tactic.update-noexec (add rem world)
  (declare (xargs :guard (and (tactic.worldp world)
                              (logic.function-symbol-listp add)
                              (logic.function-symbol-listp rem))))
  (let* ((old-list (tactic.world->noexec world))
         (new-list (fast-app add (difference old-list rem))))
    (tactic.increment-world-index
     (change-tactic.world world
                          :noexec new-list))))

(defthm tactic.worldp-of-tactic.update-noexec
  (implies (force (and (tactic.worldp world)
                       (logic.function-symbol-listp add)
                       (logic.function-symbol-listp rem)))
           (equal (tactic.worldp (tactic.update-noexec add rem world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec))))

(defthm tactic.worldp-atblp-of-tactic.update-noexec
  (implies (force (and (tactic.world-atblp world atbl)
                       (logic.function-symbol-listp add)
                       (logic.function-symbol-listp rem)))
           (equal (tactic.world-atblp (tactic.update-noexec add rem world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec))))

(defthm tactic.world-env-okp-of-tactic.update-noexec
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (logic.function-symbol-listp add)
                       (logic.function-symbol-listp rem)))
           (equal (tactic.world-env-okp (tactic.update-noexec add rem world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec))))

(defthm tactic.world->index-of-tactic.update-noexec
  (equal (tactic.world->index (tactic.update-noexec add rem world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.update-noexec))))



(defund tactic.update-noexec-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'update-noexec)
         (equal goals (tactic.skeleton->goals history))
         (tuplep 2 extras)
         (logic.function-symbol-listp (first extras)) ;; the add list
         (logic.function-symbol-listp (second extras)) ;; the rem list
         )))

(defthm booleanp-of-tactic.update-noexec-okp
  (equal (booleanp (tactic.update-noexec-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.update-noexec-okp))))

(defthm tactic.skeleton->goals-when-tactic.update-noexec-okp
  (implies (tactic.update-noexec-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-okp))))



(defund tactic.update-noexec-tac (x add rem)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (logic.function-symbol-listp add)
                              (logic.function-symbol-listp rem))))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'update-noexec
                          (list add rem)
                          x))

(defthm tactic.skeletonp-of-tactic.update-noexec-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.update-noexec-tac x add rem))
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-tac))))

(defthm tactic.update-noexec-okp-of-tactic.update-noexec-tac
  (implies (force (and (tactic.skeletonp x)
                       (logic.function-symbol-listp add)
                       (logic.function-symbol-listp rem)))
           (equal (tactic.update-noexec-okp (tactic.update-noexec-tac x add rem))
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-tac
                                    tactic.update-noexec-okp))))



(defund tactic.update-noexec-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.update-noexec-okp x)
                              (tactic.worldp world))
                  :guard-hints(("Goal" :in-theory (enable tactic.update-noexec-okp)))))
  (let ((extras (tactic.skeleton->extras x)))
    (tactic.update-noexec (first extras)
                          (second extras)
                          world)))

(defthm tactic.worldp-of-tactic.update-noexec-compile-world
  (implies (force (and (tactic.worldp world)
                       (tactic.update-noexec-okp x)))
           (equal (tactic.worldp (tactic.update-noexec-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-compile-world
                                    tactic.update-noexec-okp))))

(defthm tactic.world-atblp-of-tactic.update-noexec-compile-world
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.update-noexec-okp x)))
           (equal (tactic.world-atblp (tactic.update-noexec-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-compile-world
                                    tactic.update-noexec-okp))))

(defthm tactic.world-env-okp-of-tactic.update-noexec-compile-world
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.update-noexec-okp x)))
           (equal (tactic.world-env-okp (tactic.update-noexec-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.update-noexec-compile-world
                                    tactic.update-noexec-okp))))





(defund tactic.cheapen-each-hyp (hyps)
  (declare (xargs :guard (rw.hyp-listp hyps)))
  (if (consp hyps)
      (cons (rw.hyp (rw.hyp->term (car hyps))
                    (rw.hyp->fmode (car hyps))
                    t
                    0)
            (tactic.cheapen-each-hyp (cdr hyps)))
    nil))

(defthm rw.hyp-list-terms-of-tactic.cheapen-each-hyp
  (equal (rw.hyp-list-terms (tactic.cheapen-each-hyp hyps))
         (rw.hyp-list-terms hyps))
  :hints(("Goal" :in-theory (enable tactic.cheapen-each-hyp))))

(defthm forcing-rw.hyp-listp-of-tactic.cheapen-each-hyp
  (implies (force (rw.hyp-listp hyps))
           (equal (rw.hyp-listp (tactic.cheapen-each-hyp hyps))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-each-hyp))))

(defthm forcing-rw.hyp-list-atblp-of-tactic.cheapen-each-hyp
  (implies (force (rw.hyp-list-atblp hyps atbl))
           (equal (rw.hyp-list-atblp (tactic.cheapen-each-hyp hyps) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-each-hyp))))



(defund tactic.cheapen-rule (rule)
  (declare (xargs :guard (rw.rulep rule)))
  (rw.rule (rw.rule->name rule)
           (rw.rule->type rule)
           (tactic.cheapen-each-hyp (rw.rule->hyps rule))
           (rw.rule->equiv rule)
           (rw.rule->lhs rule)
           (rw.rule->rhs rule)
           (rw.rule->syntax rule)
           (rw.rule->crithyps rule)))

(defthm rw.rulep-of-tactic.cheapen-rule
  (implies (force (rw.rulep rule))
           (rw.rulep (tactic.cheapen-rule rule)))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rule))))

(defthm rw.rule-atblp-of-tactic.cheapen-rule
  (implies (force (and (rw.rule-atblp rule atbl)
                       (rw.rulep rule)))
           (rw.rule-atblp (tactic.cheapen-rule rule) atbl))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rule))))

(defthm rw.rule-env-okp-of-tactic.cheapen-rule
  (implies (force (rw.rule-env-okp rule thms))
           (rw.rule-env-okp (tactic.cheapen-rule rule) thms))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rule
                                    rw.rule-env-okp
                                    rw.rule-clause))))


(defun tactic.cheapen-rules (rules)
  (declare (xargs :guard (rw.rule-listp rules)))
  (if (consp rules)
      (cons (tactic.cheapen-rule (car rules))
            (tactic.cheapen-rules (cdr rules)))
    nil))

(defthm rw.rule-listp-of-tactic.cheapen-rules
  (implies (force (rw.rule-listp rules))
           (rw.rule-listp (tactic.cheapen-rules rules)))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rules))))

(defthm rw.rule-list-atblp-of-tactic.cheapen-rules
  (implies (force (and (rw.rule-list-atblp rules atbl)
                       (rw.rule-listp rules)))
           (rw.rule-list-atblp (tactic.cheapen-rules rules) atbl))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rules))))

(defthm rw.rule-list-env-okp-of-tactic.cheapen-rules
  (implies (force (rw.rule-list-env-okp rules thms))
           (rw.rule-list-env-okp (tactic.cheapen-rules rules) thms))
  :hints(("Goal" :in-theory (enable tactic.cheapen-rules))))



(defund tactic.cheapen (theoryname what world)
  ;; Enables, Disables are collection specifiers
  ;; We enable all the rules indicated by enables, and remove all the rules indicated
  ;; by Disables, into the theory indicated by theoryname.
  (declare (xargs :guard (and (tactic.worldp world)
                              (symbolp theoryname))))
  (let ((theory (tactic.find-theory theoryname world)))
    (tactic.increment-world-index
     (if (not theory)
         (ACL2::prog2$
          (ACL2::cw "Warning: unknown theory ~x0.  Not cheapening any rules.~%"
                    theoryname)
          world)
       (let* ((rules     (tactic.collect-rules what world nil))
              (cheapened (tactic.cheapen-rules rules))
              (removed   (rw.theory-delete-list rules (cdr theory)))
              (added     (rw.theory-insert-list cheapened removed)))
         (ACL2::prog2$
          (ACL2::cw (cond ((not rules)
                           "Warning: not cheapening any rules.~%")
                          (t
                           "Cheapening ~x1 rules in ~s0.~%"))
                    theoryname
                    (len rules))
          (change-tactic.world world
                               :theories (clean-update
                                          theoryname
                                          added
                                          (tactic.world->theories world)))))))))

(defthm tactic.worldp-of-tactic.cheapen
  (implies (force (and (tactic.worldp world)
                       (symbolp theoryname)))
           (equal (tactic.worldp (tactic.cheapen theoryname what world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen))))

(defthm tactic.worldp-atblp-of-tactic.cheapen
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (symbolp theoryname)))
           (equal (tactic.world-atblp (tactic.cheapen theoryname what world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen))))

(defthm tactic.world-env-okp-of-tactic.cheapen
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)))
           (equal (tactic.world-env-okp (tactic.cheapen theoryname what world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen))))

(defthm tactic.world->index-of-tactic.cheapen
  (equal (tactic.world->index (tactic.cheapen theoryname what world))
         (+ 1 (tactic.world->index world)))
  :hints(("Goal" :in-theory (enable tactic.cheapen))))






(defund tactic.cheapen-okp (x)
  (declare (xargs :guard (tactic.skeletonp x)))
  (let ((goals   (tactic.skeleton->goals x))
        (tacname (tactic.skeleton->tacname x))
        (extras  (tactic.skeleton->extras x))
        (history (tactic.skeleton->history x)))
    (and (equal tacname 'cheapen)
         (equal goals (tactic.skeleton->goals history))
         (tuplep 2 extras)
         (symbolp (first extras)) ;; the theoryname
         ;; (second extras) holds the what
         )))

(defthm booleanp-of-tactic.cheapen-okp
  (equal (booleanp (tactic.cheapen-okp x))
         t)
  :hints(("Goal" :in-theory (enable tactic.cheapen-okp))))

(defthm tactic.skeleton->goals-when-tactic.cheapen-okp
  (implies (tactic.cheapen-okp x)
           (equal (tactic.skeleton->goals x)
                  (tactic.skeleton->goals (tactic.skeleton->history x))))
  :hints(("Goal" :in-theory (enable tactic.cheapen-okp))))



(defund tactic.cheapen-tac (x theoryname what)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (symbolp theoryname))))
  (tactic.extend-skeleton (tactic.skeleton->goals x)
                          'cheapen
                          (list theoryname what)
                          x))

(defthm tactic.skeletonp-of-tactic.cheapen-tac
  (implies (force (tactic.skeletonp x))
           (equal (tactic.skeletonp (tactic.cheapen-tac x theoryname what))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-tac))))

(defthm tactic.cheapen-okp-of-tactic.cheapen-tac
  (implies (force (and (tactic.skeletonp x)
                       (symbolp theoryname)))
           (equal (tactic.cheapen-okp (tactic.cheapen-tac x theoryname what))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-tac
                                    tactic.cheapen-okp))))

(defund tactic.cheapen-compile-world (x world)
  (declare (xargs :guard (and (tactic.skeletonp x)
                              (tactic.cheapen-okp x)
                              (tactic.worldp world))
                  :guard-hints(("Goal" :in-theory (enable tactic.cheapen-okp)))))
  (let ((extras (tactic.skeleton->extras x)))
    (tactic.cheapen (first extras)
                    (second extras)
                    world)))

(defthm tactic.worldp-of-tactic.cheapen-compile-world
  (implies (force (and (tactic.worldp world)
                       (tactic.cheapen-okp x)))
           (equal (tactic.worldp (tactic.cheapen-compile-world x world))
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-compile-world
                                    tactic.cheapen-okp))))

(defthm tactic.world-atblp-of-tactic.cheapen-compile-world
  (implies (force (and (tactic.world-atblp world atbl)
                       (tactic.worldp world)
                       (tactic.cheapen-okp x)))
           (equal (tactic.world-atblp (tactic.cheapen-compile-world x world) atbl)
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-compile-world
                                    tactic.cheapen-okp))))

(defthm tactic.world-env-okp-of-tactic.cheapen-compile-world
  (implies (force (and (tactic.world-env-okp world axioms thms)
                       (tactic.worldp world)
                       (tactic.cheapen-okp x)))
           (equal (tactic.world-env-okp (tactic.cheapen-compile-world x world) axioms thms)
                  t))
  :hints(("Goal" :in-theory (enable tactic.cheapen-compile-world
                                    tactic.cheapen-okp))))

