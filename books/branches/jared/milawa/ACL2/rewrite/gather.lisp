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
(include-book "theoryp")
(include-book "evaluator")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defun rw.rule-components ()
  (declare (xargs :guard t))
  '(name type hyps equiv lhs rhs syntax crithyps))

(defund rw.consider-rule (rule criteria defs)
  ;; A generally useful thing to be able to do is ask, "does this rule fit some
  ;; certain criteria?"  There might be good reasons to ask all kinds of things
  ;; about a rule -- does it have a certain name, does it have an "if" on the
  ;; right-hand side, does it have any free variables, does etc.  Rather than
  ;; try to write a separate function to answer each of these questions, we
  ;; allow you to specify an arbitrary term as a CRITERIA.
  ;;
  ;; The criteria can include variables for each of the rule's components.
  ;; That is, it can mention: name, type, hyps, equiv, lhs, rhs, syntax, and
  ;; crithyps.  We'll substitute the quoted name, type, etc., from the rule in
  ;; for these variables before evaluating the term.  So for example, to match
  ;; a rule whose name is FOO, you can use the criteria (equal name 'FOO); to
  ;; match a rule whose lhs is (foo x y), use (equal lhs '(foo x y)); and so
  ;; forth.
  (declare (xargs :guard (and (rw.rulep rule)
                              (logic.termp criteria)
                              (subsetp (logic.term-vars criteria) (rw.rule-components))
                              (definition-listp defs))))
  (not (equal (generic-evaluator (logic.substitute criteria
                                                   (list (cons 'name (list 'quote (rw.rule->name rule)))
                                                         (cons 'type (list 'quote (rw.rule->type rule)))
                                                         (cons 'hyps (list 'quote (rw.rule->hyps rule)))
                                                         (cons 'equiv (list 'quote (rw.rule->equiv rule)))
                                                         (cons 'lhs (list 'quote (rw.rule->lhs rule)))
                                                         (cons 'rhs (list 'quote (rw.rule->rhs rule)))
                                                         (cons 'syntax (list 'quote (rw.rule->syntax rule)))
                                                         (cons 'crithyps (list 'quote (rw.rule->crithyps rule)))))
                                 defs
                                 200)
              ''nil)))

(defthm booleanp-of-rw.consider-rule
  (equal (booleanp (rw.consider-rule rule criteria defs))
         t)
  :hints(("Goal" :in-theory (enable rw.consider-rule))))



(defund rw.gather-rules-from-list (rules criteria defs acc)
  ;; We collect up all the rules that match the given criteria.  See
  ;; rw.consider-rule for more details about what valid criteria are like.
  (declare (xargs :guard (and (rw.rule-listp rules)
                              (logic.termp criteria)
                              (subsetp (logic.term-vars criteria) (rw.rule-components))
                              (definition-listp defs)
                              (rw.rule-listp acc))))
  (if (consp rules)
      (rw.gather-rules-from-list (cdr rules) criteria defs
                                 (if (rw.consider-rule (car rules) criteria defs)
                                     (cons (car rules) acc)
                                   acc))
    acc))

(defthm true-listp-of-rw.gather-rules-from-list
  (equal (true-listp (rw.gather-rules-from-list rules criteria defs acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-list))))

(defthm forcing-rw.rule-listp-of-rw.gather-rules-from-list
  (implies (force (and (rw.rule-listp rules)
                       (rw.rule-listp acc)))
           (equal (rw.rule-listp (rw.gather-rules-from-list rules criteria defs acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-list))))

(defthm forcing-rw.rule-list-atblp-of-rw.gather-rules-from-list
  (implies (force (and (rw.rule-list-atblp rules atbl)
                       (rw.rule-list-atblp acc atbl)))
           (equal (rw.rule-list-atblp (rw.gather-rules-from-list rules criteria defs acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-list))))

(defthm forcing-rw.rule-list-env-okp-of-rw.gather-rules-from-list
  (implies (force (and (rw.rule-list-env-okp rules thms)
                       (rw.rule-list-env-okp acc thms)))
           (equal (rw.rule-list-env-okp (rw.gather-rules-from-list rules criteria defs acc) thms)
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-list))))



(defund rw.gather-rules-from-map (rulemap criteria defs acc)
  ;; We collect up all the rules that match the given criteria.  See
  ;; rw.consider-rule for more details about what valid criteria are like.
  (declare (xargs :guard (and (rw.typed-rulemapp rulemap)
                              (logic.termp criteria)
                              (subsetp (logic.term-vars criteria) (rw.rule-components))
                              (definition-listp defs)
                              (rw.rule-listp acc))))
  (if (consp rulemap)
      (rw.gather-rules-from-map (cdr rulemap) criteria defs
                                (rw.gather-rules-from-list (cdr (car rulemap)) criteria defs acc))
    acc))

(defthm true-listp-of-rw.gather-rules-from-map
  (equal (true-listp (rw.gather-rules-from-map rulemap criteria defs acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-map))))

(defthm rw.rule-listp-of-rw.gather-rules-from-map
  (implies (force (and (rw.typed-rulemapp rulemap)
                       (rw.rule-listp acc)))
           (equal (rw.rule-listp (rw.gather-rules-from-map rulemap criteria defs acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-map))))

(defthm rw.rule-list-atblp-of-rw.gather-rules-from-map
  (implies (force (and (rw.rule-list-list-atblp (range rulemap) atbl)
                       (rw.rule-list-atblp acc atbl)
                       (rw.typed-rulemapp rulemap)
                       (rw.rule-listp acc)))
           (equal (rw.rule-list-atblp (rw.gather-rules-from-map rulemap criteria defs acc) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-map))))

(defthm rw.rule-list-env-okp-of-rw.gather-rules-from-map
  (implies (force (and (rw.rule-list-list-env-okp (range rulemap) thms)
                       (rw.rule-list-env-okp acc thms)
                       (rw.typed-rulemapp rulemap)
                       (rw.rule-listp acc)))
           (equal (rw.rule-list-env-okp (rw.gather-rules-from-map rulemap criteria defs acc) thms)
                  t))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-map))))



(defund rw.gather-rules-from-theory (theory criteria defs acc)
  ;; We keep all the rules that match the given criteria.  See rw.consider-rule
  ;; for more details about what valid criteria look like.
  (declare (xargs :guard (and (rw.theoryp theory)
                              (logic.termp criteria)
                              (subsetp (logic.term-vars criteria) (rw.rule-components))
                              (definition-listp defs)
                              (rw.rule-listp acc))
                  :verify-guards nil))
  (if (consp theory)
      (rw.gather-rules-from-theory (rw.theory->left theory) criteria defs
       (rw.gather-rules-from-theory (rw.theory->right theory) criteria defs
        (rw.gather-rules-from-map (rw.theory->rulemap theory) criteria defs acc)))
    acc))

(defthm true-listp-of-rw.gather-rules-from-theory
  (equal (true-listp (rw.gather-rules-from-theory theory criteria defs acc))
         (true-listp acc))
  :hints(("Goal" :in-theory (enable rw.gather-rules-from-theory))))

(defthm rw.rule-listp-of-rw.gather-rules-from-theory
   (implies (force (and (rw.theoryp theory)
                        (rw.rule-listp acc)))
            (equal (rw.rule-listp (rw.gather-rules-from-theory theory criteria defs acc))
                   t))
   :hints(("Goal" :in-theory (enable rw.gather-rules-from-theory))))

(verify-guards rw.gather-rules-from-theory)

(defthm rw.rule-list-atblp-of-rw.gather-rules-from-theory
  (implies (force (and (rw.theory-atblp theory atbl)
                       (rw.rule-list-atblp acc atbl)
                       (rw.theoryp theory)
                       (rw.rule-listp acc)))
            (equal (rw.rule-list-atblp (rw.gather-rules-from-theory theory criteria defs acc) atbl)
                   t))
 :hints(("Goal" :in-theory (enable rw.gather-rules-from-theory))))

(defthm rw.rule-list-env-okp-of-rw.gather-rules-from-theory
  (implies (force (and (rw.theory-env-okp theory thms)
                       (rw.rule-list-env-okp acc thms)
                       (rw.theoryp theory)
                       (rw.rule-listp acc)))
            (equal (rw.rule-list-env-okp (rw.gather-rules-from-theory theory criteria defs acc) thms)
                   t))
 :hints(("Goal" :in-theory (enable rw.gather-rules-from-theory))))

