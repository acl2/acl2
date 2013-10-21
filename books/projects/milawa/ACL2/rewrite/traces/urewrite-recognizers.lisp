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
(include-book "tracep")
(include-book "../rulep")
(include-book "../../defderiv/defderiv")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund@ rw.urewrite-if-specialcase-same-tracep (x)
  ;;   (equiv b d) = t
  ;;   (equiv c d) = t
  ;; ----------------------------
  ;;   (equiv (if a b c) d) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'urewrite-if-specialcase-same)
         (equal (len subtraces) 2)
         (not (rw.hypbox->left hypbox))
         (not (rw.hypbox->right hypbox))
         (not (rw.hypbox->left (rw.trace->hypbox (first subtraces))))
         (not (rw.hypbox->right (rw.trace->hypbox (first subtraces))))
         (not (rw.hypbox->left (rw.trace->hypbox (second subtraces))))
         (not (rw.hypbox->right (rw.trace->hypbox (second subtraces))))
         (equal (rw.trace->iffp (first subtraces)) iffp)
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (@match (term (rw.trace->lhs (first subtraces)) (? b))
                 (term (rw.trace->rhs (first subtraces)) (? d))
                 (term (rw.trace->lhs (second subtraces)) (? c))
                 (term (rw.trace->rhs (second subtraces)) (? d))
                 (term lhs (if (? a) (? b) (? c)))
                 (term rhs (? d)))
         (not extras))))

(defthm booleanp-of-rw.urewrite-if-specialcase-same-tracep
  (equal (booleanp (rw.urewrite-if-specialcase-same-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.urewrite-if-specialcase-same-tracep)
                                 ((:executable-counterpart acl2::force))))))




(defund@ rw.urewrite-if-generalcase-tracep (x)
  ;;   (iff a1 a2) = t
  ;;   (equiv b1 b2) = t
  ;;   (equiv c1 c2) = t
  ;; -------------------------------------------
  ;;   (equiv (if a1 b1 c1) (if a2 b2 c2)) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox     (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'urewrite-if-generalcase)
         (equal (len subtraces) 3)
         (not (rw.hypbox->left hypbox))
         (not (rw.hypbox->right hypbox))
         (not (rw.hypbox->left (rw.trace->hypbox (first subtraces))))
         (not (rw.hypbox->right (rw.trace->hypbox (first subtraces))))
         (not (rw.hypbox->left (rw.trace->hypbox (second subtraces))))
         (not (rw.hypbox->right (rw.trace->hypbox (second subtraces))))
         (not (rw.hypbox->left (rw.trace->hypbox (third subtraces))))
         (not (rw.hypbox->right (rw.trace->hypbox (third subtraces))))
         (equal (rw.trace->iffp (first subtraces)) t)
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (equal (rw.trace->iffp (third subtraces)) iffp)
         (@match (term (rw.trace->lhs (first subtraces)) (? a1))
                 (term (rw.trace->rhs (first subtraces)) (? a2))
                 (term (rw.trace->lhs (second subtraces)) (? b1))
                 (term (rw.trace->rhs (second subtraces)) (? b2))
                 (term (rw.trace->lhs (third subtraces)) (? c1))
                 (term (rw.trace->rhs (third subtraces)) (? c2))
                 (term lhs (if (? a1) (? b1) (? c1)))
                 (term rhs (if (? a2) (? b2) (? c2))))
         (not extras))))

(defthm booleanp-of-rw.urewrite-if-generalcase-tracep
  (equal (booleanp (rw.urewrite-if-generalcase-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.urewrite-if-generalcase-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.urewrite-rule-tracep (x)
  ;;
  ;; ------------------------------   via some unconditional rewrite rule
  ;;   [hyps ->] (equiv x x') = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'urewrite-rule)
         (tuplep 2 extras)
         (let ((rule      (first extras))
               (sigma     (second extras)))
           (and (rw.rulep rule)
                (logic.sigmap sigma)
                (not (rw.rule->hyps rule))
                (let ((equiv (rw.rule->equiv rule)))
                  (or (equal equiv 'equal)
                      (and (equal equiv 'iff) iffp)))
                (let ((match-result (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                  (and (not (equal 'fail match-result))
                       (submapp match-result sigma)
                       (equal (logic.substitute (rw.rule->rhs rule) sigma) rhs)))
                (not subtraces))))))

(defthm booleanp-of-rw.urewrite-rule-tracep
  (equal (booleanp (rw.urewrite-rule-tracep x))
         t)
  :hints(("Goal" :in-theory (enable rw.urewrite-rule-tracep))))



(defund rw.urewrite-rule-trace-env-okp (x thms atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.urewrite-rule-tracep x)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable rw.urewrite-rule-tracep)))))
  (let* ((extras (rw.trace->extras x))
         (rule   (first extras))
         (sigma  (second extras)))
    (and (rw.rule-atblp rule atbl)
         (rw.rule-env-okp rule thms)
         (logic.sigma-atblp sigma atbl)
         )))

(defthm booleanp-of-rw.urewrite-rule-trace-env-okp
  (equal (booleanp (rw.urewrite-rule-trace-env-okp x thms atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.urewrite-rule-trace-env-okp))))

