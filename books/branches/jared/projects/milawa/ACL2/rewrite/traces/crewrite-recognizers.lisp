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
(include-book "../../defderiv/context")
(include-book "../assms/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund@ rw.crewrite-if-specialcase-same-tracep (x)
  ;; The idea here is:
  ;;
  ;;   hyps --> (iff a1 a2) = t
  ;;   [a2, hyps] --> (equiv b d) = t
  ;;   [~a2, hyps] --> (equiv c d) = t
  ;; ---------------------------------------
  ;;   hyps --> (equiv (if a1 b c) d) = t
  ;;
  ;; We want to add a2 and ~a2 to hyps for the subtraces.  But our traces store
  ;; nhyps, not hyps, so we actually want to do something like this:
  ;;
  ;;   nhyps v (iff a1 a2) = t
  ;;   [(not a2), nhyps] v (equiv b d) = t
  ;;   [a2, nhyps] v (equiv c d) = t
  ;; ---------------------------------------
  ;;   nhyps v (equiv (if a1 b c) d) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'crewrite-if-specialcase-same)
         (equal (len subtraces) 3)
         (equal (rw.trace->iffp (first subtraces)) t)
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (equal (rw.trace->iffp (third subtraces)) iffp)
         (@match (term lhs (if (? a1) (? b) (? c)))
                 (term rhs (? d))
                 (term (rw.trace->lhs (first subtraces)) (? a1))
                 (term (rw.trace->rhs (first subtraces)) (? a2))
                 (term (rw.trace->lhs (second subtraces)) (? b))
                 (term (rw.trace->rhs (second subtraces)) (? d))
                 (term (rw.trace->lhs (third subtraces)) (? c))
                 (term (rw.trace->rhs (third subtraces)) (? d)))
         (equal (rw.trace->hypbox (first subtraces)) hypbox)
         (equal (rw.hypbox->left (rw.trace->hypbox (second subtraces)))
                (cons (logic.function 'not (list (@term (? a2))))
                      (rw.hypbox->left hypbox)))
         (equal (rw.hypbox->left (rw.trace->hypbox (third subtraces)))
                (cons (@term (? a2))
                      (rw.hypbox->left hypbox)))
         (equal (rw.hypbox->right (rw.trace->hypbox (second subtraces)))
                (rw.hypbox->right hypbox))
         (equal (rw.hypbox->right (rw.trace->hypbox (third subtraces)))
                (rw.hypbox->right hypbox))
         (not extras))))

(defthm booleanp-of-rw.crewrite-if-specialcase-same-tracep
  (equal (booleanp (rw.crewrite-if-specialcase-same-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.crewrite-if-specialcase-same-tracep)
                                 ((:executable-counterpart ACL2::force))))))



(defund@ rw.crewrite-if-generalcase-tracep (x)
  ;; The idea here is:
  ;;
  ;;   hyps --> (iff a1 a2) = t
  ;;   [a2, hyps] --> (equiv b1 b2) = t
  ;;   [~a2, hyps] --> (equiv c1 c2) = t
  ;; ----------------------------------------------------
  ;;   hyps --> (equiv (if a1 b1 c1) (if a2 b2 c2)) = t
  ;;
  ;; As above we actually deal with nhyps, so this is:
  ;;
  ;;   nhyps v (iff a1 a2) = t
  ;;   [(not a2), nhyps] v (equiv b1 b2) = t
  ;;   [a2, nhyps] v (equiv c1 c2) = t
  ;; ---------------------------------------------------
  ;;   nhyps v (equiv (if a1 b1 c1) (if a2 b2 c2)) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'crewrite-if-generalcase)
         (equal (len subtraces) 3)
         (equal (rw.trace->iffp (first subtraces)) t)
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (equal (rw.trace->iffp (third subtraces)) iffp)
         (@match (term lhs (if (? a1) (? b1) (? c1)))
                 (term rhs (if (? a2) (? b2) (? c2)))
                 (term (rw.trace->lhs (first subtraces)) (? a1))
                 (term (rw.trace->rhs (first subtraces)) (? a2))
                 (term (rw.trace->lhs (second subtraces)) (? b1))
                 (term (rw.trace->rhs (second subtraces)) (? b2))
                 (term (rw.trace->lhs (third subtraces)) (? c1))
                 (term (rw.trace->rhs (third subtraces)) (? c2)))
         (equal (rw.trace->hypbox (first subtraces)) hypbox)
         (equal (rw.hypbox->left (rw.trace->hypbox (second subtraces)))
                (cons (logic.function 'not (list (@term (? a2))))
                      (rw.hypbox->left hypbox)))
         (equal (rw.hypbox->left (rw.trace->hypbox (third subtraces)))
                (cons (@term (? a2))
                      (rw.hypbox->left hypbox)))
         (equal (rw.hypbox->right (rw.trace->hypbox (second subtraces)))
                (rw.hypbox->right hypbox))
         (equal (rw.hypbox->right (rw.trace->hypbox (third subtraces)))
                (rw.hypbox->right hypbox))
         (not extras))))

(defthm booleanp-of-rw.crewrite-if-generalcase-tracep
  (equal (booleanp (rw.crewrite-if-generalcase-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.crewrite-if-generalcase-tracep)
                                 ((:executable-counterpart ACL2::force))))))




(defund rw.crewrite-rule-tracep (x)
  ;;   [hyps ->] (iff rule-hyp1 t) = t
  ;;   ...
  ;;   [hyps ->] (iff rule-hypN t) = t
  ;; ---------------------------------------------  as justified by some rule
  ;;   [hyps ->] (equiv lhs/sigma rhs/sigma) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'crewrite-rule)
         (tuplep 2 extras)
         (let ((rule      (first extras))
               (sigma     (second extras)))
           (and (rw.rulep rule)
                (logic.sigmap sigma)
                ;; Check that the equivalence relation is acceptable
                (let ((equiv (rw.rule->equiv rule)))
                  (or (equal equiv 'equal)
                      (and (equal equiv 'iff) iffp)))
                ;; Check that the LHS matches and that the RHS is correctly instantiated
                (let* ((match-result (logic.patmatch (rw.rule->lhs rule) lhs nil)))
                  (and (not (equal match-result 'fail))
                       (submapp match-result sigma)
                       (equal (logic.substitute (rw.rule->rhs rule) sigma) rhs)))
                ;; Check that all the hyps are relieved under iff.
                (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
                (all-equalp t (rw.trace-list-iffps subtraces))
                (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                       (rw.trace-list-lhses subtraces))
                (all-equalp ''t (rw.trace-list-rhses subtraces)))))))

(defthm booleanp-of-rw.crewrite-rule-tracep
  (equal (booleanp (rw.crewrite-rule-tracep x))
         t)
  :hints(("Goal" :in-theory (enable rw.crewrite-rule-tracep))))




(defund rw.crewrite-rule-trace-env-okp (x thms atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.crewrite-rule-tracep x)
                              (logic.formula-listp thms)
                              (logic.arity-tablep atbl))
                  :guard-hints (("Goal" :in-theory (enable rw.crewrite-rule-tracep)))))
  (let* ((extras (rw.trace->extras x))
         (rule   (first extras))
         (sigma  (second extras)))
    (and (rw.rule-atblp rule atbl)
         (rw.rule-env-okp rule thms)
         (logic.sigma-atblp sigma atbl))))

(defthm booleanp-of-rw.crewrite-rule-trace-env-okp
  (equal (booleanp (rw.crewrite-rule-trace-env-okp x thms atbl))
         t)
  :hints(("Goal" :in-theory (enable rw.crewrite-rule-trace-env-okp))))




(defund rw.assumptions-tracep (x)
  ;;
  ;; ------------------------------- as justified by the assumptions system
  ;;   hyps -> (equiv lhs rhs) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'assumptions)
         (rw.eqtracep extras)
         (rw.eqtrace-okp extras hypbox)
         (not subtraces)
         ;; An eqtrace has the form [hyps ->] (equiv rhs lhs).  We'll need to
         ;; change that around.
         (equal iffp (rw.eqtrace->iffp extras))
         (equal rhs (rw.eqtrace->lhs extras))
         (equal lhs (rw.eqtrace->rhs extras)))))

(defthm booleanp-of-rw.assumptions-tracep
  (equal (booleanp (rw.assumptions-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.assumptions-tracep)
                                 ((:executable-counterpart ACL2::force))))))




(defund rw.force-tracep (x)
  ;;
  ;; ------------------------------- as justified by our forcing system
  ;;  [hyps ->] (iff lhs t) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'force)
         (equal rhs ''t)
         iffp
         (not subtraces)
         (not extras))))

(defthm booleanp-of-rw.force-tracep
  (equal (booleanp (rw.force-tracep x))
         t)
  :hints(("Goal" :in-theory (enable rw.force-tracep))))




(defund rw.weakening-tracep (x)
  ;;       (equiv lhs rhs) = t
  ;; ---------------------------------
  ;;   [hyps ->] (equiv lhs rhs) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'weakening)
         (not extras)
         (tuplep 1 subtraces)
         (let ((subtrace (car subtraces)))
           (and (not (rw.hypbox->left (rw.trace->hypbox subtrace)))
                (not (rw.hypbox->right (rw.trace->hypbox subtrace)))
                (equal iffp (rw.trace->iffp subtrace))
                (equal lhs (rw.trace->lhs subtrace))
                (equal rhs (rw.trace->rhs subtrace)))))))

(defthm booleanp-of-rw.weakening-tracep
  (equal (booleanp (rw.weakening-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.weakening-tracep)
                                 ((:executable-counterpart ACL2::force))))))