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
(include-book "../evaluator")
(include-book "../../defderiv/defderiv")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.fail-tracep (x)
  ;;
  ;; -----------------------------
  ;;   [hyps ->] (equiv x x) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'fail)
         (equal lhs rhs)
         (not subtraces)
         (not extras))))

(defthm booleanp-of-rw.fail-tracep
  (equal (booleanp (rw.fail-tracep x))
         t)
  :hints(("Goal" :in-theory (enable rw.fail-tracep))))



(defund rw.transitivity-tracep (x)
  ;;   [hyps ->] (equiv a b) = t
  ;;   [hyps ->] (equiv b c) = t
  ;; -----------------------------
  ;;   [hyps ->] (equiv a c) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (hypbox    (rw.trace->hypbox x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (iffp      (rw.trace->iffp x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'transitivity)
         (equal (len subtraces) 2)
         (not extras)
         (let ((equiv-a-b (first subtraces))
               (equiv-b-c (second subtraces)))
           (and (equal (rw.trace->iffp equiv-a-b) iffp)
                (equal (rw.trace->iffp equiv-b-c) iffp)
                (equal (rw.trace->hypbox equiv-a-b) hypbox)
                (equal (rw.trace->hypbox equiv-b-c) hypbox)
                (equal (rw.trace->lhs equiv-a-b) lhs)
                (equal (rw.trace->rhs equiv-a-b) (rw.trace->lhs equiv-b-c))
                (equal (rw.trace->rhs equiv-b-c) rhs))))))

(defthm booleanp-of-rw.transitivity-tracep
  (equal (booleanp (rw.transitivity-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.transitivity-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.equiv-by-args-tracep (x)
  ;;   [hyps ->] (equal a1 a1') = t
  ;;   ...
  ;;   [hyps ->] (equal an an') = t
  ;; -------------------------------------------------------
  ;;   [hyps ->] (equiv (f a1 ... an) (f a1' ... an')) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (hypbox    (rw.trace->hypbox x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'equiv-by-args)
         (logic.functionp lhs)
         (logic.functionp rhs)
         (equal (logic.function-name lhs) (logic.function-name rhs))
         (equal (logic.function-args lhs) (rw.trace-list-lhses subtraces))
         (equal (logic.function-args rhs) (rw.trace-list-rhses subtraces))
         (all-equalp nil (rw.trace-list-iffps subtraces))
         (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
         (not extras))))

(defthm booleanp-of-rw.equiv-by-args-tracep
  (equal (booleanp (rw.equiv-by-args-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.equiv-by-args-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.lambda-equiv-by-args-tracep (x)
  ;;   [hyps ->] (equal a1 a1') = t
  ;;   ...
  ;;   [hyps ->] (equal an an') = t
  ;; -------------------------------------------------------------------------------------------------
  ;;   [hyps ->] (equiv ((lambda (x1 ... xn) B) a1 ... an) ((lambda (x1 ... xn) B) a1' ... an')) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (hypbox    (rw.trace->hypbox x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'lambda-equiv-by-args)
         (logic.lambdap lhs)
         (logic.lambdap rhs)
         (equal (logic.lambda-formals lhs) (logic.lambda-formals rhs))
         (equal (logic.lambda-body lhs) (logic.lambda-body rhs))
         (equal (logic.lambda-actuals lhs) (rw.trace-list-lhses subtraces))
         (equal (logic.lambda-actuals rhs) (rw.trace-list-rhses subtraces))
         (all-equalp nil (rw.trace-list-iffps subtraces))
         (all-equalp hypbox (rw.trace-list-hypboxes subtraces))
         (not extras))))

(defthm booleanp-of-rw.lambda-equiv-by-args-tracep
  (equal (booleanp (rw.lambda-equiv-by-args-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.lambda-equiv-by-args-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.beta-reduction-tracep (x)
  ;;
  ;; ---------------------------------------------------------------------
  ;; [hyps ->] (equiv ((lambda (x1 ... xn) B) a1 ... an) B/[Xi<-Ai]) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'beta-reduction)
         (logic.lambdap lhs)
         (let ((formals (logic.lambda-formals lhs))
               (body    (logic.lambda-body lhs))
               (actuals (logic.lambda-actuals lhs)))
           (equal (logic.substitute body (pair-lists formals actuals)) rhs))
         (not subtraces)
         (not extras))))

(defthm booleanp-of-rw.beta-reduction-tracep
  (equal (booleanp (rw.beta-reduction-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.beta-reduction-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.ground-tracep (x defs)
  ;;
  ;; ------------------------------     where x is a ground term that simplifies to x'
  ;;   [hyps ->] (equiv x x') = t
  (declare (xargs :guard (and (rw.tracep x)
                              (definition-listp defs))))
  (let ((method    (rw.trace->method x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (iffp      (rw.trace->iffp x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x))) ;; the depth
    (and (equal method 'ground)
         (logic.groundp lhs)
         (not subtraces)
         (natp extras)
         (let ((result (generic-evaluator lhs defs extras)))
           (and result
                (equal rhs (if (and iffp (not (equal (logic.unquote result) nil)))
                               ''t ;; Results should be canonical when iffp is set
                             result)))))))

(defthm booleanp-of-rw.ground-tracep
  (equal (booleanp (rw.ground-tracep x defs))
         t)
  :hints(("Goal" :in-theory (enable rw.ground-tracep))))




(defund@ rw.if-specialcase-nil-tracep (x)
  ;;   [hyps ->] (iff a1 nil) = t
  ;;   [hyps ->] (equiv c1 c2) = t
  ;; ------------------------------------------
  ;;   [hyps ->] (equiv (if a1 b1 c1) c2) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'if-specialcase-nil)
         (equal (len subtraces) 2)
         (equal (rw.trace->hypbox (first subtraces)) hypbox)
         (equal (rw.trace->hypbox (second subtraces)) hypbox)
         (rw.trace->iffp (first subtraces))
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (@match (term (rw.trace->lhs (first subtraces)) (? a1))
                 (term (rw.trace->rhs (first subtraces)) nil)
                 (term (rw.trace->lhs (second subtraces)) (? c1))
                 (term (rw.trace->rhs (second subtraces)) (? c2))
                 (term lhs (if (? a1) (? b1) (? c1)))
                 (term rhs (? c2)))
         (not extras))))

(defthm booleanp-of-rw.if-specialcase-nil-tracep
  (equal (booleanp (rw.if-specialcase-nil-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.if-specialcase-nil-tracep)
                                 ((:executable-counterpart acl2::force))))))



(defund@ rw.if-specialcase-t-tracep (x)
  ;;   [hyps ->] (iff a1 const) = t
  ;;   [hyps ->] (equiv b1 b2) = t
  ;; ------------------------------------------   where const is a non-nil constant
  ;;   [hyps ->] (equiv (if a1 b1 c1) b2) = t
  (declare (xargs :guard (rw.tracep x)))
  (let* ((method    (rw.trace->method x))
         (hypbox    (rw.trace->hypbox x))
         (lhs       (rw.trace->lhs x))
         (rhs       (rw.trace->rhs x))
         (iffp      (rw.trace->iffp x))
         (subtraces (rw.trace->subtraces x))
         (extras    (rw.trace->extras x)))
    (and (equal method 'if-specialcase-t)
         (equal (len subtraces) 2)
         (equal (rw.trace->hypbox (first subtraces)) hypbox)
         (equal (rw.trace->hypbox (second subtraces)) hypbox)
         (rw.trace->iffp (first subtraces))
         (equal (rw.trace->iffp (second subtraces)) iffp)
         (@match (term (rw.trace->lhs (first subtraces)) (? a1))
                 (term (rw.trace->rhs (first subtraces)) (? const))
                 (term (rw.trace->lhs (second subtraces)) (? b1))
                 (term (rw.trace->rhs (second subtraces)) (? b2))
                 (term lhs (if (? a1) (? b1) (? c1)))
                 (term rhs (? b2)))
         (logic.constantp (@term (? const)))
         (not (equal (logic.unquote (@term (? const))) nil))
         (not extras))))

(defthm booleanp-of-rw.if-specialcase-t-tracep
  (equal (booleanp (rw.if-specialcase-t-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.if-specialcase-t-tracep)
                                 ((:executable-counterpart acl2::force))))))




(defund@ rw.not-tracep (x)
  ;;      [hyps ->] (iff x x-prime) = t
  ;;    -----------------------------------------------
  ;;      [hyps ->] (equiv (not x) (not x-prime)) = t     General Case
  ;; or   [hyps ->] (equiv (not x) t) = t                 When x-prime is nil
  ;; or   [hyps ->] (equiv (not x) nil) = t               When x-prime is t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (hypbox    (rw.trace->hypbox x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x)))
    (and (equal method 'not)
         (logic.functionp lhs)
         (let ((name (logic.function-name lhs))
               (args (logic.function-args lhs)))
           (and (equal name 'not)
                (equal (len args) 1)
                (equal (len subtraces) 1)
                (let ((guts (first args))
                      (sub1 (first subtraces)))
                  (and (equal (rw.trace->hypbox sub1) hypbox)
                       (equal (rw.trace->iffp sub1) t)
                       (equal (rw.trace->lhs sub1) guts)
                       (let ((sub1-rhs (rw.trace->rhs sub1)))
                         (cond ((equal sub1-rhs ''t)
                                (equal rhs ''nil))
                               ((equal sub1-rhs ''nil)
                                (equal rhs ''t))
                               (t
                                (equal rhs (logic.function 'not (list sub1-rhs)))))))))))))

(defthm booleanp-of-rw.not-tracep
  (equal (booleanp (rw.not-tracep x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.not-tracep)
                                 ((:executable-counterpart ACL2::force))))))




(defund@ rw.negative-if-tracep (x)
  ;;
  ;; ----------------------------------------------
  ;;   [hyps ->] (equiv (if x nil t) (not x)) = t
  (declare (xargs :guard (rw.tracep x)))
  (let ((method    (rw.trace->method x))
        (lhs       (rw.trace->lhs x))
        (rhs       (rw.trace->rhs x))
        (subtraces (rw.trace->subtraces x))
        (extras    (rw.trace->extras x)))
    (and (equal method 'negative-if)
         (not subtraces)
         (not extras)
         (logic.functionp lhs)
         (logic.functionp rhs)
         (let ((lhs-name (logic.function-name lhs))
               (lhs-args (logic.function-args lhs))
               (rhs-name (logic.function-name rhs))
               (rhs-args (logic.function-args rhs)))
           (and (equal lhs-name 'if)
                (equal (len lhs-args) 3)
                (equal (second lhs-args) ''nil)
                (equal (third lhs-args) ''t)
                (equal rhs-name 'not)
                (equal (len rhs-args) 1)
                (equal (first lhs-args) (first rhs-args)))))))

(defthm booleanp-of-rw.negative-if-tracep
  (equal (booleanp (rw.negative-if-tracep x))
         t)
  :hints(("Goal" :in-theory (enable rw.negative-if-tracep))))

