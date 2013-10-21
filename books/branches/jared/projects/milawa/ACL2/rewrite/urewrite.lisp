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
(include-book "traces/urewrite-builders")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(definline rw.empty-hypbox ()
  (declare (xargs :guard t))
  (rw.hypbox nil nil))


(defconst *rw.flag-urewrite*
  '(cond
    ((zp n)
     (ACL2::prog2$ (ACL2::cw! "[rw.urewrite]: ran out of steps on ~x0.!~%" x)
                   (rw.fail-trace (rw.empty-hypbox) x iffp)))

    ((logic.constantp x)
     ;; we might be able to canonicalize constants under iffp
     (or (rw.try-ground-simplify (rw.empty-hypbox) x iffp control)
         (rw.fail-trace (rw.empty-hypbox) x iffp)))

    ((logic.variablep x)
     ;; can't simplify variables since we have no assumptions
     (rw.fail-trace (rw.empty-hypbox) x iffp))

    ((logic.functionp x)
     (let ((name (logic.function-name x))
           (args (logic.function-args x)))
       (if (and (equal name 'if)
                (equal (len args) 3))
           (let* ((arg1 (first args))
                  (arg2 (second args))
                  (arg3 (third args))
                  (arg1-trace (rw.flag-urewrite 'term arg1 t control n))
                  (arg1-prime (rw.trace->rhs arg1-trace)))
             (if (logic.constantp arg1-prime)
                 (if (logic.unquote arg1-prime)
                     (rw.if-specialcase-t-trace arg1-trace (rw.flag-urewrite 'term arg2 iffp control n) arg3)
                   (rw.if-specialcase-nil-trace arg1-trace (rw.flag-urewrite 'term arg3 iffp control n) arg2))
               (let* ((arg2-trace (rw.flag-urewrite 'term arg2 iffp control n))
                      (arg3-trace (rw.flag-urewrite 'term arg3 iffp control n))
                      (arg2-prime (rw.trace->rhs arg2-trace))
                      (arg3-prime (rw.trace->rhs arg3-trace)))
                 (if (equal arg2-prime arg3-prime)
                     (rw.urewrite-if-specialcase-same-trace arg2-trace arg3-trace arg1)
                   (let ((general-trace (rw.urewrite-if-generalcase-trace arg1-trace arg2-trace arg3-trace)))
                     (if (and (equal arg2-prime ''nil)
                              (equal arg3-prime ''t))
                         (rw.transitivity-trace general-trace (rw.negative-if-trace arg1-prime iffp (rw.empty-hypbox)))
                       general-trace))))))
         (or
          ;; Try evaluation.  This prevents loops with constant-gathering rules and
          ;; outside-in rewrite rules.  If we win, we're canonical and can stop.
          (and (logic.constant-listp args)
               (rw.try-ground-simplify (rw.empty-hypbox) x iffp control))
          ;; Try outside-in rules.  If we win, we need to keep rewriting because we
          ;; probably aren't canonical yet.
          (let ((outside-trace (rw.try-urewrite-rules (rw.empty-hypbox) x 'outside iffp control)))
            (and outside-trace
                 (rw.transitivity-trace outside-trace
                                        (rw.flag-urewrite 'term (rw.trace->rhs outside-trace) iffp control (- n 1)))))
          ;; Try working inside out.
          (let* ((arg-traces (rw.flag-urewrite 'list args nil control n))
                 (main-trace (rw.equiv-by-args-trace (rw.empty-hypbox) name iffp arg-traces)) ;; (f args) == (f args')
                 (term-prime (rw.trace->rhs main-trace))
                 (args-prime (logic.function-args term-prime)))
            (or
             ;; If all the args turned into constants, try evaluation.  If we win, we
             ;; can stop because we're canonical.
             (let ((ground-trace (and (logic.constant-listp args-prime)
                                      (rw.try-ground-simplify (rw.empty-hypbox) term-prime iffp control))))
               (and ground-trace
                    (rw.transitivity-trace main-trace ground-trace)))
             ;; Otherwise, try using inside-out rules.  If we win, we need to keep
             ;; rewriting because we may not be canonical yet.
             (let ((rule-trace (rw.try-urewrite-rules (rw.empty-hypbox) term-prime 'inside iffp control)))
               (and rule-trace
                    (let ((next-trace (rw.flag-urewrite 'term (rw.trace->rhs rule-trace) iffp control (- n 1))))
                      (rw.transitivity-trace main-trace
                                             (rw.transitivity-trace rule-trace next-trace)))))
             ;; Otherwise nothing works, maybe some argument simplified.
             main-trace))))))

    ((logic.lambdap x)
     (let* ((formals    (logic.lambda-formals x))
            (body       (logic.lambda-body x))
            (actuals    (logic.lambda-actuals x))
            (arg-traces (rw.flag-urewrite 'list actuals nil control n))
            (main-trace (rw.lambda-equiv-by-args-trace (rw.empty-hypbox) formals body iffp arg-traces)) ;; (lambda ... args) == (lambda ... args')
            (term-prime (rw.trace->rhs main-trace))
            (args-prime (logic.lambda-actuals term-prime)))
       (or
        ;; Perhaps we can just evaluate it?
        (and (logic.constant-listp args-prime)
             (let ((ground-trace (rw.try-ground-simplify (rw.empty-hypbox) term-prime iffp control)))
               (and ground-trace
                    (rw.transitivity-trace main-trace ground-trace))))
        ;; Perhaps we're allowed to beta reduce?
        ;; We haven't bothered to implement recursive simplification, i.e., we treat t as 'once.
        (and (rw.control->betamode control)
             (let* ((trace1 (rw.beta-reduction-trace (rw.empty-hypbox) term-prime iffp)) ;; (lambda ... args') == body/args'
                    (trace2 (rw.transitivity-trace main-trace trace1)) ;; (lambda ... args) == body/args'
                    (trace3 (rw.flag-urewrite 'term (rw.trace->rhs trace1) iffp control (- n 1)))) ;; body/args' == result
               (rw.transitivity-trace trace2 trace3))) ;; (lambda ... args) == result
        ;; Otherwise we can only hope an argument simplified.
        main-trace)))))

(defconst *rw.flag-urewrite-list*
  '(if (consp x)
       (cons (rw.flag-urewrite 'term (car x) iffp control n)
             (rw.flag-urewrite 'list (cdr x) iffp control n))
     nil))


(ACL2::make-event
 `(defun rw.flag-urewrite (flag x iffp control n)
    ;; We perform up to n passes of unconditional rewriting.
    (declare (xargs :guard (and (booleanp iffp)
                                (rw.controlp control)
                                (natp n)
                                (if (equal flag 'term)
                                    (logic.termp x)
                                  (and (equal flag 'list)
                                       (logic.term-listp x))))
                    :measure (two-nats-measure (nfix n) (rank x))
                    :verify-guards nil))
    (if (equal flag 'term)
        ,*rw.flag-urewrite*
      ,*rw.flag-urewrite-list*)))

(defund rw.urewrite (x iffp control n)
  (declare (xargs :guard (and (logic.termp x)
                              (booleanp iffp)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil))
  (rw.flag-urewrite 'term x iffp control n))

(defund rw.urewrite-list (x iffp control n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (booleanp iffp)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil))
  (rw.flag-urewrite 'list x iffp control n))

(defconst *rw.flagless-urewrite-sigma*
  (list (cons '(ACL2::prog2$ ?x ?y)
              '?y)
        (cons '(rw.flag-urewrite 'term ?x ?iffp ?control ?n)
              '(rw.urewrite ?x ?iffp ?control ?n))
        (cons '(rw.flag-urewrite 'list ?x ?iffp ?control ?n)
              '(rw.urewrite-list ?x ?iffp ?control ?n))))

(ACL2::make-event
 `(defthmd definition-of-rw.urewrite
    (equal (rw.urewrite x iffp control n)
           ,(ACL2::jared-rewrite *rw.flag-urewrite* *rw.flagless-urewrite-sigma*))
    :rule-classes :definition
    :hints(("Goal"
            :in-theory (enable rw.urewrite rw.urewrite-list)
            :expand (rw.flag-urewrite 'term x iffp control n)))))

(ACL2::make-event
 `(defthmd definition-of-rw.urewrite-list
    (equal (rw.urewrite-list x iffp control n)
           ,(ACL2::jared-rewrite *rw.flag-urewrite-list* *rw.flagless-urewrite-sigma*))
    :rule-classes :definition
    :hints(("Goal"
            :in-theory (enable rw.urewrite rw.urewrite-list)
            :expand (rw.flag-urewrite 'list x iffp control n)))))

(defthm rw.flag-urewrite-of-term
  (equal (rw.flag-urewrite 'term x iffp control n)
         (rw.urewrite x iffp control n))
  :hints(("Goal" :in-theory (enable rw.urewrite))))

(defthm rw.flag-urewrite-of-list
  (equal (rw.flag-urewrite 'list x iffp control n)
         (rw.urewrite-list x iffp control n))
  :hints(("Goal" :in-theory (enable rw.urewrite-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.urewrite))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.urewrite-list))))

(defthm rw.urewrite-list-when-not-consp
  (implies (not (consp x))
           (equal (rw.urewrite-list x iffp control n)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.urewrite-list))))

(defthm rw.urewrite-list-of-cons
  (equal (rw.urewrite-list (cons a x) iffp control n)
         (cons (rw.urewrite a iffp control n)
               (rw.urewrite-list x iffp control n)))
  :hints(("Goal" :in-theory (enable definition-of-rw.urewrite-list))))

(defprojection
  :list (rw.urewrite-list x iffp control n)
  :element (rw.urewrite x iffp control n)
  :already-definedp t)

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.tracep-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.tracep (rw.urewrite x iffp control n))
                               t)))
         (t forcing-rw.trace-listp-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-listp (rw.urewrite-list x iffp control n))
                            t))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :in-theory (disable forcing-lookup-of-logic.function-name)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.trace->iffp-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.trace->iffp (rw.urewrite x iffp control n))
                               iffp)))
         (t forcing-rw.trace-list-iffps-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-list-iffps (rw.urewrite-list x iffp control n))
                            (repeat iffp (len x))))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :in-theory (disable forcing-lookup-of-logic.function-name)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.trace->lhs-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.trace->lhs (rw.urewrite x iffp control n))
                               x)))
         (t forcing-rw.trace-list-lhses-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-list-lhses (rw.urewrite-list x iffp control n))
                            (list-fix x)))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :in-theory (disable forcing-lookup-of-logic.function-name)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.trace->nhyps-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.trace->hypbox (rw.urewrite x iffp control n))
                               (rw.empty-hypbox))))
         (t forcing-rw.trace-list-nhyps-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-list-hypboxes (rw.urewrite-list x iffp control n))
                            (repeat (rw.empty-hypbox) (len x))))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :in-theory (disable forcing-lookup-of-logic.function-name)
           :induct (rw.flag-urewrite flag x iffp control n))))

(verify-guards rw.flag-urewrite)
(verify-guards rw.urewrite)
(verify-guards rw.urewrite-list)

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)
                          (rw.control-atblp control atbl)
                          (equal (cdr (lookup 'not atbl)) 1)))
  :thms ((term forcing-rw.trace-atblp-of-rw.urewrite
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)))
                        (equal (rw.trace-atblp (rw.urewrite x iffp control n) atbl)
                               t)))
         (t forcing-rw.trace-list-atblp-of-rw.urewrite-list
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)))
                     (equal (rw.trace-list-atblp (rw.urewrite-list x iffp control n) atbl)
                            t))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)
                          (rw.control-atblp control atbl)
                          (rw.control-env-okp control axioms thms)
                          (equal (cdr (lookup 'not atbl)) 1)))
  :thms ((term forcing-rw.trace-env-okp-of-rw.urewrite
               (implies (force (and (logic.termp x)
                                    (logic.term-atblp x atbl)))
                        (equal (rw.trace-env-okp (rw.urewrite x iffp control n) defs thms atbl)
                               t)))
         (t forcing-rw.trace-list-env-okp-of-rw.urewrite-list
            (implies (force (and (logic.term-listp x)
                                 (logic.term-list-atblp x atbl)))
                     (equal (rw.trace-list-env-okp (rw.urewrite-list x iffp control n) defs thms atbl)
                            t))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.trace-okp-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.trace-okp (rw.urewrite x iffp control n)
                                             (rw.control->defs control))
                               t)))
         (t forcing-rw.trace-list-okp-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-list-okp (rw.urewrite-list x iffp control n)
                                               (rw.control->defs control))
                            t))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :induct (rw.flag-urewrite flag x iffp control n))))

(defthms-flag
  :shared-hyp (force (and (booleanp iffp)
                          (rw.controlp control)))
  :thms ((term forcing-rw.collect-forced-goals-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.collect-forced-goals (rw.urewrite x iffp control n))
                               nil)))
         (t forcing-rw.collect-forced-goals-list-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.collect-forced-goals-list (rw.urewrite-list x iffp control n))
                            nil))))
  :hints (("Goal"
           :expand (rw.urewrite x iffp control n)
           :induct (rw.flag-urewrite flag x iffp control n))))



;; (defund rw.urewrite (x iffp control n)
;;   ;; We perform (up to) n+1 inside-out passes of unconditional rewriting, and
;;   ;; produce a trace of our progress.
;;   (declare (xargs :guard (and (logic.termp x)
;;                               (booleanp iffp)
;;                               (rw.controlp control)
;;                               (natp n))
;;                   :measure (nfix n)
;;                   :verify-guards nil))
;;   (let ((first-trace (rw.urewrite-core x iffp control)))
;;     (cond ((equal (rw.trace->method first-trace) 'fail)
;;            ;; No simplification was possible
;;            first-trace)

;;           ((zp n)
;;            ;; We cannot further simplify becuase we have run out of steps.
;;            (ACL2::prog2$ (ACL2::cw "[rw.urewrite] Warning: ran out of rewriting steps.~%")
;;                          first-trace))

;;           (t
;;            ;; Perhaps we can simplify it further?
;;            (rw.transitivity-trace first-trace
;;                                   (rw.urewrite (rw.trace->rhs first-trace) iffp control (- n 1)))))))


;; (encapsulate
;;  ()
;;  (local (in-theory (enable rw.urewrite)))

;;  (defthm forcing-rw.tracep-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.tracep (rw.urewrite x iffp control n))
;;                    t)))

;;  (defthm forcing-rw.trace-atblp-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (logic.term-atblp x atbl)
;;                         (booleanp iffp)
;;                         (rw.controlp control)
;;                         (rw.control-atblp control atbl)
;;                         (equal (cdr (lookup 'not atbl)) 1)))
;;             (equal (rw.trace-atblp (rw.urewrite x iffp control n) atbl)
;;                    t)))

;;  (defthm forcing-rw.trace->lhs-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace->lhs (rw.urewrite x iffp control n))
;;                    x)))

;;  (defthm forcing-rw.trace->hypbox-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace->hypbox (rw.urewrite x iffp control n))
;;                    (rw.empty-hypbox))))

;;  (defthm forcing-rw.trace->iffp-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace->iffp (rw.urewrite x iffp control n))
;;                    iffp)))

;;  (verify-guards rw.urewrite)

;;  (defthm forcing-rw.trace-okp-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-okp (rw.urewrite x iffp control n))
;;                    t)))

;;  (defthm forcing-rw.trace-env-okp-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (logic.term-atblp x atbl)
;;                         (booleanp iffp)
;;                         (rw.controlp control)
;;                         (rw.control-atblp control atbl)
;;                         (rw.control-env-okp control axioms thms)
;;                         (equal (cdr (lookup 'not atbl)) 1)))
;;             (equal (rw.trace-env-okp (rw.urewrite x iffp control n) axioms thms atbl)
;;                    t)))

;;  (defthm forcing-rw.collect-forced-goals-of-rw.urewrite
;;    (implies (force (and (logic.termp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.collect-forced-goals (rw.urewrite x iffp control n))
;;                    nil))))




;; (defprojection :list (rw.urewrite-list x iffp control n)
;;                :element (rw.urewrite x iffp control n)
;;                :guard (and (logic.term-listp x)
;;                            (booleanp iffp)
;;                            (rw.controlp control)
;;                            (natp n)))

;; (encapsulate
;;  ()
;;  (defthm forcing-rw.trace-listp-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-listp (rw.urewrite-list x iffp control n))
;;                    t))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-atblp-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (logic.term-list-atblp x atbl)
;;                         (booleanp iffp)
;;                         (rw.controlp control)
;;                         (rw.control-atblp control atbl)
;;                         (equal (cdr (lookup 'not atbl)) 1)))
;;             (equal (rw.trace-list-atblp (rw.urewrite-list x iffp control n) atbl)
;;                    t))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-lhses-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-list-lhses (rw.urewrite-list x iffp control n))
;;                    (list-fix x)))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-iffps-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-list-iffps (rw.urewrite-list x iffp control n))
;;                    (repeat iffp (len x))))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-hypboxes-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-list-hypboxes (rw.urewrite-list x iffp control n))
;;                    (repeat (rw.empty-hypbox) (len x))))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-okp-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.trace-list-okp (rw.urewrite-list x iffp control n))
;;                    t))
;;    :hints(("Goal" :induct (cdr-induction x))))

;;  (defthm forcing-rw.trace-list-env-okp-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (logic.term-list-atblp x atbl)
;;                         (booleanp iffp)
;;                         (rw.controlp control)
;;                         (rw.control-atblp control atbl)
;;                         (rw.control-env-okp control axioms thms)
;;                         (equal (cdr (lookup 'not atbl)) 1)))
;;             (equal (rw.trace-list-env-okp (rw.urewrite-list x iffp control n) axioms thms atbl)
;;                    t))
;;    :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.trace-list-formulas-of-rw.urewrite-list
   (implies (force (and (logic.term-listp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace-list-formulas (rw.urewrite-list x iffp control n))
                   (rw.trace-list-conclusion-formulas (rw.urewrite-list x iffp control n))))
   :hints(("Goal"
           :use ((:instance rw.trace-list-formulas-when-all-equalp-of-rw.trace-list-hypboxes
                            (hypbox (rw.empty-hypbox))
                            (x (rw.urewrite-list x iffp control n)))))))

(defthm forcing-rw.trace-list-conclusion-formulas-of-rw.urewrite-list
   (implies (force (and (logic.term-listp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.trace-list-conclusion-formulas (rw.urewrite-list x iffp control n))
                   (logic.pequal-list
                    (logic.function-list (if iffp 'iff 'equal)
                                         (list2-list (rw.trace-list-lhses (rw.urewrite-list x iffp control n))
                                                     (rw.trace-list-rhses (rw.urewrite-list x iffp control n))))
                    (repeat ''t (len x)))))
   :hints(("Goal"
           :induct (cdr-induction x)
           :in-theory (enable rw.trace-conclusion-formula rw.trace-list-conclusion-formulas))))

;;  (defthm forcing-rw.collect-forced-goals-list-of-rw.urewrite-list
;;    (implies (force (and (logic.term-listp x)
;;                         (booleanp iffp)
;;                         (rw.controlp control)))
;;             (equal (rw.collect-forced-goals-list (rw.urewrite-list x iffp control n))
;;                    nil))
;;    :hints(("Goal" :induct (cdr-induction x)))))



(defprojection :list (rw.urewrite-list-list x iffp control n)
               :element (rw.urewrite-list x iffp control n)
               :guard (and (logic.term-list-listp x)
                           (booleanp iffp)
                           (rw.controlp control)
                           (natp n)))

(defthm cons-listp-of-rw.urewrite-list-list
  (equal (cons-listp (rw.urewrite-list-list x iffp control n))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.trace-list-listp-of-rw.urewrite-list-list
  (implies (force (and (logic.term-list-listp x)
                       (rw.controlp control)
                       (booleanp iffp)))
           (equal (rw.trace-list-listp (rw.urewrite-list-list x iffp control n))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.collect-forced-goals-list-list-of-rw.urewrite-list-list
  (implies (force (and (logic.term-list-listp x)
                       (rw.controlp control)
                       (booleanp iffp)))
           (equal (rw.collect-forced-goals-list-list (rw.urewrite-list-list x iffp control n))
                  nil))
  :hints(("Goal" :induct (cdr-induction x))))
