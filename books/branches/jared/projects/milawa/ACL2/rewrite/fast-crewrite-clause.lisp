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
(include-book "crewrite-clause")
(include-book "fast-crewrite")
(include-book "fast-traces")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(definlined rw.fast-ccstepp (x)
  (declare (xargs :guard t))
  (and (consp x)
       ;; (contradictionp . ftrace)
       (let ((contradictionp (car x))
             (ftrace         (cdr x)))
         (and (booleanp contradictionp)
              (if contradictionp
                  (not ftrace)
                (rw.ftracep ftrace))))))

(definlined rw.fast-ccstep (contradictionp ftrace)
  (declare (xargs :guard (and (booleanp contradictionp)
                              (if contradictionp
                                  (not ftrace)
                                (rw.ftracep ftrace)))))
  (cons contradictionp ftrace))

(definlined rw.fast-ccstep->contradictionp (x)
  (declare (xargs :guard (rw.fast-ccstepp x)))
  (car x))

(definlined rw.fast-ccstep->ftrace (x)
  (declare (xargs :guard (rw.fast-ccstepp x)))
  (cdr x))

(defthm rw.fast-ccstep->contradictionp-of-rw.fast-ccstep
  (equal (rw.fast-ccstep->contradictionp (rw.fast-ccstep contradictionp ftrace))
         contradictionp)
  :hints(("Goal" :in-theory (enable rw.fast-ccstep
                                    rw.fast-ccstep->contradictionp))))

(defthm rw.fast-ccstep->ftrace-of-rw.fast-ccstep
  (equal (rw.fast-ccstep->ftrace (rw.fast-ccstep contradictionp ftrace))
         ftrace)
  :hints(("Goal" :in-theory (enable rw.fast-ccstep
                                    rw.fast-ccstep->ftrace))))

(defthm booleanp-of-rw.fast-ccstepp
  (equal (booleanp (rw.fast-ccstepp x))
         t)
  :hints(("Goal" :in-theory (enable rw.fast-ccstepp))))

(defthm rw.fast-ccstepp-of-rw.fast-ccstep
  (implies (force (and (booleanp contradictionp)
                       (if contradictionp
                           (not ftrace)
                         (rw.ftracep ftrace))))
           (equal (rw.fast-ccstepp (rw.fast-ccstep contradictionp ftrace))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-ccstepp rw.fast-ccstep))))

(defthm booleanp-of-rw.fast-ccstep->contradictionp
  (implies (force (rw.fast-ccstepp x))
           (equal (booleanp (rw.fast-ccstep->contradictionp x))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-ccstepp
                                    rw.fast-ccstep->contradictionp))))

(defthm rw.ftracep-of-rw.fast-ccstep->ftrace
  (implies (and (force (rw.fast-ccstepp x))
                (force (not (rw.fast-ccstep->contradictionp x))))
           (equal (rw.ftracep (rw.fast-ccstep->ftrace x))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-ccstepp
                                    rw.fast-ccstep->contradictionp
                                    rw.fast-ccstep->ftrace))))





(definlined rw.ccstep-fast-image (x)
  (declare (xargs :guard (rw.ccstepp x)))
  (let* ((contradictionp (if (rw.ccstep->contradiction x) t nil))
         (trace          (if contradictionp
                             nil
                           (rw.trace-fast-image (rw.ccstep->trace x)))))
    (rw.fast-ccstep contradictionp trace)))

(defthm rw.fast-ccstepp-of-rw.ccstep-fast-image
  (implies (force (rw.ccstepp x))
           (equal (rw.fast-ccstepp (rw.ccstep-fast-image x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-fast-image))))

(defthm rw.fast-ccstep->contradictionp-of-rw.ccstep-fast-image
  (equal (rw.fast-ccstep->contradictionp (rw.ccstep-fast-image x))
         (if (rw.ccstep->contradiction x) t nil))
  :hints(("Goal" :in-theory (enable rw.ccstep-fast-image))))

(defthm rw.fast-ccstep->ftrace-of-rw.ccstep-fast-image
  (equal (rw.fast-ccstep->ftrace (rw.ccstep-fast-image x))
         (if (rw.ccstep->contradiction x)
             nil
           (rw.trace-fast-image (rw.ccstep->trace x))))
  :hints(("Goal" :in-theory (enable rw.ccstep-fast-image))))



(defund rw.fast-crewrite-take-step (todo done blimit rlimit control n)
  ;; Note: redefined to add timing information in interface/rewrite-tactics.lisp
  (declare (xargs :guard (and (consp todo)
                              (logic.term-listp todo)
                              (logic.term-listp done)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n))))
  (let* ((assms (rw.empty-fast-assms (rw.control->assmctrl control)))
         (assms (rw.fast-assume-left-list (cdr todo) assms))
         (assms (rw.fast-assume-right-list done assms))
         (contr (rw.fast-assms->contradiction assms)))
    (rw.fast-ccstep contr
                    (if contr
                        nil
                      (rw.fast-crewrite assms (car todo) t blimit rlimit control n)))))

(defthm rw.fast-ccstepp-of-rw.fast-crewrite-take-step
  (implies (force (and (consp todo)
                       (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.fast-ccstepp (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-crewrite-take-step))))

(defthm rw.ccstep-fast-image-of-rw.crewrite-take-step
  (implies (force (and (consp todo)
                       (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.ccstep-fast-image (rw.crewrite-take-step todo done blimit rlimit control n))
                  (rw.fast-crewrite-take-step todo done blimit rlimit control n)))
  :hints(("Goal"
          :in-theory (e/d (rw.ccstep-fast-image
                           rw.crewrite-take-step
                           rw.fast-crewrite-take-step)
                          (rw.fast-assms->contradiction-of-rw.assms-fast-image))
          :use ((:instance rw.fast-assms->contradiction-of-rw.assms-fast-image
                           (assms (rw.assume-right-list
                                   done
                                   (rw.assume-left-list (cdr todo)
                                                        (rw.empty-assms (rw.control->assmctrl control))))))))))

(defthm rw.fast-ccstep->contradictionp-of-rw.fast-crewrite-take-step
  (implies (force (and (consp todo)
                       (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.fast-ccstep->contradictionp
                   (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                  (if (rw.ccstep->contradiction
                       (rw.crewrite-take-step todo done blimit rlimit control n))
                      t
                    nil)))
  :hints(("Goal"
          :in-theory (disable rw.fast-ccstep->contradictionp-of-rw.ccstep-fast-image)
          :use ((:instance rw.fast-ccstep->contradictionp-of-rw.ccstep-fast-image
                           (x (rw.crewrite-take-step todo done blimit rlimit control n)))))))

(defthm rw.fast-ccstep->ftrace-of-rw.fast-crewrite-take-step
  (implies (force (and (consp todo)
                       (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.fast-ccstep->ftrace
                   (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                  (if (rw.ccstep->contradiction
                       (rw.crewrite-take-step todo done blimit rlimit control n))
                      nil
                    (rw.trace-fast-image
                     (rw.ccstep->trace
                      (rw.crewrite-take-step todo done blimit rlimit control n))))))
  :hints(("Goal"
          :in-theory (e/d (rw.fast-crewrite-take-step
                           rw.crewrite-take-step)
                          (rw.fast-assms->contradiction-of-rw.assms-fast-image))
          :use ((:instance rw.fast-assms->contradiction-of-rw.assms-fast-image
                           (assms (rw.assume-right-list
                                   done
                                   (rw.assume-left-list (cdr todo)
                                                        (rw.empty-assms (rw.control->assmctrl control))))))))))



;; (deflist rw.fast-ccstep-listp (x)
;;   (rw.fast-ccstepp x)
;;   :elementp-of-nil nil)

;; (defprojection :list (rw.ccstep-list-fast-image x)
;;                :element (rw.ccstep-fast-image x)
;;                :guard (rw.ccstep-listp x))



(defund rw.fast-ccstep->provedp (x)
  (declare (xargs :guard (rw.fast-ccstepp x)))
  (or (rw.fast-ccstep->contradictionp x)
      (clause.obvious-termp (rw.ftrace->rhs (rw.fast-ccstep->ftrace x)))))

(defthm rw.fast-ccstep->provedp-of-rw.ccstep-fast-image
  (equal (rw.fast-ccstep->provedp (rw.ccstep-fast-image x))
         (rw.ccstep->provedp x))
  :hints(("Goal" :in-theory (enable rw.fast-ccstep->provedp
                                    rw.ccstep->provedp))))

(defthm rw.fast-ccstep->contradictionp-when-not-rw.fast-ccstep->provedp
  (implies (not (rw.fast-ccstep->provedp x))
           (equal (rw.fast-ccstep->contradictionp x)
                  nil))
  :hints(("Goal" :in-theory (enable rw.fast-ccstep->provedp))))

(defthm rw.fast-ccstep->provedp-of-rw.fast-crewrite-take-step
  (implies (force (and (consp todo)
                       (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.fast-ccstep->provedp
                   (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                  (rw.ccstep->provedp
                   (rw.crewrite-take-step todo done blimit rlimit control n))))
  :hints(("Goal"
          :in-theory (disable rw.fast-ccstep->provedp-of-rw.ccstep-fast-image)
          :use ((:instance rw.fast-ccstep->provedp-of-rw.ccstep-fast-image
                           (x (rw.crewrite-take-step todo done blimit rlimit control n)))))))



(defund rw.fast-ccstep->t1prime (x)
  (declare (xargs :guard (and (rw.fast-ccstepp x)
                              (not (rw.fast-ccstep->provedp x)))
                  :guard-hints (("Goal" :in-theory (enable rw.fast-ccstep->provedp)))))
  (rw.ftrace->rhs (rw.fast-ccstep->ftrace x)))

(defthm rw.fast-ccstep->t1prime-of-rw.ccstep-fast-image
  (implies (force (not (rw.ccstep->contradiction x)))
           (equal (rw.fast-ccstep->t1prime (rw.ccstep-fast-image x))
                  (rw.ccstep->t1prime x)))
  :hints(("Goal" :in-theory (enable rw.fast-ccstep->t1prime
                                    rw.ccstep->t1prime))))

(defthm logic.termp-of-rw.fast-ccstep->t1prime
  (implies (force (and (not (rw.fast-ccstep->contradictionp x))
                       (rw.fast-ccstepp x)))
           (equal (logic.termp (rw.fast-ccstep->t1prime x))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-ccstep->t1prime))))

(defthm rw.fast-ccstep->t1prime-of-rw.fast-crewrite-take-step
  (implies (and (not (rw.ccstep->provedp (rw.crewrite-take-step todo done blimit rlimit control n)))
                (force (and (consp todo)
                            (logic.term-listp todo)
                            (logic.term-listp done)
                            (rw.controlp control))))
           (equal (rw.fast-ccstep->t1prime
                   (rw.fast-crewrite-take-step todo done blimit rlimit control n))
                  (rw.ccstep->t1prime
                   (rw.crewrite-take-step todo done blimit rlimit control n))))
  :hints(("Goal"
          :in-theory (e/d (rw.ccstep->provedp)
                          (rw.fast-ccstep->t1prime-of-rw.ccstep-fast-image))
          :use ((:instance rw.fast-ccstep->t1prime-of-rw.ccstep-fast-image
                           (x (rw.crewrite-take-step todo done blimit rlimit control n)))))))








;; Fast clause crewriting.
;;
;; This has been kind of tricky.  We don't really care about building any
;; intermediate steps.  All we want to know is (1) whether the clause gets
;; proved, (2) what is clause-prime, if the clause wasn't proved, and (2) what
;; goals were forced?  We begin by introducing three functions to compute
;; exactly these answers.  We won't run these functions, we just use them to do
;; the reasoning.

(defund rw.crewrite-clause-aux-provedp (todo done blimit rlimit control n)
  (declare (xargs :verify-guards nil))
  (if (consp todo)
      (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
        (or (rw.ccstep->provedp step1)
            (rw.crewrite-clause-aux-provedp (cdr todo)
                                            (cons (rw.ccstep->t1prime step1) done)
                                            blimit rlimit control n)))
    nil))

(defund rw.crewrite-clause-aux-todo-primes (todo done blimit rlimit control n)
  (declare (xargs :verify-guards nil))
  (if (consp todo)
      (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
        (cons (rw.ccstep->t1prime step1)
              (rw.crewrite-clause-aux-todo-primes (cdr todo)
                                                  (cons (rw.ccstep->t1prime step1) done)
                                                  blimit rlimit control n)))
    nil))

(defund rw.crewrite-clause-aux-fgoals (todo done blimit rlimit control n)
  (declare (xargs :verify-guards nil))
  (if (consp todo)
      (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
        (if (rw.ccstep->provedp step1)
            (rw.ccstep-forced-goals step1)
          (app (rw.crewrite-clause-aux-fgoals (cdr todo)
                                              (cons (rw.ccstep->t1prime step1) done)
                                              blimit rlimit control n)
               (rw.ccstep-forced-goals step1))))
    nil))

;; We now re-phrase rw.crewrite-clause-aux in terms of these functions.  The
;; accumulator gets in the way, so we actually introduce an auxilliary function
;; first that does the same thing as rw.crewrite-clause-aux, without tail
;; recursion.  Again, we never intend to run this function.

(defund rw.crewrite-clause-aux-noacc (todo done blimit rlimit control n)
  (declare (xargs :verify-guards nil))
  (if (consp todo)
      (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
        (if (rw.ccstep->provedp step1)
            (list step1)
          (app (rw.crewrite-clause-aux-noacc (cdr todo)
                                             (cons (rw.ccstep->t1prime step1) done)
                                             blimit
                                             rlimit control n)
               (list step1))))
    nil))

(defthm consp-of-rw.crewrite-clause-aux-noacc
  (equal (consp (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n))
         (consp todo))
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-aux-noacc))))

(defthmd rw.crewrite-clause-aux-removal
  (implies (true-listp acc)
           (equal (rw.crewrite-clause-aux todo done blimit rlimit control n acc)
                  (app (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n)
                       acc)))
  :hints(("Goal"
          :in-theory (e/d (rw.crewrite-clause-aux
                           rw.crewrite-clause-aux-noacc)
                          ((:executable-counterpart acl2::force))))))


(defthmd car-of-app
  ;; Probably not something to keep enabled normally
  (equal (car (app x y))
         (if (consp x)
             (car x)
           (car y))))

(defthmd cdr-of-app
  ;; Probably not something to keep enabled normally
  (equal (cdr (app x y))
         (if (consp x)
             (app (cdr x) y)
           (cdr (list-fix y)))))

(local (in-theory (enable car-of-app cdr-of-app)))



(defthm rw.crewrite-clause-aux-provedp-correct
  (equal (rw.ccstep->provedp (car (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n)))
         (rw.crewrite-clause-aux-provedp todo done blimit rlimit control n))
  :hints(("Goal"
          :expand ((rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)
                   (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n))
          :in-theory (enable (:induction rw.crewrite-clause-aux-noacc)))))



(defthm consp-of-rw.crewrite-clause-aux-todo-primes
  (equal (consp (rw.crewrite-clause-aux-todo-primes todo done blimit rlimit control n))
         (consp todo))
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-aux-todo-primes))))

(defthm rw.ccstep->clause-prime-of-rw.crewrite-take-step
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)))
           (equal (rw.ccstep->clause-prime (rw.crewrite-take-step todo done blimit rlimit control n))
                  (if (rw.ccstep->provedp (rw.crewrite-take-step todo done blimit rlimit control n))
                      nil
                    (cons (rw.ccstep->t1prime (rw.crewrite-take-step todo done blimit rlimit control n))
                          (list-fix done)))))
  :hints(("Goal" :in-theory (e/d (rw.ccstep->clause-prime
                                  rw.ccstep->provedp
                                  rw.ccstep->t1prime
                                  rw.crewrite-take-step)))))

(defthm rw.crewrite-clause-aux-todo-primes-correct
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (consp todo)
                       (rw.controlp control)
                       (not (rw.crewrite-clause-aux-provedp todo done blimit rlimit control n))))
           (equal (rw.ccstep->clause-prime
                   (car (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n)))
                  (app (rev (rw.crewrite-clause-aux-todo-primes todo done blimit rlimit control n))
                       done)))
  :hints(("Goal"
          :induct (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n)
          :expand ((rw.crewrite-clause-aux-todo-primes todo done blimit rlimit control n)
                   (rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)
                   (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n))
          :in-theory (enable (:induction rw.crewrite-clause-aux-noacc)))))



(defthm true-listp-of-rw.crewrite-clause-aux-fgoals
  (equal (true-listp (rw.crewrite-clause-aux-fgoals todo done blimit rlimit control n))
         t)
  :hints(("Goal" :in-theory (enable rw.crewrite-clause-aux-fgoals))))

(defthm rw.crewrite-clause-aux-fgoals-correct
  (equal (rw.ccstep-list-forced-goals (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n))
         (rw.crewrite-clause-aux-fgoals todo done blimit rlimit control n))
  :hints(("Goal"
          :induct (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n)
          :expand ((rw.crewrite-clause-aux-fgoals todo done blimit rlimit control n)
                   (rw.crewrite-clause-aux-noacc todo done blimit rlimit control n))
          :in-theory (enable (:induction rw.crewrite-clause-aux-noacc)))))



;; We're now ready to present the fast version of crewrite-clause-aux.  Here,
;; we return (LIST PROVEDP CLAUSE-PRIME FGOALS).  We then show that this
;; function is correct with respect to our simplified vesions of what
;; rw.crewrite-clause-aux returns.

(defund rw.fast-crewrite-clause-aux (todo done blimit rlimit control n fgacc)
  ;; Note: redefined in interface/rewrite-tactics.lisp to add timing information
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n)
                              (true-listp fgacc))
                  :verify-guards nil))
  (if (consp todo)
      (let* ((step1          (rw.fast-crewrite-take-step todo done blimit rlimit control n))
             (step1-contr    (rw.fast-ccstep->contradictionp step1))
             (step1-provedp  (rw.fast-ccstep->provedp step1))
             (step1-ftrace   (rw.fast-ccstep->ftrace step1))
             (step1-fgoals   (and (not step1-contr)
                                  (rw.ftrace->fgoals step1-ftrace))))
        (if step1-provedp
            (list t nil (fast-app step1-fgoals fgacc))
          (rw.fast-crewrite-clause-aux (cdr todo)
                                       (cons (rw.fast-ccstep->t1prime step1) done)
                                       blimit rlimit control n
                                       (fast-app step1-fgoals fgacc))))
    (list nil done fgacc)))

(defthm provedp-of-rw.fast-crewrite-clause-aux
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (rw.controlp control)
                       (true-listp fgacc)))
           (equal (car (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
                  (rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)))
  :hints(("Goal"
          :induct (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc)
          :expand ((rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)
                   (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
          :in-theory (e/d ((:induction rw.fast-crewrite-clause-aux))
                          (rw.crewrite-clause-aux-provedp-correct)))))

(defthm clause-prime-of-rw.fast-crewrite-clause-aux
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (true-listp done)
                       (rw.controlp control)
                       (true-listp fgacc)))
           (equal (second (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
                  (if (rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)
                      nil
                    (app (rev (rw.crewrite-clause-aux-todo-primes todo done blimit rlimit control n))
                         done))))
  :hints(("Goal"
          :induct (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc)
          :expand ((rw.crewrite-clause-aux-provedp todo done blimit rlimit control n)
                   (rw.crewrite-clause-aux-todo-primes todo done blimit rlimit control n)
                   (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
          :in-theory (e/d ((:induction rw.fast-crewrite-clause-aux))
                          ()))))

(defthm forced-goals-of-rw.fast-crewrite-clause-aux
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (true-listp done)
                       (rw.controlp control)
                       (true-listp fgacc)))
           (equal (third (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
                  (app (rw.crewrite-clause-aux-fgoals todo done blimit rlimit control n)
                       fgacc)))
  :hints(("Goal"
          :induct (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc)
          :expand ((rw.crewrite-clause-aux-fgoals todo done blimit rlimit control n)
                   (rw.fast-crewrite-clause-aux todo done blimit rlimit control n fgacc))
          :in-theory (e/d ((:induction rw.fast-crewrite-clause-aux)
                           rw.ccstep-forced-goals)
                          ()))))

(verify-guards rw.fast-crewrite-clause-aux)




(defund rw.fast-crewrite-clause (clause blimit rlimit control n)
  ;; Note: redefined in interface/rewrite-tactics to add timing info
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n))))
  ;; Returns (LIST PROVEDP CLAUSE-PRIME FGOALS).  Immediately below, we show
  ;; below these are the same as the provedp, clause-prime, and fgoals produced
  ;; by rw.crewrite-clause.
  (rw.fast-crewrite-clause-aux clause nil blimit rlimit control n nil))

(defthm first-of-rw.fast-crewrite-clause
  (implies (force (and (logic.term-listp clause)
                       (rw.controlp control)))
           (equal (first (rw.fast-crewrite-clause clause blimit rlimit control n))
                  (rw.ccstep->provedp (car (rw.crewrite-clause clause blimit rlimit control n)))))
  :hints(("Goal" :in-theory (enable rw.fast-crewrite-clause
                                    rw.crewrite-clause
                                    rw.crewrite-clause-aux-removal))))

(defthm second-of-rw.fast-crewrite-clause
  (implies (force (and (logic.term-listp clause)
                       (consp clause)
                       (rw.controlp control)
                       ))
           (equal (second (rw.fast-crewrite-clause clause blimit rlimit control n))
                  (if (rw.ccstep->provedp (car (rw.crewrite-clause clause blimit rlimit control n)))
                      nil
                    (rw.ccstep->clause-prime (car (rw.crewrite-clause clause blimit rlimit control n))))))
  :hints(("Goal" :in-theory (enable rw.fast-crewrite-clause
                                    rw.crewrite-clause
                                    rw.crewrite-clause-aux-removal))))

(defthm third-of-rw.fast-crewrite-clause
  (implies (force (and (logic.term-listp clause)
                       (rw.controlp control)))
           (equal (third (rw.fast-crewrite-clause clause blimit rlimit control n))
                  (rw.ccstep-list-forced-goals (rw.crewrite-clause clause blimit rlimit control n))))
    :hints(("Goal" :in-theory (enable rw.fast-crewrite-clause
                                    rw.crewrite-clause
                                    rw.crewrite-clause-aux-removal))))

