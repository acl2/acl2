; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "ccsteps")
(include-book "crewrite")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm rw.ccstep->clause-prime-under-iff
  (iff (rw.ccstep->clause-prime x)
       (not (rw.ccstep->provedp x)))
  :hints(("Goal" :in-theory (enable rw.ccstep->clause-prime
                                    rw.ccstep->provedp))))

(defthm forcing-rw.eqtrace-okp-of-rw.assms->contradiction-and-rw.assms->hypbox-free
  ;; bozo move to assms
  (implies (and (equal free (rw.assms->hypbox x))
                (force (and (rw.assmsp x)
                            (rw.assms->contradiction x))))
           (equal (rw.eqtrace-okp (rw.assms->contradiction x) free)
                  t)))


(defthm forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-right
  (implies (force (and (rw.assmsp assms)
                       (rw.assms-atblp assms atbl)
                       (logic.termp nhyp)
                       (logic.term-atblp nhyp atbl)
                       (or (not (rw.assms->contradiction assms))
                           (rw.eqtrace-atblp (rw.assms->contradiction assms) atbl))
                       (rw.assms->contradiction (rw.assume-right nhyp assms))))
           (equal (rw.eqtrace-atblp (rw.assms->contradiction (rw.assume-right nhyp assms)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.assume-right))))

(defthm forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-right-list
  (implies (force (and (rw.assmsp assms)
                       (rw.assms-atblp assms atbl)
                       (logic.term-listp nhyps)
                       (logic.term-list-atblp nhyps atbl)
                       (or (not (rw.assms->contradiction assms))
                           (rw.eqtrace-atblp (rw.assms->contradiction assms) atbl))
                       (rw.assms->contradiction (rw.assume-right-list nhyps assms))
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (rw.eqtrace-atblp (rw.assms->contradiction (rw.assume-right-list nhyps assms)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.assume-right-list))))

(defthm forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-left
  (implies (force (and (rw.assmsp assms)
                       (rw.assms-atblp assms atbl)
                       (logic.termp nhyp)
                       (logic.term-atblp nhyp atbl)
                       (or (not (rw.assms->contradiction assms))
                           (rw.eqtrace-atblp (rw.assms->contradiction assms) atbl))
                       (rw.assms->contradiction (rw.assume-left nhyp assms))))
           (equal (rw.eqtrace-atblp (rw.assms->contradiction (rw.assume-left nhyp assms)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.assume-left))))

(defthm forcing-rw.eqtrace-atblp-of-rw.assms->contradiction-of-rw.assume-left-list
  (implies (force (and (rw.assmsp assms)
                       (rw.assms-atblp assms atbl)
                       (logic.term-listp nhyps)
                       (logic.term-list-atblp nhyps atbl)
                       (or (not (rw.assms->contradiction assms))
                           (rw.eqtrace-atblp (rw.assms->contradiction assms) atbl))
                       (rw.assms->contradiction (rw.assume-left-list nhyps assms))
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (rw.eqtrace-atblp (rw.assms->contradiction (rw.assume-left-list nhyps assms)) atbl)
                  t))
  :hints(("Goal" :in-theory (enable rw.assume-left-list))))





;; Taking steps
;;
;; It is straightforward to take an individual step and create the ccstep
;; record of it.

(defsection rw.crewrite-take-step

  (definlined rw.crewrite-take-step (todo done blimit rlimit control n)
    (declare (xargs :guard (and (consp todo)
                                (logic.term-listp todo)
                                (logic.term-listp done)
                                (natp blimit)
                                (natp rlimit)
                                (rw.controlp control)
                                (natp n))))
    (let* ((assms (rw.empty-assms (rw.control->assmctrl control)))
           (assms (rw.assume-left-list (cdr todo) assms))
           (assms (rw.assume-right-list done assms))
           (contr (rw.assms->contradiction assms)))
      (rw.ccstep (car todo)
                 (rw.assms->hypbox assms)
                 contr
                 (if (not contr)
                     (rw.crewrite assms (car todo) t blimit rlimit control n)
                   nil))))

  (local (in-theory (enable rw.crewrite-take-step)))

  (defthm forcing-rw.ccstepp-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)))
             (equal (rw.ccstepp (rw.crewrite-take-step todo done blimit rlimit control n))
                    t)))

  (defthm forcing-rw.trace-okp-of-rw.ccstep->trace-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)))
             (equal (rw.trace-okp (rw.ccstep->trace (rw.crewrite-take-step todo done blimit rlimit control n))
                                  (rw.control->defs control))
                    (not (rw.ccstep->contradiction (rw.crewrite-take-step todo done blimit rlimit control n))))))

  (defthm forcing-rw.trace-atblp-of-rw.ccstep->trace-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.trace-atblp (rw.ccstep->trace (rw.crewrite-take-step todo done blimit rlimit control n)) atbl)
                    (not (rw.ccstep->contradiction (rw.crewrite-take-step todo done blimit rlimit control n))))))

  (defthm forcing-rw.ccstep-trace-env-okp-of-rw.ccstep->trace-of-rw.crewrite-take-step
    (implies (and (consp todo)
                  (logic.term-listp todo)
                  (logic.term-listp done)
                  (rw.controlp control)
                  (logic.term-list-atblp todo atbl)
                  (logic.term-list-atblp done atbl)
                  (rw.control-atblp control atbl)
                  (rw.control-env-okp control axioms thms)
                  (equal (cdr (lookup 'not atbl)) 1))
             (equal (rw.trace-env-okp (rw.ccstep->trace (rw.crewrite-take-step todo done blimit rlimit control n))
                                      (rw.control->defs control)
                                      thms atbl)
                    t)))

  (defthm forcing-rw.eqtrace-atblp-of-rw.ccstep->contradiction-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.eqtrace-atblp (rw.ccstep->contradiction (rw.crewrite-take-step todo done blimit rlimit control n)) atbl)
                    (if (rw.ccstep->contradiction (rw.crewrite-take-step todo done blimit rlimit control n))
                        t
                      nil))))

  (defthm forcing-logic.term-atblp-of-rw.ccstep->term-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (rw.controlp control)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (logic.term-list-atblp todo atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (logic.term-atblp (rw.ccstep->term (rw.crewrite-take-step todo done blimit rlimit control n)) atbl)
                    t)))

  (defthm forcing-rw.hypbox-atblp-of-rw.ccstep->hypbox-of-rw.crewrite-take-step
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.hypbox-atblp (rw.ccstep->hypbox (rw.crewrite-take-step todo done blimit rlimit control n)) atbl)
                    t))))




;; Rewriting the clause
;;
;; We now are finally ready to introduce our main function, which takes steps
;; until it the clause is proved or has been entirely rewritten.

(defsection rw.crewrite-clause-aux

  (defund rw.crewrite-clause-aux (todo done blimit rlimit control n acc)
    (declare (xargs :guard (and (logic.term-listp todo)
                                (logic.term-listp done)
                                (natp blimit)
                                (natp rlimit)
                                (rw.controlp control)
                                (natp n)
                                (rw.ccstep-listp acc))))
    (if (consp todo)
        (let ((step1 (rw.crewrite-take-step todo done blimit rlimit control n)))
          (if (rw.ccstep->provedp step1)
              (cons step1 acc)
            (rw.crewrite-clause-aux (cdr todo)
                                    (cons (rw.ccstep->t1prime step1) done)
                                    blimit rlimit control n
                                    (cons step1 acc))))
      acc))

  (defobligations rw.crewrite-clause-aux
    (rw.crewrite-take-step))

  (local (in-theory (enable rw.crewrite-clause-aux
                            rw.ccstep->provedp)))

  (defthm consp-of-rw.crewrite-clause-aux
    (equal (consp (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
           (or (consp todo)
               (consp acc))))

  (defthm forcing-rw.ccstep-listp-of-rw.crewrite-clause-aux
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)))
             (equal (rw.ccstep-listp (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
                    t)))

  (defthm forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)
                         (rw.trace-list-okp (rw.ccstep-list-gather-traces acc) (rw.control->defs control))))
             (equal (rw.trace-list-okp (rw.ccstep-list-gather-traces (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
                                       (rw.control->defs control))
                    t)))

  (defthm forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)
                         (rw.trace-list-atblp (rw.ccstep-list-gather-traces acc) atbl)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.trace-list-atblp (rw.ccstep-list-gather-traces (rw.crewrite-clause-aux todo done blimit rlimit control n acc)) atbl)
                    t)))

  (defthm forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-aux
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)
                         (rw.trace-list-atblp (rw.ccstep-list-gather-traces acc) atbl)
                         (rw.trace-list-env-okp (rw.ccstep-list-gather-traces acc)
                                                (rw.control->defs control)
                                                thms atbl)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (rw.control-atblp control atbl)
                         (rw.control-env-okp control axioms thms)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.trace-list-env-okp (rw.ccstep-list-gather-traces
                                            (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
                                           (rw.control->defs control)
                                           thms atbl)
                    t)))

  (local (defthm lemma
           (implies (and (consp todo)
                         (consp (cdr todo))
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (not (rw.ccstep->provedp (rw.crewrite-take-step todo done blimit rlimit control n))))
                    (equal
                     (rw.ccstep->result-goal
                      (rw.crewrite-take-step todo done blimit rlimit control n))
                     (rw.ccstep->original-goal
                      (rw.crewrite-take-step (cdr todo)
                                             (cons (rw.ccstep->t1prime
                                                    (rw.crewrite-take-step todo done blimit rlimit control n))
                                                   done)
                                             blimit rlimit control n))))
           :hints(("Goal"
                   :in-theory (enable rw.crewrite-take-step
                                      rw.ccstep->result-goal
                                      rw.ccstep->original-goal
                                      rw.ccstep->t1prime
                                      rw.ccstep->provedp)
                   :do-not-induct t))))

  (defthm forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause-aux
    (implies (force (and (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)
                         (rw.ccstep-list->compatiblep acc)
                         ;; ---
                         (or (not (consp todo))
                             (not (consp acc))
                             (and (not (rw.ccstep->provedp (first acc)))
                                  (equal (rw.ccstep->result-goal (first acc))
                                         (rw.ccstep->original-goal
                                          (rw.crewrite-take-step todo done blimit rlimit control n)))))))
             (equal (rw.ccstep-list->compatiblep (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
                    t))
    :hints(("Goal"
            :induct (rw.crewrite-clause-aux todo done blimit rlimit control n acc)
            :in-theory (enable rw.ccstep-list->compatiblep)
            :do-not-induct t)))

  (defthm forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause-aux
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)
                         (rw.ccstep-listp acc)))
             (equal (rw.ccstep-list->original-goal (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
                    (if (consp acc)
                        (rw.ccstep-list->original-goal acc)
                      (rw.ccstep->original-goal
                       (rw.crewrite-take-step todo done blimit rlimit control n)))))
    :hints(("Goal"
            :induct (rw.crewrite-clause-aux todo done blimit rlimit control n acc)
            :in-theory (enable rw.ccstep-list->original-goal))))

;;   (defthm forcing-consp-of-rw.crewrite-clause-aux
;;     (implies (force (consp todo))
;;              (equal (consp (rw.crewrite-clause-aux todo done blimit rlimit control n acc))
;;                     t)))

  (local (defthm lemma2
           (implies (force (and (rw.controlp control)
                                (logic.term-listp todo)
                                (logic.term-listp done)))
                    (iff (rw.hypbox->left (rw.ccstep->hypbox (rw.crewrite-take-step todo done blimit rlimit control n)))
                         (consp (cdr todo))))
           :hints(("Goal" :in-theory (enable rw.crewrite-take-step)))))

  (defthm forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause-aux
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (rw.controlp control)))
             (equal (rw.ccstep->terminalp (car (rw.crewrite-clause-aux todo done blimit rlimit control n acc)))
                    t))
    :hints(("Goal"
            :induct (rw.crewrite-clause-aux todo done blimit rlimit control n acc)
            :in-theory (enable rw.ccstep->terminalp
                               rw.ccstep->provedp)
            :do-not-induct t)))

  (defthm forcing-rw.eqtrace-list-atblp-of-rw.ccstep-list-gather-contradictions-of-rw.crewrite-clause-aux
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions acc) atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions (rw.crewrite-clause-aux todo done blimit rlimit control n acc)) atbl)
                    t)))

  (defthm forcing-logic.term-list-atblp-of-rw.ccstep-list-terms-of-rw.crewrite-clause-aux
    (implies (force (and (consp todo)
                         (rw.controlp control)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp (rw.ccstep-list-terms acc) atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (logic.term-list-atblp (rw.ccstep-list-terms (rw.crewrite-clause-aux todo done blimit rlimit control n acc)) atbl)
                    t)))

  (defthm forcing-rw.hypbox-list-atblp-of-rw.ccstep-list-hypboxes-of-rw.crewrite-clause-aux
    (implies (force (and (consp todo)
                         (logic.term-listp todo)
                         (logic.term-listp done)
                         (logic.term-list-atblp todo atbl)
                         (logic.term-list-atblp done atbl)
                         (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes acc) atbl)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes (rw.crewrite-clause-aux todo done blimit rlimit control n acc)) atbl)
                    t))))



(defsection rw.crewrite-clause

  (definlined rw.crewrite-clause (clause blimit rlimit control n)
    ;; This is just a simple wrapper for crewrite-clause-aux
    (declare (xargs :guard (and (logic.term-listp clause)
                                (consp clause)
                                (natp blimit)
                                (natp rlimit)
                                (rw.controlp control)
                                (natp n))))
    (rw.crewrite-clause-aux clause nil blimit rlimit control n nil))

  (defobligations rw.crewrite-clause
    (rw.crewrite-clause-aux))

  (local (in-theory (enable rw.crewrite-clause)))

  (defthm forcing-rw.ccstep-listp-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.ccstep-listp (rw.crewrite-clause clause blimit rlimit control n))
                    t)))

  (defthm forcing-rw.ccstep-listp-of-rw.crewrite-clause-free
    (implies (and (equal free (rw.crewrite-clause clause blimit rlimit control n))
                  (force (and (logic.term-listp clause)
                              (consp clause)
                              (rw.controlp control))))
             (equal (rw.ccstep-listp free)
                    t)))

  (defthm forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.trace-list-okp (rw.ccstep-list-gather-traces (rw.crewrite-clause clause blimit rlimit control n))
                                       (rw.control->defs control))
                    t)))

  (defthm forcing-rw.trace-list-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free
    (implies (and (equal free (rw.crewrite-clause clause blimit rlimit control n))
                  (force (and (logic.term-listp clause)
                              (consp clause)
                              (rw.controlp control))))
             (equal (rw.trace-list-okp (rw.ccstep-list-gather-traces free) (rw.control->defs control))
                    t)))

  (defthm forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (logic.term-list-atblp clause atbl)
                         (consp clause)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.trace-list-atblp (rw.ccstep-list-gather-traces (rw.crewrite-clause clause blimit rlimit control n)) atbl)
                    t)))

  (defthm forcing-rw.trace-list-atblp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free
    (implies (and (equal free (rw.crewrite-clause clause blimit rlimit control n))
                  (force (and (logic.term-listp clause)
                              (logic.term-list-atblp clause atbl)
                              (consp clause)
                              (rw.controlp control)
                              (rw.control-atblp control atbl)
                              (equal (cdr (lookup 'not atbl)) 1))))
             (equal (rw.trace-list-atblp (rw.ccstep-list-gather-traces free) atbl)
                    t)))

  (defthm forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (logic.term-list-atblp clause atbl)
                         (consp clause)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (rw.control-env-okp control axioms thms)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.trace-list-env-okp (rw.ccstep-list-gather-traces (rw.crewrite-clause clause blimit rlimit control n))
                                           (rw.control->defs control)
                                           thms atbl)
                    t)))

  (defthm forcing-rw.trace-list-env-okp-of-rw.ccstep-list-gather-traces-of-rw.crewrite-clause-free
    (implies (and (equal free (rw.crewrite-clause clause blimit rlimit control n))
                  (force (and (logic.term-listp clause)
                              (logic.term-list-atblp clause atbl)
                              (consp clause)
                              (rw.controlp control)
                              (rw.control-atblp control atbl)
                              (rw.control-env-okp control axioms thms)
                              (equal (cdr (lookup 'not atbl)) 1))))
             (equal (rw.trace-list-env-okp (rw.ccstep-list-gather-traces free)
                                           (rw.control->defs control)
                                           thms atbl)
                    t)))

  (defthm forcing-rw.ccstep-list->compatiblep-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.ccstep-list->compatiblep (rw.crewrite-clause clause blimit rlimit control n))
                    t))
    :hints(("Goal" :in-theory (enable rw.crewrite-clause))))

  (local (defthm lemma
           (implies (force (and (logic.term-listp clause)
                                (rw.controlp control)
                                (consp clause)))
                    (equal (rw.ccstep->original-goal (rw.crewrite-take-step clause nil blimit rlimit control n))
                           (clause.clause-formula clause)))
           :hints(("Goal" :in-theory (enable rw.ccstep->original-goal
                                             rw.crewrite-take-step)))))

  (defthm forcing-rw.ccstep-list->original-goal-of-rw.crewrite-clause
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.ccstep-list->original-goal (rw.crewrite-clause clause blimit rlimit control n))
                    (clause.clause-formula clause))))

  (defthm forcing-consp-of-rw.crewrite-clause
    (implies (force (consp clause))
             (equal (consp (rw.crewrite-clause clause blimit rlimit control n))
                    t)))

  (local (defthm lemma2
           (implies (and (not (rw.ccstep->provedp (car (rw.crewrite-clause clause blimit rlimit control n))))
                         (force (and (logic.term-listp clause)
                                     (consp clause)
                                     (rw.controlp control))))
                    (equal (rw.ccstep->result-goal (car (rw.crewrite-clause clause blimit rlimit control n)))
                           (clause.clause-formula
                            (rw.ccstep->clause-prime
                             (car (rw.crewrite-clause clause blimit rlimit control n))))))
           :hints(("Goal" :in-theory (enable rw.crewrite-clause)))))

  (defthm forcing-rw.ccstep->result-goal-of-car-of-cdr-of-rw.crewrite-clause
    (implies (force (and (not (rw.ccstep->provedp (car (rw.crewrite-clause clause blimit rlimit control n))))
                         (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)))
             (equal (rw.ccstep->result-goal (car (rw.crewrite-clause clause blimit rlimit control n)))
                    (clause.clause-formula
                     (rw.ccstep->clause-prime
                      (car (rw.crewrite-clause clause blimit rlimit control n)))))))

  (defthm forcing-rw.ccstep->terminalp-of-car-of-rw.crewrite-clause
    (implies (force (and (consp clause)
                         (force (logic.term-listp clause))
                         (force (rw.controlp control))))
             (equal (rw.ccstep->terminalp (car (rw.crewrite-clause clause blimit rlimit control n)))
                    t)))

  (defthm forcing-rw.eqtrace-list-atblp-of-rw.ccstep-list-gather-contradictions-of-rw.crewrite-clause
    (implies (force (and (consp clause)
                         (logic.term-listp clause)
                         (logic.term-list-atblp clause atbl)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions (rw.crewrite-clause clause blimit rlimit control n)) atbl)
                    t)))

  (defthm forcing-logic.term-list-atblp-of-rw.ccstep-list-terms-of-rw.crewrite-clause
    (implies (force (and (consp clause)
                         (rw.controlp control)
                         (logic.term-listp clause)
                         (logic.term-list-atblp clause atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (logic.term-list-atblp (rw.ccstep-list-terms (rw.crewrite-clause clause blimit rlimit control n)) atbl)
                    t)))

  (defthm forcing-rw.hypbox-list-atblp-of-rw.ccstep-list-hypboxes-of-rw.crewrite-clause
    (implies (force (and (consp clause)
                         (logic.term-listp clause)
                         (logic.term-list-atblp clause atbl)
                         (rw.controlp control)
                         (rw.control-atblp control atbl)
                         (equal (cdr (lookup 'not atbl)) 1)))
             (equal (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes (rw.crewrite-clause clause blimit rlimit control n)) atbl)
                    t))))




(defsection rw.crewrite-clause-bldr

  (defund rw.crewrite-clause-bldr (clause blimit rlimit control n record proof fproofs)
    ;; Prove the clause given:
    ;;  - the same arguments as rw.crewrite-clause,
    ;;  - the record produced by rw.crewrite-clause,
    ;;  - a proof of the clause-prime it produced (if it was nonempty), and
    ;;  - proofs of all the forced goals from the clause-prime
    (declare (xargs :guard (and (logic.term-listp clause)
                                (consp clause)
                                (natp blimit)
                                (natp rlimit)
                                (rw.controlp control)
                                (natp n)
                                (equal record (rw.crewrite-clause clause blimit rlimit control n))
                                (if (not (rw.ccstep->provedp (car record)))
                                    (and (logic.appealp proof)
                                         (equal (logic.conclusion proof)
                                                (clause.clause-formula (rw.ccstep->clause-prime (car record)))))
                                  (not proof))
                                (logic.appeal-listp fproofs)
                                (subsetp (rw.ccstep-list-forced-goals record) (logic.strip-conclusions fproofs)))
                    :verify-guards nil))
    (declare (ignore clause blimit rlimit n))
    (rw.ccstep-list-bldr record (rw.control->defs control) proof fproofs))

  (defobligations rw.crewrite-clause-bldr
    (rw.crewrite-clause
     rw.ccstep-list-bldr))

  (local (in-theory (enable rw.crewrite-clause-bldr)))

  (verify-guards rw.crewrite-clause-bldr)

  (defthm forcing-logic.appealp-of-rw.crewrite-clause-bldr
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)
                         (equal record (rw.crewrite-clause clause blimit rlimit control n))
                         (if (not (rw.ccstep->provedp (car record)))
                             (and (logic.appealp proof)
                                  (equal (logic.conclusion proof)
                                         (clause.clause-formula (rw.ccstep->clause-prime (car record)))))
                           (not proof))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals record) (logic.strip-conclusions fproofs))))
             (equal (logic.appealp (rw.crewrite-clause-bldr clause blimit rlimit control n record proof fproofs))
                    t)))

  (defthm forcing-logic.conclusion-of-rw.crewrite-clause-bldr
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)
                         (equal record (rw.crewrite-clause clause blimit rlimit control n))
                         (if (not (rw.ccstep->provedp (car record)))
                             (and (logic.appealp proof)
                                  (equal (logic.conclusion proof)
                                         (clause.clause-formula (rw.ccstep->clause-prime (car record)))))
                           (not proof))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals record) (logic.strip-conclusions fproofs))))
             (equal (logic.conclusion (rw.crewrite-clause-bldr clause blimit rlimit control n record proof fproofs))
                    (clause.clause-formula clause)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm@ forcing-logic.proofp-of-rw.crewrite-clause-bldr
    (implies (force (and (logic.term-listp clause)
                         (consp clause)
                         (rw.controlp control)
                         (equal record (rw.crewrite-clause clause blimit rlimit control n))
                         (if (not (rw.ccstep->provedp (car record)))
                             (and (logic.appealp proof)
                                  (equal (logic.conclusion proof)
                                         (clause.clause-formula (rw.ccstep->clause-prime (car record))))
                                  ;; ---
                                  (logic.proofp proof axioms thms atbl))
                           (not proof))
                         (logic.appeal-listp fproofs)
                         (subsetp (rw.ccstep-list-forced-goals record) (logic.strip-conclusions fproofs))
                         ;; ---
                         (logic.proof-listp fproofs axioms thms atbl)
                         (logic.term-list-atblp clause atbl)
                         (rw.control-atblp control atbl)
                         (rw.control-env-okp control axioms thms)
                         (equal (cdr (lookup 'not atbl)) 1)
                         (equal (cdr (lookup 'equal atbl)) 2)
                         (equal (cdr (lookup 'iff atbl)) 2)
                         (equal (cdr (lookup 'if atbl)) 3)
                         (@obligations rw.crewrite-clause-bldr)))
             (equal (logic.proofp (rw.crewrite-clause-bldr clause blimit rlimit control n record proof fproofs) axioms thms atbl)
                    t))))




(defprojection :list (rw.crewrite-clause-list x blimit rlimit control n)
               :element (rw.crewrite-clause x blimit rlimit control n)
               :guard (and (logic.term-list-listp x)
                           (cons-listp x)
                           (natp blimit)
                           (natp rlimit)
                           (rw.controlp control)
                           (natp n)))

(defthm forcing-cons-listp-of-rw.crewrite-clause-list
  (implies (force (cons-listp x))
           (equal (cons-listp (rw.crewrite-clause-list x blimit rlimit control n))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.ccstep-list-listp-of-rw.crewrite-clause-list
  (implies (force (and (logic.term-list-listp x)
                       (cons-listp x)
                       (rw.controlp control)))
           (equal (rw.ccstep-list-listp (rw.crewrite-clause-list x blimit rlimit control n))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.ccstep-list-listp-of-rw.crewrite-clause-list-free
  (implies (and (equal free (rw.crewrite-clause-list x blimit rlimit control n))
                (force (and (logic.term-list-listp x)
                            (cons-listp x)
                            (rw.controlp control))))
           (equal (rw.ccstep-list-listp free)
                  t)))

(defthm forcing-rw.trace-list-atblp-of-rw.ccstep-list-list-gather-traces-of-rw.crewrite-clause-list
  (implies (force (and (logic.term-list-listp x)
                       (logic.term-list-list-atblp x atbl)
                       (cons-listp x)
                       (rw.controlp control)
                       (rw.control-atblp control atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (rw.trace-list-atblp (rw.ccstep-list-list-gather-traces (rw.crewrite-clause-list x blimit rlimit control n)) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-rw.trace-list-atblp-of-rw.ccstep-list-list-gather-traces-of-rw.crewrite-clause-list-free
  (implies (and (equal free (rw.crewrite-clause-list x blimit rlimit control n))
                (force (and (logic.term-list-listp x)
                            (logic.term-list-list-atblp x atbl)
                            (cons-listp x)
                            (rw.controlp control)
                            (rw.control-atblp control atbl)
                            (equal (cdr (lookup 'not atbl)) 1))))
           (equal (rw.trace-list-atblp (rw.ccstep-list-list-gather-traces free) atbl)
                  t)))



(defund rw.ccstep-list-list-terminalp (x)
  (declare (xargs :guard (and (rw.ccstep-list-listp x)
                              (cons-listp x))))
  (if (consp x)
      (and (rw.ccstep->terminalp (car (car x)))
           (rw.ccstep-list-list-terminalp (cdr x)))
    t))

(defthm rw.ccstep-list-list-terminalp-when-not-consp
  (implies (not (consp x))
           (equal (rw.ccstep-list-list-terminalp x)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-terminalp))))

(defthm rw.ccstep-list-list-terminalp-of-cons
  (equal (rw.ccstep-list-list-terminalp (cons a x))
         (and (rw.ccstep->terminalp (car a))
              (rw.ccstep-list-list-terminalp x)))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-terminalp))))

(defthm rw.ccstep-list-list-terminalp-of-rw.crewrite-clause-list
  (implies (force (and (cons-listp x)
                       (logic.term-list-listp x)
                       (rw.controlp control)))
           (equal (rw.ccstep-list-list-terminalp (rw.crewrite-clause-list x blimit rlimit control n))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defund rw.ccstep-list-list-obligations (x)
  (declare (xargs :guard (and (rw.ccstep-list-listp x)
                              (cons-listp x)
                              (rw.ccstep-list-list-terminalp x))))
  (if (consp x)
      (let* ((entry1       (car x))
             (entry1-step1 (car entry1)))
        (if (rw.ccstep->provedp entry1-step1)
            (rw.ccstep-list-list-obligations (cdr x))
          (cons (rw.ccstep->clause-prime entry1-step1)
                (rw.ccstep-list-list-obligations (cdr x)))))
    nil))

(defthm true-listp-of-rw.ccstep-list-list-obligations
  (equal (true-listp (rw.ccstep-list-list-obligations x))
         t)
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-obligations))))

(defthm forcing-cons-listp-of-rw.ccstep-list-list-obligations
  (implies (force (and (rw.ccstep-list-listp x)
                       (cons-listp x)))
           (equal (cons-listp (rw.ccstep-list-list-obligations x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-obligations))))

(defthm forcing-logic.term-list-listp-of-rw.ccstep-list-list-obligations
  (implies (force (and (rw.ccstep-list-listp x)
                       (cons-listp x)))
           (equal (logic.term-list-listp (rw.ccstep-list-list-obligations x))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-obligations))))

(defthm forcing-logic.term-list-listp-of-rw.ccstep-list-list-obligations-free
; Matt K. mod for v7-2: Don't force assumption below with free variable.
  (implies (and (equal free (rw.ccstep-list-list-obligations x))
                (force (rw.ccstep-list-listp x))
                (force (cons-listp x)))
           (equal (logic.term-list-listp free)
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-list-obligations))))


(defund rw.crewrite-clause-list-bldr (clauses blimit rlimit control n results proofs fproofs)
  ;; Prove clauses given:
  ;;  - the same arguments as rw.crewrite-clause-list,
  ;;  - the results it produced,
  ;;  - proofs of the obligations for its results
  (declare (xargs :guard (and (logic.term-list-listp clauses)
                              (cons-listp clauses)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n)
                              (equal results (rw.crewrite-clause-list clauses blimit rlimit control n))
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (clause.clause-list-formulas (rw.ccstep-list-list-obligations results)))
                              (logic.appeal-listp fproofs)
                              (subsetp (rw.ccstep-list-list-forced-goals results)
                                       (logic.strip-conclusions fproofs)))
                  :verify-guards nil))
  (if (consp clauses)
      (let* ((entry1       (car results))
             (entry1-step1 (car entry1)))
        (if (rw.ccstep->provedp entry1-step1)
            ;; We proved clause1 directly; use nil as its input proof
            (cons (ACL2::prog2$ (ACL2::cw! ";; Compiling winning rewrite for clause ~x0.~%" (fast-len clauses 0))
                                (rw.crewrite-clause-bldr (car clauses) blimit rlimit control n entry1 nil fproofs))
                  (rw.crewrite-clause-list-bldr (cdr clauses) blimit rlimit control n (cdr results) proofs fproofs))
          ;; We need the input proof to prove clause1
          (cons (ACL2::prog2$ (ACL2::cw! ";; Compiling rewrite for clause ~x0.~%" (fast-len clauses 0))
                              (rw.crewrite-clause-bldr (car clauses) blimit rlimit control n entry1 (car proofs) fproofs))
                (rw.crewrite-clause-list-bldr (cdr clauses) blimit rlimit control n (cdr results) (cdr proofs) fproofs))))
    nil))

(defobligations rw.crewrite-clause-list-bldr
  (rw.crewrite-clause-bldr))

(encapsulate
 ()
 (local (in-theory (enable rw.crewrite-clause-list-bldr
                           rw.ccstep-list-list-obligations)))

 (verify-guards rw.crewrite-clause-list-bldr)

 (defthm forcing-logic.appeal-listp-of-rw.crewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp clauses)
                        (cons-listp clauses)
                        (rw.controlp control)
                        (equal results (rw.crewrite-clause-list clauses blimit rlimit control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.ccstep-list-list-obligations results)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.ccstep-list-list-forced-goals results)
                                 (logic.strip-conclusions fproofs))))
            (equal (logic.appeal-listp (rw.crewrite-clause-list-bldr clauses blimit rlimit control n results proofs fproofs))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-rw.crewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp clauses)
                        (cons-listp clauses)
                        (rw.controlp control)
                        (equal results (rw.crewrite-clause-list clauses blimit rlimit control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.ccstep-list-list-obligations results)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.ccstep-list-list-forced-goals results)
                                 (logic.strip-conclusions fproofs))))
            (equal (logic.strip-conclusions (rw.crewrite-clause-list-bldr clauses blimit rlimit control n results proofs fproofs))
                   (clause.clause-list-formulas clauses)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-rw.crewrite-clause-list-bldr
   (implies (force (and (logic.term-list-listp clauses)
                        (cons-listp clauses)
                        (rw.controlp control)
                        (equal results (rw.crewrite-clause-list clauses blimit rlimit control n))
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs)
                               (clause.clause-list-formulas (rw.ccstep-list-list-obligations results)))
                        (logic.appeal-listp fproofs)
                        (subsetp (rw.ccstep-list-list-forced-goals results)
                                 (logic.strip-conclusions fproofs))
                        ;; ---
                        (logic.term-list-list-atblp clauses atbl)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)
                        (logic.proof-listp proofs axioms thms atbl)
                        (logic.proof-listp fproofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations rw.crewrite-clause-list-bldr)))
            (equal (logic.proof-listp (rw.crewrite-clause-list-bldr clauses blimit rlimit control n results proofs fproofs) axioms thms atbl)
                   t))))



(defund rw.crewrite-records-show-progressp (original-goals new-obligations)
  (declare (xargs :guard (and (logic.term-list-listp original-goals)
                              (cons-listp original-goals)
                              (logic.term-list-listp new-obligations)
                              (cons-listp new-obligations))))
  ;; If rewriting fails to make any progress, then it leaves each clause intact
  ;; but reversed.  So, we see if new-obligations are the same as original-goals,
  ;; except that each is reversed.
  (if (consp original-goals)
      (or (not (consp new-obligations))
          (not (equal (fast-rev (car new-obligations)) (car original-goals)))
          (rw.crewrite-records-show-progressp (cdr original-goals) (cdr new-obligations)))
    nil))


