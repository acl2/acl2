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
(include-book "assms/eqtrace-arities")
(include-book "traces/trace-arities")
(include-book "ccsteps")
(set-verify-guards-eagerness 2)
(set-measure-function rank)
(set-well-founded-relation ord<)
(set-case-split-limitations nil)



(defund rw.faster-ccstepp (x)
  (declare (xargs :guard t))
  (let ((term (car (car x)))
        (hypbox (cdr (car x)))
        (contradiction (car (cdr x)))
        (trace (cdr (cdr x))))
    (and (logic.termp term)
         (rw.faster-hypboxp hypbox)
         (if contradiction
             (and (rw.eqtracep contradiction)
                  (rw.eqtrace-contradictionp contradiction)
                  (rw.eqtrace-okp contradiction hypbox)
                  (not trace))
           (and (rw.faster-tracep trace hypbox)
                (rw.trace->iffp trace)
                (equal (rw.trace->hypbox trace) hypbox)
                (equal (rw.trace->lhs trace) term))))))

(defthm rw.faster-ccstep-removal
  (equal (rw.faster-ccstepp x)
         (rw.ccstepp x))
  :hints(("Goal" :in-theory (enable rw.ccstepp rw.faster-ccstepp))))

(defund rw.faster-ccstep-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (rw.faster-ccstepp (car x))
           (rw.faster-ccstep-listp (cdr x)))
    t))

(defthm rw.faster-ccstep-list-removal
  (equal (rw.faster-ccstep-listp x)
         (rw.ccstep-listp x))
  :hints(("Goal" :in-theory (enable rw.faster-ccstep-listp))))




(defund rw.slow-ccstep-arities (x)
  (declare (xargs :guard (rw.ccstepp x)))
  (let* ((term          (rw.ccstep->term x))
         (hypbox        (rw.ccstep->hypbox x))
         (contradiction (rw.ccstep->contradiction x))
         (acc           (logic.slow-term-arities term))
         (acc           (app (rw.slow-hypbox-arities hypbox) acc)))
    (if contradiction
        (app (rw.slow-eqtrace-arities contradiction) acc)
      (app (rw.slow-faster-trace-arities (rw.ccstep->trace x) hypbox) acc))))

(defthm rw.slow-ccsteps-arities-correct
  (implies (force (rw.ccstepp x))
           (equal (logic.arities-okp (rw.slow-ccstep-arities x) atbl)
                  (and (logic.term-atblp (rw.ccstep->term x) atbl)
                       (rw.hypbox-atblp (rw.ccstep->hypbox x) atbl)
                       (if (rw.ccstep->contradiction x)
                           (rw.eqtrace-atblp (rw.ccstep->contradiction x) atbl)
                         (rw.trace-atblp (rw.ccstep->trace x) atbl)))))
  :hints(("Goal" :in-theory (e/d (rw.slow-ccstep-arities)
                                 ((:executable-counterpart acl2::force))))))



(defund rw.ccstep-arities (x acc)
  (declare (xargs :guard (and (rw.ccstepp x)
                              (true-listp acc))))
  (let* ((term          (rw.ccstep->term x))
         (hypbox        (rw.ccstep->hypbox x))
         (contradiction (rw.ccstep->contradiction x))
         (acc           (logic.term-arities term acc))
         (acc           (rw.hypbox-arities hypbox acc)))
    (if contradiction
        (rw.eqtrace-arities contradiction acc)
      (rw.faster-flag-trace-arities 'term (rw.ccstep->trace x) hypbox acc))))

(defthm rw.cstep-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.ccstep-arities x acc)
                  (app (rw.slow-ccstep-arities x) acc)))
  :hints(("Goal"
          :in-theory (enable rw.ccstep-arities rw.slow-ccstep-arities))))



(defund rw.slow-ccstep-list-arities (x)
  (declare (xargs :guard (rw.ccstep-listp x)))
  (if (consp x)
      (app (rw.slow-ccstep-arities (car x))
           (rw.slow-ccstep-list-arities (cdr x)))
    nil))

(defthm rw.slow-ccstep-list-arities-correct
  (implies (force (rw.ccstep-listp x))
           (equal (logic.arities-okp (rw.slow-ccstep-list-arities x) atbl)
                  (and (logic.term-list-atblp (rw.ccstep-list-terms x) atbl)
                       (rw.hypbox-list-atblp (rw.ccstep-list-hypboxes x) atbl)
                       (rw.eqtrace-list-atblp (rw.ccstep-list-gather-contradictions x) atbl)
                       (rw.trace-list-atblp (rw.ccstep-list-gather-traces x) atbl))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.slow-ccstep-list-arities x)))))



(defund rw.ccstep-list-arities (x acc)
  (declare (xargs :guard (and (rw.ccstep-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.ccstep-arities (car x)
                         (rw.ccstep-list-arities (cdr x) acc))
    acc))

(defthm true-listp-of-rw.ccstep-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.ccstep-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.ccstep-list-arities))))

(defthm rw.ccstep-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.ccstep-list-arities x acc)
                  (app (rw.slow-ccstep-list-arities x) acc)))
  :hints(("Goal"
          :in-theory (enable rw.slow-ccstep-list-arities
                             rw.ccstep-list-arities))))
