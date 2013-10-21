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
(include-book "urewrite")
(include-book "crewrite")
(include-book "fast-traces")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; The Fast, Unconditional Rewriter
;;
;; We now introduce a version of urewrite which produces fast traces instead of
;; full-blown traces.  We prove it mirrors the operation of urewrite, in that
;; the ftrace it produces:
;;
;;   - has no fgoals (just like urewrite) and also
;;   - has the same rhs as the trace produced by urewrite
;;
;; Thus, the fast version of urewrite can be used when we do not need to
;; produce a full-blown trace.

(defconst *rw.fast-flag-urewrite-sigma*
  (list (cons '(rw.flag-urewrite 'term ?x ?iffp ?control ?n)
              '(rw.fast-flag-urewrite 'term ?x ?iffp ?control ?n))
        (cons '(rw.flag-urewrite 'list ?x ?iffp ?control ?n)
              '(rw.fast-flag-urewrite 'list ?x ?iffp ?control ?n))))

(ACL2::make-event
 `(encapsulate
   ()
   (defun rw.fast-flag-urewrite (flag x iffp control n)
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
        ,(ACL2::jared-rewrite *rw.flag-urewrite*
                              (revappend *rw.fast-flag-urewrite-sigma* *rw.fast-traces-sigma*))
      (if (consp x)
          (let ((car-rw (rw.fast-flag-urewrite 'term (car x) iffp control n))
                (cdr-rw (rw.fast-flag-urewrite 'list (cdr x) iffp control n)))
            (rw.ftraces (cons (rw.ftrace->rhs car-rw) (rw.ftraces->rhses cdr-rw))
                        nil))
        (rw.ftraces nil nil))))))

(defund rw.fast-urewrite (x iffp control n)
  (declare (xargs :guard (and (logic.termp x)
                              (booleanp iffp)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil))
  (rw.fast-flag-urewrite 'term x iffp control n))

(defund rw.fast-urewrite-list (x iffp control n)
  (declare (xargs :guard (and (logic.term-listp x)
                              (booleanp iffp)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil))
  (rw.fast-flag-urewrite 'list x iffp control n))


(defconst *rw.fast-flagless-urewrite-sigma*
  (list (cons '(ACL2::prog2$ ?x ?y)
              '?y)
        (cons '(rw.flag-urewrite 'term ?x ?iffp ?control ?n)
              '(rw.fast-urewrite ?x ?iffp ?control ?n))
        (cons '(rw.flag-urewrite 'list ?x ?iffp ?control ?n)
              '(rw.fast-urewrite-list ?x ?iffp ?control ?n))))


(ACL2::make-event
 `(defthmd definition-of-rw.fast-urewrite
    (equal (rw.fast-urewrite x iffp control n)
           ,(ACL2::jared-rewrite *rw.flag-urewrite*
                                 (revappend *rw.fast-flagless-urewrite-sigma*
                                            *rw.fast-traces-sigma*)))
    :rule-classes :definition
    :hints(("Goal"
            :in-theory (enable rw.fast-urewrite
                               rw.fast-urewrite-list)
            :expand (rw.fast-flag-urewrite 'term x iffp control n)))))

(defthmd definition-of-rw.fast-urewrite-list
  (equal (rw.fast-urewrite-list x iffp control n)
         (if (consp x)
             (let ((car-rw (rw.fast-flag-urewrite 'term (car x) iffp control n))
                   (cdr-rw (rw.fast-flag-urewrite 'list (cdr x) iffp control n)))
               (rw.ftraces (cons (rw.ftrace->rhs car-rw) (rw.ftraces->rhses cdr-rw))
                           nil))
           (rw.ftraces nil nil)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (enable rw.fast-urewrite
                             rw.fast-urewrite-list)
          :expand (rw.fast-flag-urewrite 'list x iffp control n))))

(defthm rw.fast-flag-urewrite-of-term
  (equal (rw.fast-flag-urewrite 'term x iffp control n)
         (rw.fast-urewrite x iffp control n))
  :hints(("Goal" :in-theory (enable rw.fast-urewrite))))

(defthm rw.fast-flag-urewrite-of-list
  (equal (rw.fast-flag-urewrite 'list x iffp control n)
         (rw.fast-urewrite-list x iffp control n))
  :hints(("Goal" :in-theory (enable rw.fast-urewrite-list))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-urewrite))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-urewrite-list))))


(defthm rw.fast-urewrite-under-iff
  (implies (force (logic.termp x))
           (iff (rw.fast-urewrite x iffp control n)
                t))
  :hints(("Goal"
          :expand (rw.fast-urewrite x iffp control n)
          :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthm len-of-rw.ftraces->rhses-of-rw.fast-urewrite-list
  (equal (len (rw.ftraces->rhses (rw.fast-urewrite-list x iffp control n)))
         (len x))
  :hints(("Goal"
          :expand (rw.fast-urewrite-list x iffp control n)
          :induct (cdr-induction x))))



(defthms-flag
  :shared-hyp (force (rw.controlp control))
  :thms ((term forcing-rw.ftracep-of-rw.fast-urewrite
               (implies (force (logic.termp x))
                        (equal (rw.ftracep (rw.fast-urewrite x iffp control n))
                               t)))
         (t forcing-rw.ftrace-listp-of-rw.fast-urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.ftracesp (rw.fast-urewrite-list x iffp control n))
                            t))))
  :hints(("Goal"
          :expand ((:free (iffp) (rw.fast-urewrite x iffp control n))
                   (:free (iffp) (rw.fast-urewrite-list x iffp control n)))
          :induct (rw.fast-flag-urewrite flag x iffp control n)
          :in-theory (disable forcing-lookup-of-logic.function-name))))



(defthms-flag
  :shared-hyp (force (and (rw.controlp control)
                          (booleanp iffp)))
  :thms ((term forcing-rw.trace-fast-image-of-rw.urewrite
               (implies (force (logic.termp x))
                        (equal (rw.trace-fast-image (rw.urewrite x iffp control n))
                               (rw.fast-urewrite x iffp control n))))
         (t forcing-rw.trace-list-fast-image-of-rw.urewrite-list
            (implies (force (logic.term-listp x))
                     (equal (rw.trace-list-fast-image (rw.urewrite-list x iffp control n))
                            (rw.fast-urewrite-list x iffp control n)))))
  :hints(("Goal"
          :expand ((:free (iffp) (rw.fast-urewrite x iffp control n))
                   (:free (iffp) (rw.urewrite x iffp control n))
                   (:free (iffp) (rw.fast-urewrite-list x iffp control n))
                   (:free (iffp) (rw.urewrite-list x iffp control n)))
          :induct (rw.flag-urewrite flag x iffp control n)
          :in-theory (e/d (rw.trace-fast-image-equivalence-lemmas)
                          (forcing-lookup-of-logic.function-name)))))


(defthm forcing-rw.ftrace->rhs-of-rw.fast-urewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.controlp control)))
           (equal (rw.ftrace->rhs (rw.fast-urewrite x iffp control n))
                  (rw.trace->rhs (rw.urewrite x iffp control n))))
  :hints(("Goal"
          :in-theory (disable forcing-rw.trace-fast-image-of-rw.urewrite)
          :use ((:instance forcing-rw.trace-fast-image-of-rw.urewrite)))))

(defthm forcing-rw.ftraces->rhses-of-rw.fast-urewrite-list
  (implies (force (and (logic.term-listp x)
                       (booleanp iffp)
                       (rw.controlp control)))
           (equal (rw.ftraces->rhses (rw.fast-urewrite-list x iffp control n))
                  (rw.trace-list-rhses (rw.urewrite-list x iffp control n))))
  :hints(("Goal"
          :in-theory (disable forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
          :use ((:instance forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))))


(defthm forcing-rw.ftrace->fgoals-of-rw.fast-urewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.controlp control)))
           (equal (rw.ftrace->fgoals (rw.fast-urewrite x iffp control n))
                  nil))
  :hints(("Goal"
          :in-theory (disable forcing-rw.trace-fast-image-of-rw.urewrite)
          :use ((:instance forcing-rw.trace-fast-image-of-rw.urewrite)))))

(defthm forcing-rw.ftraces->fgoals-of-rw.fast-urewrite-list
  (implies (force (and (logic.term-listp x)
                       (booleanp iffp)
                       (rw.controlp control)))
           (equal (rw.ftraces->fgoals (rw.fast-urewrite-list x iffp control n))
                  nil))
  :hints(("Goal"
          :in-theory (disable forcing-rw.trace-list-fast-image-of-rw.urewrite-list)
          :use ((:instance forcing-rw.trace-list-fast-image-of-rw.urewrite-list)))))

(verify-guards rw.fast-flag-urewrite)
(verify-guards rw.fast-urewrite)
(verify-guards rw.fast-urewrite-list)

