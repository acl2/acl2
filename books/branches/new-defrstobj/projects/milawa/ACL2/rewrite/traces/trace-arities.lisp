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
(include-book "../assms/hypbox-arities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.slow-flag-trace-arities (flag x)
  (declare (xargs :guard (if (equal flag 'term)
                             (rw.tracep x)
                           (rw.trace-listp x))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (let* ((res (rw.slow-hypbox-arities (rw.trace->hypbox x)))
             (res (app (logic.slow-term-arities (rw.trace->lhs x)) res))
             (res (app (logic.slow-term-arities (rw.trace->rhs x)) res))
             (res (app (rw.slow-flag-trace-arities 'list (rw.trace->subtraces x)) res)))
        res)
    (if (consp x)
        (app (rw.slow-flag-trace-arities 'term (car x))
             (rw.slow-flag-trace-arities 'list (cdr x)))
      nil)))

(definlined rw.slow-trace-arities (x)
  (declare (xargs :guard (rw.tracep x)))
  (rw.slow-flag-trace-arities 'term x))

(definlined rw.slow-trace-list-arities (x)
  (declare (xargs :guard (rw.trace-listp x)))
  (rw.slow-flag-trace-arities 'list x))

(defthmd definition-of-rw.slow-trace-arities
  (equal (rw.slow-trace-arities x)
         (let* ((res (rw.slow-hypbox-arities (rw.trace->hypbox x)))
                (res (app (logic.slow-term-arities (rw.trace->lhs x)) res))
                (res (app (logic.slow-term-arities (rw.trace->rhs x)) res))
                (res (app (rw.slow-trace-list-arities (rw.trace->subtraces x)) res)))
           res))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.slow-flag-trace-arities 'term x))
          :in-theory (enable rw.slow-trace-list-arities rw.slow-trace-arities))))

(defthmd definition-of-rw.slow-trace-list-arities
  (equal (rw.slow-trace-list-arities x)
         (if (consp x)
             (app (rw.slow-trace-arities (car x))
                  (rw.slow-trace-list-arities (cdr x)))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.slow-flag-trace-arities 'list x))
          :in-theory (enable rw.slow-trace-list-arities rw.slow-trace-arities))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.slow-trace-arities))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.slow-trace-arities-list))))

(defthm rw.slow-trace-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (rw.slow-trace-list-arities x)
                  nil))
  :hints(("Goal" :in-theory (enable definition-of-rw.slow-trace-list-arities))))

(defthm rw.slow-trace-list-arities-of-cons
  (equal (rw.slow-trace-list-arities (cons a x))
         (app (rw.slow-trace-arities a)
              (rw.slow-trace-list-arities x)))
  :hints(("Goal" :in-theory (enable definition-of-rw.slow-trace-list-arities))))



(defund rw.flag-trace-arities (flag x acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (rw.tracep x)
                                (rw.trace-listp x))
                              (true-listp acc))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))
                  :verify-guards nil))
  (if (equal flag 'term)
      (let* ((acc (rw.hypbox-arities (rw.trace->hypbox x) acc))
             (acc (logic.term-arities (rw.trace->lhs x) acc))
             (acc (logic.term-arities (rw.trace->rhs x) acc)))
        (rw.flag-trace-arities 'list (rw.trace->subtraces x) acc))
    (if (consp x)
        (rw.flag-trace-arities 'term (car x)
                               (rw.flag-trace-arities 'list (cdr x) acc))
      acc)))

(definlined rw.trace-arities (x acc)
  (declare (xargs :guard (and (rw.tracep x)
                              (true-listp acc))
                  :verify-guards nil))
  (rw.flag-trace-arities 'term x acc))

(definlined rw.trace-list-arities (x acc)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (true-listp acc))
                  :verify-guards nil))
  (rw.flag-trace-arities 'list x acc))

(defthmd definition-of-rw.trace-arities
  (equal (rw.trace-arities x acc)
         (let* ((acc (rw.hypbox-arities (rw.trace->hypbox x) acc))
                (acc (logic.term-arities (rw.trace->lhs x) acc))
                (acc (logic.term-arities (rw.trace->rhs x) acc)))
           (rw.trace-list-arities (rw.trace->subtraces x) acc)))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (e/d (rw.trace-arities
                           rw.trace-list-arities)
                          ((:executable-counterpart acl2::force)))
          :expand (rw.flag-trace-arities 'term x acc))))

(defthmd definition-of-rw.trace-list-arities
  (equal (rw.trace-list-arities x acc)
         (if (consp x)
             (rw.trace-arities (car x)
                               (rw.trace-list-arities (cdr x) acc))
           acc))
  :rule-classes :definition
  :hints(("Goal"
          :in-theory (e/d (rw.trace-arities
                           rw.trace-list-arities)
                          ((:executable-counterpart acl2::force)))
          :expand (rw.flag-trace-arities 'list x acc))))

(defthm rw.flag-trace-arities-of-term
  (equal (rw.flag-trace-arities 'term x acc)
         (rw.trace-arities x acc))
  :hints(("Goal" :in-theory (enable rw.trace-arities))))

(defthm rw.flag-trace-arities-of-list
  (equal (rw.flag-trace-arities 'list x acc)
         (rw.trace-list-arities x acc))
  :hints(("Goal" :in-theory (enable rw.trace-list-arities))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-arities))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.trace-list-arities))))

(defthm rw.trace-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (rw.trace-list-arities x acc)
                  acc))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-arities))))

(defthm rw.trace-list-arities-of-cons
  (equal (rw.trace-list-arities (cons a x) acc)
         (rw.trace-arities a
                           (rw.trace-list-arities x acc)))
  :hints(("Goal" :in-theory (enable definition-of-rw.trace-list-arities))))


(defthms-flag
  :shared-hyp (force (true-listp acc))
  :thms ((term true-listp-of-rw.trace-arities
               (equal (true-listp (rw.trace-arities x acc))
                      t))
         (t true-listp-of-rw.trace-list-arities
            (equal (true-listp (rw.trace-list-arities x acc))
                   t)))
  :hints(("Goal"
          :induct (rw.flag-trace-arities flag x acc)
          :in-theory (enable (:induction rw.flag-trace-arities))
          :expand ((rw.trace-arities x acc)))))

(verify-guards rw.flag-trace-arities)
(verify-guards rw.trace-arities)
(verify-guards rw.trace-list-arities)


(defthms-flag
  :shared-hyp (force (true-listp acc))
  :thms ((term rw.trace-arities-removal
               (equal (rw.trace-arities x acc)
                      (app (rw.slow-trace-arities x)
                           acc)))
         (t rw.trace-list-arities-removal
            (equal (rw.trace-list-arities x acc)
                   (app (rw.slow-trace-list-arities x)
                        acc))))
  :hints(("Goal"
          :induct (rw.flag-trace-arities flag x acc)
          :in-theory (enable (:induction rw.flag-trace-arities))
          :expand ((rw.trace-arities x acc)
                   (rw.slow-trace-arities x)))))

(defthms-flag
  :thms ((term rw.slow-trace-arities-correct
               (implies (force (rw.tracep x))
                        (equal (logic.arities-okp (rw.slow-trace-arities x) atbl)
                               (rw.trace-atblp x atbl))))
         (t rw.slow-trace-list-arities-correct
            (implies (force (rw.trace-listp x))
                     (equal (logic.arities-okp (rw.slow-trace-list-arities x) atbl)
                            (rw.trace-list-atblp x atbl)))))
  :hints(("Goal"
          :induct (rw.trace-induction flag x)
          :expand ((rw.trace-atblp x atbl)
                   (rw.slow-trace-arities x))
          :in-theory (disable (:executable-counterpart acl2::force)))))


(definlined rw.fast-trace-atblp (x atbl)
  (declare (xargs :guard (and (rw.tracep x)
                              (logic.arity-tablep atbl))))
  (logic.fast-arities-okp (rw.trace-arities x nil) atbl))

(defthm rw.fast-trace-atblp-removal
  (implies (and (force (rw.tracep x))
                (force (mapp atbl)))
           (equal (rw.fast-trace-atblp x atbl)
                  (rw.trace-atblp x atbl)))
  :hints(("Goal" :in-theory (enable rw.fast-trace-atblp))))




(defund rw.fast-trace-list-atblp (x atbl)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (logic.arity-tablep atbl))))
  (logic.fast-arities-okp (rw.trace-list-arities x nil) atbl))

(defthm rw.fast-trace-list-atblp-removal
  (implies (force (and (rw.trace-listp x)
                       (mapp atbl)))
           (equal (rw.fast-trace-list-atblp x atbl)
                  (rw.trace-list-atblp x atbl)))
  :hints(("Goal" :in-theory (enable rw.fast-trace-list-atblp))))






; Now we want to do develop a similar arity table check that avoids redundantly gathering
; arities from equal hypboxes.

(defund rw.slow-faster-flag-trace-arities (flag x ext-hypbox)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (rw.tracep x)
                                (rw.trace-listp x))
                              (rw.hypboxp ext-hypbox))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))))
  (if (equal flag 'term)
      (let* ((hypbox (rw.trace->hypbox x))
             (res (if (equal hypbox ext-hypbox)
                      nil
                    (rw.slow-hypbox-arities hypbox)))
             (res (app (logic.slow-term-arities (rw.trace->lhs x)) res))
             (res (app (logic.slow-term-arities (rw.trace->rhs x)) res))
             (res (app (rw.slow-faster-flag-trace-arities 'list (rw.trace->subtraces x) hypbox) res)))
        res)
    (if (consp x)
        (app (rw.slow-faster-flag-trace-arities 'term (car x) ext-hypbox)
             (rw.slow-faster-flag-trace-arities 'list (cdr x) ext-hypbox))
      nil)))

(defund rw.slow-faster-trace-arities (x ext-hypbox)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.hypboxp ext-hypbox))))
  (rw.slow-faster-flag-trace-arities 'term x ext-hypbox))

(defund rw.slow-faster-trace-list-arities (x ext-hypbox)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (rw.hypboxp ext-hypbox))))
  (rw.slow-faster-flag-trace-arities 'list x ext-hypbox))

(defthmd definition-of-rw.slow-faster-trace-arities
  (equal (rw.slow-faster-trace-arities x ext-hypbox)
         (let* ((hypbox (rw.trace->hypbox x))
                (res (if (equal hypbox ext-hypbox)
                         nil
                       (rw.slow-hypbox-arities hypbox)))
                (res (app (logic.slow-term-arities (rw.trace->lhs x)) res))
                (res (app (logic.slow-term-arities (rw.trace->rhs x)) res))
                (res (app (rw.slow-faster-trace-list-arities (rw.trace->subtraces x) hypbox) res)))
           res))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.slow-faster-flag-trace-arities 'term x ext-hypbox))
          :in-theory (enable rw.slow-faster-trace-arities
                             rw.slow-faster-trace-list-arities ))))

(defthmd definition-of-rw.slow-faster-trace-list-arities
  (equal (rw.slow-faster-trace-list-arities x ext-hypbox)
         (if (consp x)
             (app (rw.slow-faster-trace-arities (car x) ext-hypbox)
                  (rw.slow-faster-trace-list-arities (cdr x) ext-hypbox))
           nil))
  :rule-classes :definition
  :hints(("Goal"
          :expand ((rw.slow-faster-flag-trace-arities 'list x ext-hypbox))
          :in-theory (enable rw.slow-faster-trace-arities
                             rw.slow-faster-trace-list-arities))))

(defthm rw.slow-faster-flag-trace-arities-of-term
  (equal (rw.slow-faster-flag-trace-arities 'term x ext-hypbox)
         (rw.slow-faster-trace-arities x ext-hypbox))
  :hints(("Goal" :in-theory (enable rw.slow-faster-trace-arities))))

(defthm rw.slow-faster-flag-trace-arities-of-list
  (equal (rw.slow-faster-flag-trace-arities 'list x ext-hypbox)
         (rw.slow-faster-trace-list-arities x ext-hypbox))
  :hints(("Goal" :in-theory (enable rw.slow-faster-trace-list-arities))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.slow-faster-trace-arities))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.slow-faster-trace-list-arities))))

(defthm rw.slow-faster-trace-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (rw.slow-faster-trace-list-arities x ext-hypbox)
                  nil))
  :hints(("Goal" :expand (rw.slow-faster-trace-list-arities x ext-hypbox))))

(defthm rw.slow-faster-trace-list-arities-of-cons
  (equal (rw.slow-faster-trace-list-arities (cons a x) ext-hypbox)
         (app (rw.slow-faster-trace-arities a ext-hypbox)
              (rw.slow-faster-trace-list-arities x ext-hypbox)))
  :hints(("Goal" :expand (rw.slow-faster-trace-list-arities (cons a x) ext-hypbox))))

(defthms-flag
  :shared-hyp (force (and (rw.hypboxp hypbox)
                          (rw.hypbox-atblp hypbox atbl)))
  :thms ((term rw.slow-faster-trace-arities-correct
               (implies (rw.tracep x)
                        (equal (logic.arities-okp (rw.slow-faster-trace-arities x hypbox) atbl)
                               (rw.trace-atblp x atbl))))
         (t rw.slow-faster-trace-list-arities-correct
            (implies (rw.trace-listp x)
                     (equal (logic.arities-okp (rw.slow-faster-trace-list-arities x hypbox) atbl)
                            (rw.trace-list-atblp x atbl)))))
  :hints(("Goal"
          :in-theory (e/d ((:induction rw.slow-faster-flag-trace-arities))
                          ((:executable-counterpart acl2::force)))
          :induct (rw.slow-faster-flag-trace-arities flag x hypbox)
          :expand ((rw.slow-faster-trace-arities x hypbox)
                   (rw.trace-atblp x atbl)))))




(defund rw.faster-flag-trace-arities (flag x ext-hypbox acc)
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (rw.tracep x)
                                (rw.trace-listp x))
                              (rw.hypboxp ext-hypbox)
                              (true-listp acc))
                  :measure (two-nats-measure (rank x) (if (equal flag 'term) 1 0))
                  :verify-guards nil))
  (if (equal flag 'term)
      (let* ((hypbox (rw.trace->hypbox x))
             (acc    (if (equal hypbox ext-hypbox)
                         acc
                       (rw.hypbox-arities (rw.trace->hypbox x) acc)))
             (acc    (logic.term-arities (rw.trace->lhs x) acc))
             (acc    (logic.term-arities (rw.trace->rhs x) acc)))
        (rw.faster-flag-trace-arities 'list (rw.trace->subtraces x) hypbox acc))
    (if (consp x)
        (rw.faster-flag-trace-arities 'term (car x) ext-hypbox
                                      (rw.faster-flag-trace-arities 'list (cdr x) ext-hypbox acc))
      acc)))

(defund rw.faster-trace-arities (x ext-hypbox acc)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.hypboxp ext-hypbox)
                              (true-listp acc))
                  :verify-guards nil))
  (rw.faster-flag-trace-arities 'term x ext-hypbox acc))

(defund rw.faster-trace-list-arities (x ext-hypbox acc)
  (declare (xargs :guard (and (rw.trace-listp x)
                              (rw.hypboxp ext-hypbox)
                              (true-listp acc))
                  :verify-guards nil))
  (rw.faster-flag-trace-arities 'list x ext-hypbox acc))

(defthmd definition-of-rw.faster-trace-arities
  (equal (rw.faster-trace-arities x ext-hypbox acc)
         (let* ((hypbox (rw.trace->hypbox x))
                (acc    (if (equal hypbox ext-hypbox)
                            acc
                          (rw.hypbox-arities (rw.trace->hypbox x) acc)))
                (acc    (logic.term-arities (rw.trace->lhs x) acc))
                (acc    (logic.term-arities (rw.trace->rhs x) acc)))
           (rw.faster-trace-list-arities (rw.trace->subtraces x) hypbox acc)))
  :rule-classes :definition
  :hints(("Goal"
          :expand (rw.faster-flag-trace-arities 'term x ext-hypbox acc)
          :in-theory (enable rw.faster-trace-arities rw.faster-trace-list-arities))))

(defthmd definition-of-rw.faster-trace-list-arities
  (equal (rw.faster-trace-list-arities x ext-hypbox acc)
         (if (consp x)
             (rw.faster-trace-arities (car x) ext-hypbox
              (rw.faster-trace-list-arities (cdr x) ext-hypbox acc))
           acc))
  :rule-classes :definition
  :hints(("Goal"
          :expand (rw.faster-flag-trace-arities 'list x ext-hypbox acc)
          :in-theory (enable rw.faster-trace-arities rw.faster-trace-list-arities))))

(defthm rw.faster-flag-trace-arities-of-term
  (equal (rw.faster-flag-trace-arities 'term x ext-hypbox acc)
         (rw.faster-trace-arities x ext-hypbox acc))
  :hints(("Goal" :in-theory (enable rw.faster-trace-arities))))

(defthm rw.faster-flag-trace-arities-of-list
  (equal (rw.faster-flag-trace-arities 'list x ext-hypbox acc)
         (rw.faster-trace-list-arities x ext-hypbox acc))
  :hints(("Goal" :in-theory (enable rw.faster-trace-list-arities))))

(defthm rw.faster-trace-list-arities-when-not-consp
  (implies (not (consp x))
           (equal (rw.faster-trace-list-arities x ext-hypbox acc)
                  acc))
  :hints(("Goal" :expand (rw.faster-trace-list-arities x ext-hypbox acc))))

(defthm rw.faster-trace-list-arities-of-cons
  (equal (rw.faster-trace-list-arities (cons a x) ext-hypbox acc)
         (rw.faster-trace-arities a ext-hypbox
                                  (rw.faster-trace-list-arities x ext-hypbox acc)))
  :hints(("Goal"
          :expand (rw.faster-trace-list-arities (cons a x) ext-hypbox acc)
          :in-theory (disable (:executable-counterpart acl2::force))
          )))

(defthms-flag
  :shared-hyp (force (true-listp acc))
  :thms ((term true-listp-of-rw.faster-trace-arities
               (equal (true-listp (rw.faster-trace-arities x ext-hypbox acc))
                      t))
         (t true-listp-of-rw.faster-trace-list-arities
            (equal (true-listp (rw.faster-trace-list-arities x ext-hypbox acc))
                   t)))
  :hints(("Goal"
          :induct (rw.faster-flag-trace-arities flag x ext-hypbox acc)
          :in-theory (e/d ((:induction rw.faster-flag-trace-arities)))
          :expand ((rw.faster-trace-arities x ext-hypbox acc)
                   (rw.slow-faster-trace-arities x ext-hypbox)))))

(defthms-flag
  :shared-hyp (force (true-listp acc))
  :thms ((term rw.faster-trace-arities-removal
               (equal (rw.faster-trace-arities x ext-hypbox acc)
                      (app (rw.slow-faster-trace-arities x ext-hypbox)
                           acc)))
         (t rw.faster-trace-list-arities-removal
            (equal (rw.faster-trace-list-arities x ext-hypbox acc)
                   (app (rw.slow-faster-trace-list-arities x ext-hypbox)
                        acc))))
  :hints(("Goal"
          :induct (rw.faster-flag-trace-arities flag x ext-hypbox acc)
          :in-theory (e/d ((:induction rw.faster-flag-trace-arities))
                          ;((:executable-counterpart acl2::force)))
                          )
          :expand ((rw.faster-trace-arities x ext-hypbox acc)
                   (rw.slow-faster-trace-arities x ext-hypbox)))))

(verify-guards rw.faster-flag-trace-arities)
(verify-guards rw.faster-trace-arities)
(verify-guards rw.faster-trace-list-arities)

