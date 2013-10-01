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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund rw.slow-hyp-arities (x)
  (declare (xargs :guard (rw.hypp x)))
  (logic.slow-term-arities (rw.hyp->term x)))

(defund rw.hyp-arities (x acc)
  (declare (xargs :guard (and (rw.hypp x)
                              (true-listp acc))))
  (logic.term-arities (rw.hyp->term x) acc))

(defthm true-listp-of-rw.hyp-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hyp-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hyp-arities))))

(defthm rw.hyp-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hyp-arities x acc)
                  (app (rw.slow-hyp-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hyp-arities
                                    rw.slow-hyp-arities))))

(defthm logic.slow-hyp-arities-correct
  (implies (force (rw.hypp x))
           (equal (logic.arities-okp (rw.slow-hyp-arities x) atbl)
                  (rw.hyp-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.hyp-atblp x atbl)
                   (rw.slow-hyp-arities x))
          :in-theory (disable FORCING-LOGIC.TERM-ATBLP-OF-RW.HYP))))




(defund rw.slow-hyp-list-arities (x)
  (declare (xargs :guard (rw.hyp-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (rw.slow-hyp-list-arities (cdr x))
           (rw.slow-hyp-arities (car x)))
    nil))

(defund rw.hyp-list-arities (x acc)
  (declare (xargs :guard (and (rw.hyp-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.hyp-list-arities (cdr x)
                           (rw.hyp-arities (car x) acc))
    acc))

(defthm true-listp-of-rw.hyp-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hyp-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hyp-list-arities))))

(defthm rw.hyp-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hyp-list-arities x acc)
                  (app (rw.slow-hyp-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hyp-list-arities
                                    rw.slow-hyp-list-arities))))

(defthm rw.slow-hyp-list-arities-correct
  (implies (force (rw.hyp-listp x))
           (equal (logic.arities-okp (rw.slow-hyp-list-arities x) atbl)
                  (rw.hyp-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.hyp-list-atblp x atbl)
                   (rw.slow-hyp-list-arities x)))))




(defund rw.slow-rule-arities (x)
  (declare (xargs :guard (rw.rulep x)))
  (let* ((res (rw.slow-hyp-list-arities (rw.rule->hyps x)))
         (res (app (list (cons (rw.rule->equiv x) 2))                   res))
         (res (app (logic.slow-term-arities (rw.rule->lhs x))           res))
         (res (app (logic.slow-term-arities (rw.rule->rhs x))           res))
         (res (app (logic.slow-term-list-arities (rw.rule->crithyps x)) res)))
    res))

(defund rw.rule-arities (x acc)
  (declare (xargs :guard (and (rw.rulep x)
                              (true-listp acc))))
  (let* ((acc (rw.hyp-list-arities (rw.rule->hyps x) acc))
         (acc (cons (cons (rw.rule->equiv x) 2) acc))
         (acc (logic.term-arities (rw.rule->lhs x) acc))
         (acc (logic.term-arities (rw.rule->rhs x) acc)))
    ;; BOZO why do we care about crithyps arities?
    (logic.term-list-arities (rw.rule->crithyps x) acc)))

(defthm true-listp-of-rw.rule-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.rule-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-arities))))

(defthm rw.rule-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.rule-arities x acc)
                  (app (rw.slow-rule-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.rule-arities
                                    rw.slow-rule-arities))))

(defthm rw.slow-rule-arities-correct
  (implies (force (rw.rulep x))
           (equal (logic.arities-okp (rw.slow-rule-arities x) atbl)
                  (rw.rule-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.rule-atblp x atbl)
                   (rw.slow-rule-arities x))
          :in-theory (disable LOGIC.ARITIES-OKP-WHEN-SUBSETP-1
                              LOGIC.ARITIES-OKP-WHEN-SUBSETP-2
                              forcing-logic.term-list-atblp-of-rw.rule->crithyps
                              forcing-logic.term-atblp-of-rw.rule->lhs
                              forcing-logic.term-atblp-of-rw.rule->rhs
                              forcing-lookup-of-rw.rule-equiv
                              forcing-rw.hyp-list-atblp-of-rw.rule->hyps))))




(defund rw.slow-rule-list-arities (x)
  (declare (xargs :guard (rw.rule-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (rw.slow-rule-list-arities (cdr x))
           (rw.slow-rule-arities (car x)))
    nil))

(defund rw.rule-list-arities (x acc)
  (declare (xargs :guard (and (rw.rule-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.rule-list-arities (cdr x)
                           (rw.rule-arities (car x) acc))
    acc))

(defthm true-listp-of-rw.rule-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.rule-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-list-arities))))

(defthm rw.rule-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.rule-list-arities x acc)
                  (app (rw.slow-rule-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-arities
                                    rw.slow-rule-list-arities))))

(defthm rw.slow-rule-list-arities-correct
  (implies (force (rw.rule-listp x))
           (equal (logic.arities-okp (rw.slow-rule-list-arities x) atbl)
                  (rw.rule-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.rule-list-atblp x atbl)
                   (rw.slow-rule-list-arities x)))))





(defund rw.slow-rule-list-list-arities (x)
  (declare (xargs :guard (rw.rule-list-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (rw.slow-rule-list-list-arities (cdr x))
           (rw.slow-rule-list-arities (car x)))
    nil))

(defund rw.rule-list-list-arities (x acc)
  (declare (xargs :guard (and (rw.rule-list-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.rule-list-list-arities (cdr x)
                           (rw.rule-list-arities (car x) acc))
    acc))

(defthm true-listp-of-rw.rule-list-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.rule-list-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.rule-list-list-arities))))

(defthm rw.rule-list-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.rule-list-list-arities x acc)
                  (app (rw.slow-rule-list-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.rule-list-list-arities
                                    rw.slow-rule-list-list-arities))))

(defthm rw.slow-rule-list-list-arities-correct
  (implies (force (rw.rule-list-listp x))
           (equal (logic.arities-okp (rw.slow-rule-list-list-arities x) atbl)
                  (rw.rule-list-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.rule-list-list-atblp x atbl)
                   (rw.slow-rule-list-list-arities x)))))





(defund rw.slow-typed-rulemap-arities (x)
  (declare (xargs :guard (rw.typed-rulemapp x)))
  (if (consp x)
      (app (rw.slow-typed-rulemap-arities (cdr x))
           (rw.slow-rule-list-arities (cdr (car x))))
    nil))

(defund rw.typed-rulemap-arities (x acc)
  (declare (xargs :guard (and (rw.typed-rulemapp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.typed-rulemap-arities (cdr x)
                                (rw.rule-list-arities (cdr (car x))
                                                      acc))
    acc))

(defthm true-listp-of-rw.typed-rulemap-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.typed-rulemap-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.typed-rulemap-arities))))

(defthm rw.typed-rulemap-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.typed-rulemap-arities x acc)
                  (app (rw.slow-typed-rulemap-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.typed-rulemap-arities
                                    rw.slow-typed-rulemap-arities))))

(defthm rw.slow-typed-rulemap-arities-correct
  (implies (force (rw.typed-rulemapp x))
           (equal (logic.arities-okp (rw.slow-typed-rulemap-arities x) atbl)
                  (rw.rule-list-list-atblp (range x) atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.slow-typed-rulemap-arities x)))))




(defund rw.slow-theory-arities (x)
  (declare (xargs :guard (rw.theoryp x)))
  (if (consp x)
      (let* ((res (rw.slow-typed-rulemap-arities (rw.theory->rulemap x)))
             (res (app (rw.slow-theory-arities (rw.theory->left x)) res))
             (res (app (rw.slow-theory-arities (rw.theory->right x)) res)))
        res)
    nil))

(defund rw.theory-arities (x acc)
  (declare (xargs :guard (and (rw.theoryp x)
                              (true-listp acc))
                  :verify-guards nil))
  (if (consp x)
      (let* ((acc (rw.typed-rulemap-arities (rw.theory->rulemap x) acc))
             (acc (rw.theory-arities (rw.theory->left x) acc)))
        (rw.theory-arities (rw.theory->right x) acc))
    acc))

(defthm true-listp-of-rw.theory-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.theory-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.theory-arities))))

(verify-guards rw.theory-arities)

(defthm rw.theory-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.theory-arities x acc)
                  (app (rw.slow-theory-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.theory-arities
                                    rw.slow-theory-arities))))

(defthm rw.slow-theory-arities-correct
  (implies (force (rw.theoryp x))
           (equal (logic.arities-okp (rw.slow-theory-arities x) atbl)
                  (rw.theory-atblp x atbl)))
  :hints(("Goal"
          :expand ((rw.slow-theory-arities x)
                   (rw.theory-atblp x atbl))
          :in-theory (e/d (rw.slow-theory-arities)
                          (logic.arities-okp-when-subsetp-1
                           logic.arities-okp-when-subsetp-2
                           forcing-rw.rule-list-list-atblp-of-of-range-of-rw.theory->rulemap
                           forcing-theory-atblp-of-rw.theory->left
                           forcing-theory-atblp-of-rw.theory->right)))))




(defund rw.slow-theory-map-arities (x)
  (declare (xargs :guard (rw.theory-mapp x)))
  (if (consp x)
      (app (rw.slow-theory-map-arities (cdr x))
           (rw.slow-theory-arities (cdr (car x))))
    nil))

(defund rw.theory-map-arities (x acc)
  (declare (xargs :guard (and (rw.theory-mapp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.theory-map-arities (cdr x)
                              (rw.theory-arities (cdr (car x)) acc))
    acc))

(defthm true-listp-of-rw.theory-map-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.theory-map-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.theory-map-arities))))

(verify-guards rw.theory-map-arities)

(defthm rw.theory-map-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.theory-map-arities x acc)
                  (app (rw.slow-theory-map-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.theory-map-arities
                                    rw.slow-theory-map-arities))))

(defthm rw.slow-theory-map-arities-correct
  (implies (force (rw.theory-mapp x))
           (equal (logic.arities-okp (rw.slow-theory-map-arities x) atbl)
                  (rw.theory-list-atblp (range x) atbl)))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-theory-map-arities)
                          (logic.arities-okp-when-subsetp-1
                           logic.arities-okp-when-subsetp-2)))))
