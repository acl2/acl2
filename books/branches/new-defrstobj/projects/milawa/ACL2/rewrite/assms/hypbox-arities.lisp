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
(include-book "hypboxp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund rw.slow-hypbox-arities (x)
  (declare (xargs :guard (rw.hypboxp x)))
  (app (logic.slow-term-list-arities (rw.hypbox->left x))
       (logic.slow-term-list-arities (rw.hypbox->right x))))

(defund rw.hypbox-arities (x acc)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (true-listp acc))))
  (logic.term-list-arities (rw.hypbox->left x)
                           (logic.term-list-arities (rw.hypbox->right x)
                                                    acc)))

(defthm true-listp-of-rw.hypbox-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hypbox-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-arities))))

(defthm rw.hypbox-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hypbox-arities x acc)
                  (app (rw.slow-hypbox-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hypbox-arities
                                    rw.slow-hypbox-arities))))

(defthm rw.slow-hypbox-arities-correct
  (implies (force (rw.hypboxp x))
           (equal (logic.arities-okp (rw.slow-hypbox-arities x) atbl)
                  (rw.hypbox-atblp x atbl)))
  :hints(("Goal"
          :in-theory (e/d (rw.slow-hypbox-arities
                           rw.hypbox-atblp)
                          ((:executable-counterpart acl2::force))))))

(definlined rw.fast-hypbox-atblp (x atbl)
  (declare (xargs :guard (and (rw.hypboxp x)
                              (logic.arity-tablep atbl))))
  (logic.fast-arities-okp (rw.hypbox-arities x nil) atbl))

(defthm rw.fast-hypbox-atblp-removal
  (implies (and (force (rw.hypboxp x))
                (force (mapp atbl)))
           (equal (rw.fast-hypbox-atblp x atbl)
                  (rw.hypbox-atblp x atbl)))
  :hints(("Goal" :in-theory (enable rw.fast-hypbox-atblp))))






(defund rw.slow-hypbox-list-arities (x)
  (declare (xargs :guard (rw.hypbox-listp x)))
  (if (consp x)
      ;; Reverse order gives us a tail call in the fast version
      (app (rw.slow-hypbox-list-arities (cdr x))
           (rw.slow-hypbox-arities (car x)))
    nil))

(defund rw.hypbox-list-arities (x acc)
  (declare (xargs :guard (and (rw.hypbox-listp x)
                              (true-listp acc))))
  (if (consp x)
      (rw.hypbox-list-arities (cdr x)
                              (rw.hypbox-arities (car x) acc))
    acc))

(defthm true-listp-of-rw.hypbox-list-arities
  (implies (force (true-listp acc))
           (equal (true-listp (rw.hypbox-list-arities x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.hypbox-list-arities))))

(defthm rw.hypbox-list-arities-removal
  (implies (force (true-listp acc))
           (equal (rw.hypbox-list-arities x acc)
                  (app (rw.slow-hypbox-list-arities x) acc)))
  :hints(("Goal" :in-theory (enable rw.hypbox-list-arities
                                    rw.slow-hypbox-list-arities))))

(defthm rw.slow-hypbox-list-arities-correct
  (implies (force (rw.hypbox-listp x))
           (equal (logic.arities-okp (rw.slow-hypbox-list-arities x) atbl)
                  (rw.hypbox-list-atblp x atbl)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :expand ((rw.hypbox-list-atblp x atbl)
                   (rw.slow-hypbox-list-arities x)))))

