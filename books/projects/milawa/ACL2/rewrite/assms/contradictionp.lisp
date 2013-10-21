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
(include-book "eqtrace-okp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.eqtrace-contradictionp (x)
  ;; We recognize traces of the following forms as contradictions:
  ;;  -- (equal c1 c2) = t
  ;;       Where c1,c2 are unequal constants
  ;;  -- (equal x (not* x)) = t
  ;;       By the term order, this also checks (equal (not* x) x) = t
  ;;  -- (iff nil t) = t
  ;;       By the term order, this also checks (iff t nil) = t
  ;;       By the canonicalization of constants, this also checks for all other
  ;;       non-nil constants besides t
  ;;  -- (iff x (not* x)) = t
  ;;       By the term order, this also checks (iff (not* x) x) = t
  (declare (xargs :guard (rw.eqtracep x)))
  (let ((lhs  (rw.eqtrace->lhs x))
        (rhs  (rw.eqtrace->rhs x))
        (iffp (rw.eqtrace->iffp x)))
    (or ;; Perhaps there is a contradiction from a constant
        (if iffp
            (and (equal lhs ''nil)
                 (equal rhs ''t))
          (and (logic.constantp lhs)
               (logic.constantp rhs)
               (not (equal lhs rhs))))
        ;; Perhaps there is a contradiction from (equiv x (not* x))
        (and (clause.negative-termp rhs)
             (equal (clause.negative-term-guts rhs) lhs)))))

(defthm booleanp-of-rw.eqtrace-contradictionp
  (equal (booleanp (rw.eqtrace-contradictionp x))
         t)
  :hints(("Goal" :in-theory (enable rw.eqtrace-contradictionp))))



(defund rw.find-eqtrace-contradiction (x)
  (declare (xargs :guard (rw.eqtrace-listp x)))
  (if (consp x)
      (if (rw.eqtrace-contradictionp (car x))
          (car x)
        (rw.find-eqtrace-contradiction (cdr x)))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.find-eqtrace-contradiction)))

 (defthm forcing-rw.eqtracep-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-listp x)))
            (equal (rw.eqtracep (rw.find-eqtrace-contradiction x))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-list-atblp x atbl)))
            (equal (rw.eqtrace-atblp (rw.find-eqtrace-contradiction x) atbl)
                   t)))

 (defthm forcing-rw.eqtrace-okp-of-rw.find-eqtrace-contradiction
   (implies (and (rw.find-eqtrace-contradiction x)
                 (force (rw.eqtrace-list-okp x box)))
            (equal (rw.eqtrace-okp (rw.find-eqtrace-contradiction x) box)
                   t)))

 (defthm forcing-rw.eqtrace-contradictionp-of-rw.find-eqtrace-contradiction
   (implies (rw.find-eqtrace-contradiction x)
            (equal (rw.eqtrace-contradictionp (rw.find-eqtrace-contradiction x))
                   t))))
