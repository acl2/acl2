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
(include-book "eqtracep")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




(defund rw.weakening-eqtrace (x)
  ;; Infer (iff lhs rhs) from (equiv lhs rhs).
  (declare (xargs :guard (rw.eqtracep x)))
  (rw.eqtrace 'weakening t (rw.eqtrace->lhs x) (rw.eqtrace->rhs x) (list x)))

(encapsulate
 ()
 (local (in-theory (enable rw.weakening-eqtrace)))

 (defthm forcing-rw.eqtrace->method-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->method (rw.weakening-eqtrace x))
          'weakening))

 (defthm forcing-rw.eqtrace->iffp-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->iffp (rw.weakening-eqtrace x))
          t))

 (defthm forcing-rw.eqtrace->lhs-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->lhs (rw.weakening-eqtrace x))
          (rw.eqtrace->lhs x)))

 (defthm forcing-rw.eqtrace->rhs-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->rhs (rw.weakening-eqtrace x))
          (rw.eqtrace->rhs x)))

 (defthm forcing-rw.eqtrace->subtraces-of-rw.weakening-eqtrace
   (equal (rw.eqtrace->subtraces (rw.weakening-eqtrace x))
          (list x)))

 (defthm forcing-rw.eqtracep-of-rw.weakening-eqtrace
   (implies (force (rw.eqtracep x))
            (equal (rw.eqtracep (rw.weakening-eqtrace x))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.weakening-eqtrace
   (implies (force (rw.eqtrace-atblp x atbl))
            (equal (rw.eqtrace-atblp (rw.weakening-eqtrace x) atbl)
                   t))))



(defund rw.weakening-eqtrace-okp (x)
  ;; Check if any nhyp in the hypbox would generate this weakening eqtrace.
  (declare (xargs :guard (and (rw.eqtracep x))))
  (let ((method    (rw.eqtrace->method x))
        (iffp      (rw.eqtrace->iffp x))
        (lhs       (rw.eqtrace->lhs x))
        (rhs       (rw.eqtrace->rhs x))
        (subtraces (rw.eqtrace->subtraces x)))
    (and (equal method 'weakening)
         (equal iffp t)
         (equal (len subtraces) 1)
         (equal lhs (rw.eqtrace->lhs (first subtraces)))
         (equal rhs (rw.eqtrace->rhs (first subtraces))))))

(defthm booleanp-of-rw.weakening-eqtrace-okp
  (equal (booleanp (rw.weakening-eqtrace-okp x))
         t)
  :hints(("Goal" :in-theory (e/d (rw.weakening-eqtrace-okp)
                                 (forcing-booleanp-of-rw.eqtrace->iffp)))))

(defthm forcing-rw.weakening-eqtrace-okp-of-rw.weakening-eqtrace
  (equal (rw.weakening-eqtrace-okp (rw.weakening-eqtrace x))
         t)
  :hints(("Goal" :in-theory (enable rw.weakening-eqtrace rw.weakening-eqtrace-okp))))
