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


(definlined rw.trans1-eqtrace-okp (x)
  ;; A equiv B, B equiv C --> A equiv C
  (declare (xargs :guard (rw.eqtracep x)))
  (let ((method    (rw.eqtrace->method x))
        (iffp      (rw.eqtrace->iffp x))
        (lhs       (rw.eqtrace->lhs x))
        (rhs       (rw.eqtrace->rhs x))
        (subtraces (rw.eqtrace->subtraces x)))
    (and (equal method 'trans1)
         (equal (len subtraces) 2)
         (let* ((sub1 (first subtraces))
                (sub2 (second subtraces)))
           (and (equal lhs (rw.eqtrace->lhs sub1))
                (equal (rw.eqtrace->rhs sub1) (rw.eqtrace->lhs sub2))
                (equal rhs (rw.eqtrace->rhs sub2))
                (implies (not iffp)
                         (and (not (rw.eqtrace->iffp sub1))
                              (not (rw.eqtrace->iffp sub2)))))))))

(encapsulate
 ()
 (local (in-theory (enable rw.trans1-eqtrace-okp)))

 (defthm booleanp-of-rw.trans1-eqtrace-okp
   (equal (booleanp (rw.trans1-eqtrace-okp x))
          t))

 (defthm rw.eqtrace->rhs-of-sub1-when-rw.trans1-eqtrace-okp
   (implies (rw.trans1-eqtrace-okp x)
            (equal (rw.eqtrace->rhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->lhs (second (rw.eqtrace->subtraces x))))))

 (defthm rw.eqtrace->lhs-of-sub1-when-rw.trans1-eqtrace-okp
   (implies (rw.trans1-eqtrace-okp x)
            (equal (rw.eqtrace->lhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->lhs x))))

 (defthm rw.eqtrace->rhs-of-sub2-when-rw.trans1-eqtrace-okp
   (implies (rw.trans1-eqtrace-okp x)
            (equal (rw.eqtrace->rhs (second (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->rhs x)))))



(definlined rw.trans1-eqtrace (iffp x y)
  (declare (xargs :guard (and (booleanp iffp)
                              (rw.eqtracep x)
                              (rw.eqtracep y)
                              (equal (rw.eqtrace->rhs x) (rw.eqtrace->lhs y))
                              (implies (not iffp)
                                       (and (not (rw.eqtrace->iffp x))
                                            (not (rw.eqtrace->iffp y)))))
                  :verify-guards nil))
  (rw.eqtrace 'trans1
              iffp
              (rw.eqtrace->lhs x)
              (rw.eqtrace->rhs y)
              (list x y)))

(encapsulate
 ()
 (local (in-theory (enable rw.trans1-eqtrace)))

 (defthmd lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace
   (implies (and (rw.eqtracep x)
                 (rw.eqtracep y)
                 (equal (rw.eqtrace->rhs x) (rw.eqtrace->lhs y)))
            (logic.term-< (rw.eqtrace->lhs x) (rw.eqtrace->rhs y)))
   :hints(("Goal"
           :in-theory (disable forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs)
           :use ((:instance forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs (x x))
                 (:instance forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs (x y))))))

 (local (in-theory (enable lemma-for-forcing-rw.eqtracep-of-rw.trans1-eqtrace)))

 (verify-guards rw.trans1-eqtrace)

 (defthm rw.eqtrace->method-of-rw.trans1-eqtrace
   (equal (rw.eqtrace->method (rw.trans1-eqtrace iffp x y))
          'trans1))

 (defthm rw.eqtrace->iffp-of-rw.trans1-eqtrace
   (equal (rw.eqtrace->iffp (rw.trans1-eqtrace iffp x y))
          iffp))

 (defthm rw.eqtrace->lhs-of-rw.trans1-eqtrace
   (equal (rw.eqtrace->lhs (rw.trans1-eqtrace iffp x y))
          (rw.eqtrace->lhs x)))

 (defthm rw.eqtrace->rhs-of-rw.trans1-eqtrace
   (equal (rw.eqtrace->rhs (rw.trans1-eqtrace iffp x y))
          (rw.eqtrace->rhs y)))

 (defthm rw.eqtrace->subtraces-of-rw.trans1-eqtrace
   (equal (rw.eqtrace->subtraces (rw.trans1-eqtrace iffp x y))
          (list x y)))

 (defthm forcing-rw.eqtracep-of-rw.trans1-eqtrace
   (implies (force (and (rw.eqtracep x)
                        (rw.eqtracep y)
                        (booleanp iffp)
                        (equal (rw.eqtrace->rhs x) (rw.eqtrace->lhs y))))
            (equal (rw.eqtracep (rw.trans1-eqtrace iffp x y))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.trans1-eqtrace
   (implies (force (and (rw.eqtrace-atblp x atbl)
                        (rw.eqtrace-atblp y atbl)))
            (equal (rw.eqtrace-atblp (rw.trans1-eqtrace iffp x y) atbl)
                   t)))

 (defthm forcing-rw.trans1-eqtrace-okp-of-rw.trans1-eqtrace
   (implies (force (and (equal (rw.eqtrace->rhs x) (rw.eqtrace->lhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.trans1-eqtrace-okp (rw.trans1-eqtrace iffp x y))
                   t))
   :hints(("Goal" :in-theory (enable rw.trans1-eqtrace-okp)))))




(definlined rw.trans2-eqtrace-okp (x)
  ;; A equiv B, A equiv C --> B equiv C
  (declare (xargs :guard (rw.eqtracep x)))
  (let ((method    (rw.eqtrace->method x))
        (iffp      (rw.eqtrace->iffp x))
        (lhs       (rw.eqtrace->lhs x))
        (rhs       (rw.eqtrace->rhs x))
        (subtraces (rw.eqtrace->subtraces x)))
    (and (equal method 'trans2)
         (equal (len subtraces) 2)
         (let* ((sub1 (first subtraces))
                (sub2 (second subtraces)))
           (and (equal (rw.eqtrace->lhs sub1) (rw.eqtrace->lhs sub2))
                (equal lhs (rw.eqtrace->rhs sub1))
                (equal rhs (rw.eqtrace->rhs sub2))
                (implies (not iffp)
                         (and (not (rw.eqtrace->iffp sub1))
                              (not (rw.eqtrace->iffp sub2)))))))))

(encapsulate
 ()
 (local (in-theory (enable rw.trans2-eqtrace-okp)))

 (defthm booleanp-of-rw.trans2-eqtrace-okp
   (equal (booleanp (rw.trans2-eqtrace-okp x))
          t))

 (defthm rw.eqtrace->lhs-of-sub1-when-rw.trans2-eqtrace-okp
   (implies (rw.trans2-eqtrace-okp x)
            (equal (rw.eqtrace->lhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->lhs (second (rw.eqtrace->subtraces x))))))

 (defthm rw.eqtrace->rhs-of-sub1-when-rw.trans2-eqtrace-okp
   (implies (rw.trans2-eqtrace-okp x)
            (equal (rw.eqtrace->rhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->lhs x))))

 (defthm rw.eqtrace->rhs-of-sub2-when-rw.trans2-eqtrace-okp
   (implies (rw.trans2-eqtrace-okp x)
            (equal (rw.eqtrace->rhs (second (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->rhs x)))))



(definlined rw.trans2-eqtrace (iffp x y)
  (declare (xargs :guard (and (booleanp iffp)
                              (rw.eqtracep x)
                              (rw.eqtracep y)
                              (equal (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))
                              (logic.term-< (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))
                              (implies (not iffp)
                                       (and (not (rw.eqtrace->iffp x))
                                            (not (rw.eqtrace->iffp y)))))
                  :verify-guards nil))
  (rw.eqtrace 'trans2
              iffp
              (rw.eqtrace->rhs x)
              (rw.eqtrace->rhs y)
              (list x y)))

(encapsulate
 ()
 (local (in-theory (enable rw.trans2-eqtrace)))

 (verify-guards rw.trans2-eqtrace)

 (defthm rw.eqtrace->method-of-rw.trans2-eqtrace
   (equal (rw.eqtrace->method (rw.trans2-eqtrace iffp x y))
          'trans2))

 (defthm rw.eqtrace->iffp-of-rw.trans2-eqtrace
   (equal (rw.eqtrace->iffp (rw.trans2-eqtrace iffp x y))
          iffp))

 (defthm rw.eqtrace->lhs-of-rw.trans2-eqtrace
   (equal (rw.eqtrace->lhs (rw.trans2-eqtrace iffp x y))
          (rw.eqtrace->rhs x)))

 (defthm rw.eqtrace->rhs-of-rw.trans2-eqtrace
   (equal (rw.eqtrace->rhs (rw.trans2-eqtrace iffp x y))
          (rw.eqtrace->rhs y)))

 (defthm rw.eqtrace->subtraces-of-rw.trans2-eqtrace
   (equal (rw.eqtrace->subtraces (rw.trans2-eqtrace iffp x y))
          (list x y)))

 (defthm forcing-rw.eqtracep-of-rw.trans2-eqtrace
   (implies (force (and (booleanp iffp)
                        (rw.eqtracep x)
                        (rw.eqtracep y)
                        (equal (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))
                        (logic.term-< (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))))
            (equal (rw.eqtracep (rw.trans2-eqtrace iffp x y))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.trans2-eqtrace
   (implies (force (and (rw.eqtrace-atblp x atbl)
                        (rw.eqtrace-atblp y atbl)))
            (equal (rw.eqtrace-atblp (rw.trans2-eqtrace iffp x y) atbl)
                   t)))

 (defthm forcing-rw.trans2-eqtrace-okp-of-rw.trans2-eqtrace
   (implies (force (and (equal (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.trans2-eqtrace-okp (rw.trans2-eqtrace iffp x y))
                   t))
   :hints(("Goal" :in-theory (enable rw.trans2-eqtrace-okp)))))





(definlined rw.trans3-eqtrace-okp (x)
  ;; A equiv C, B equiv C --> A equiv B
  (declare (xargs :guard (rw.eqtracep x)))
  (let ((method    (rw.eqtrace->method x))
        (iffp      (rw.eqtrace->iffp x))
        (lhs       (rw.eqtrace->lhs x))
        (rhs       (rw.eqtrace->rhs x))
        (subtraces (rw.eqtrace->subtraces x)))
    (and (equal method 'trans3)
         (equal (len subtraces) 2)
         (let* ((sub1 (first subtraces))
                (sub2 (second subtraces)))
           (and (equal lhs (rw.eqtrace->lhs sub1))
                (equal rhs (rw.eqtrace->lhs sub2))
                (equal (rw.eqtrace->rhs sub1) (rw.eqtrace->rhs sub2))
                (implies (not iffp)
                         (and (not (rw.eqtrace->iffp sub1))
                              (not (rw.eqtrace->iffp sub2)))))))))

(encapsulate
 ()
 (local (in-theory (enable rw.trans3-eqtrace-okp)))

 (defthm booleanp-of-rw.trans3-eqtrace-okp
   (equal (booleanp (rw.trans3-eqtrace-okp x))
          t))

 (defthm rw.eqtrace->rhs-of-sub1-when-rw.trans3-eqtrace-okp
   (implies (rw.trans3-eqtrace-okp x)
            (equal (rw.eqtrace->rhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->rhs (second (rw.eqtrace->subtraces x))))))

 (defthm rw.eqtrace->lhs-of-sub1-when-rw.trans3-eqtrace-okp
   (implies (rw.trans3-eqtrace-okp x)
            (equal (rw.eqtrace->lhs (first (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->lhs x))))

 (defthm rw.eqtrace->lhs-of-sub2-when-rw.trans3-eqtrace-okp
   (implies (rw.trans3-eqtrace-okp x)
            (equal (rw.eqtrace->lhs (second (rw.eqtrace->subtraces x)))
                   (rw.eqtrace->rhs x)))))



(definlined rw.trans3-eqtrace (iffp x y)
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.eqtracep y)
                              (booleanp iffp)
                              (equal (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))
                              (logic.term-< (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))
                              (implies (not iffp)
                                       (and (not (rw.eqtrace->iffp x))
                                            (not (rw.eqtrace->iffp y)))))
                  :verify-guards nil))
  (rw.eqtrace 'trans3
              iffp
              (rw.eqtrace->lhs x)
              (rw.eqtrace->lhs y)
              (list x y)))

(encapsulate
 ()
 (local (in-theory (enable rw.trans3-eqtrace)))

 (verify-guards rw.trans3-eqtrace)

 (defthm rw.eqtrace->method-of-rw.trans3-eqtrace
   (equal (rw.eqtrace->method (rw.trans3-eqtrace iffp x y))
          'trans3))

 (defthm rw.eqtrace->iffp-of-rw.trans3-eqtrace
   (equal (rw.eqtrace->iffp (rw.trans3-eqtrace iffp x y))
          iffp))

 (defthm rw.eqtrace->lhs-of-rw.trans3-eqtrace
   (equal (rw.eqtrace->lhs (rw.trans3-eqtrace iffp x y))
          (rw.eqtrace->lhs x)))

 (defthm rw.eqtrace->rhs-of-rw.trans3-eqtrace
   (equal (rw.eqtrace->rhs (rw.trans3-eqtrace iffp x y))
          (rw.eqtrace->lhs y)))

 (defthm rw.eqtrace->subtraces-of-rw.trans3-eqtrace
   (equal (rw.eqtrace->subtraces (rw.trans3-eqtrace iffp x y))
          (list x y)))

 (defthm forcing-rw.eqtracep-of-rw.trans3-eqtrace
   (implies (force (and (booleanp iffp)
                        (rw.eqtracep x)
                        (rw.eqtracep y)
                        (equal (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))
                        (logic.term-< (rw.eqtrace->lhs x) (rw.eqtrace->lhs y))))
            (equal (rw.eqtracep (rw.trans3-eqtrace iffp x y))
                   t)))

 (defthm forcing-rw.eqtrace-atblp-of-rw.trans3-eqtrace
   (implies (force (and (rw.eqtrace-atblp x atbl)
                        (rw.eqtrace-atblp y atbl)))
            (equal (rw.eqtrace-atblp (rw.trans3-eqtrace iffp x y) atbl)
                   t)))

 (defthm forcing-rw.trans3-eqtrace-okp-of-rw.trans3-eqtrace
   (implies (force (and (equal (rw.eqtrace->rhs x) (rw.eqtrace->rhs y))
                        (implies (not iffp)
                                 (and (not (rw.eqtrace->iffp x))
                                      (not (rw.eqtrace->iffp y))))))
            (equal (rw.trans3-eqtrace-okp (rw.trans3-eqtrace iffp x y))
                   t))
   :hints(("Goal" :in-theory (enable rw.trans3-eqtrace-okp)))))

