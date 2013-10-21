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
(%interactive)


;; BOZO move this to primitives
;; BOZO why bother, why not just use the two-nats-measure to admit it?

(defthm rank-of-fifth
  (equal (< (rank (fifth x)) (rank x))
         (consp x)))

(%autoprove rank-of-fifth)


(defthm rank-of-fifth-weak
  (equal (< (rank x) (rank (fifth x)))
         nil))

(%autoprove rank-of-fifth-weak)

(defthm rank-of-cdr-of-cdr-of-cdr-weak
  (equal (< (rank x)
            (rank (cdr (cdr (cdr x)))))
         nil))

(%autoprove rank-of-cdr-of-cdr-of-cdr-weak
            (%restrict default rank (memberp x '(x (cdr x) (cdr (cdr x))))))

(defthm rank-of-cdr-of-cdr-of-cdr
  (equal (< (rank (cdr (cdr (cdr x))))
            (rank x))
         (consp x)))

(%autoprove rank-of-cdr-of-cdr-of-cdr
            (%restrict default rank (memberp x '(x (cdr x) (cdr (cdr x))))))


(%autoadmit rw.flag-eqtracep)
(%autoadmit rw.eqtracep)
(%autoadmit rw.eqtrace-listp)

(%autoprove definition-of-rw.eqtracep
            (%restrict default rw.flag-eqtracep (equal x 'x))
            (%enable default rw.eqtracep rw.eqtrace-listp))

(%autoprove definition-of-rw.eqtrace-listp
            (%restrict default rw.flag-eqtracep (equal x 'x))
            (%enable default rw.eqtracep rw.eqtrace-listp))

(%autoprove rw.flag-eqtracep-of-trace
            (%enable default rw.eqtracep))

(%autoprove rw.flag-eqtracep-of-list
            (%enable default rw.eqtrace-listp))



(defmacro %rw.flag-eqtracep-induction-raw (flag x)
  ;; This is a lot better than autoinduct for controlling cases
  `(%induct (two-nats-measure (rank ,x) (if (equal ,flag 'trace) '1 '0))
            ((equal ,flag 'trace)
             (((,flag 'list) (,x (cdr (cdr (cdr ,x)))))))
            ((and (not (equal ,flag 'trace))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'trace))
                  (consp ,x))
             (((,flag 'trace) (,x (car ,x)))
              ((,flag 'list) (,x (cdr ,x)))))))

(%autoprove lemma-for-booleanp-of-rw.eqtracep
            (%rw.flag-eqtracep-induction-raw flag x)
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%restrict default definition-of-rw.eqtrace-listp (equal x 'x)))

(%autoprove booleanp-of-rw.eqtracep
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtracep)
                             (flag 'trace))))

(%autoprove booleanp-of-rw.eqtrace-listp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtracep)
                             (flag 'list))))

(%autoprove rw.eqtrace-listp-when-not-consp
            (%restrict default definition-of-rw.eqtrace-listp (equal x 'x)))

(%autoprove rw.eqtrace-listp-of-cons
            (%restrict default definition-of-rw.eqtrace-listp (equal x '(cons a x))))

(%deflist rw.eqtrace-listp (x)
          (rw.eqtracep x))



(%autoadmit rw.eqtrace->method)
(%autoadmit rw.eqtrace->iffp)
(%autoadmit rw.eqtrace->lhs)
(%autoadmit rw.eqtrace->rhs)
(%autoadmit rw.eqtrace->subtraces)

(%autoprove forcing-symbolp-of-rw.eqtrace->method
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->method))

(%autoprove forcing-booleanp-of-rw.eqtrace->iffp
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->iffp))

(%autoprove forcing-logic.termp-of-rw.eqtrace->lhs
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->lhs))

(%autoprove forcing-logic.termp-of-rw.eqtrace->rhs
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->rhs))

(%autoprove forcing-rw.eqtrace-listp-of-rw.eqtrace->subtraces
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->subtraces))

(%autoprove forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs
            (%restrict default definition-of-rw.eqtracep (equal x 'x))
            (%enable default rw.eqtrace->lhs rw.eqtrace->rhs))

(%autoprove forcing-logic.term-<-of-rw.eqtrace->lhs-and-rw.eqtrace->rhs-free)

;; BOZO move to primitives
(%autoprove |(< a (+ b c d e f a g))|)

;; BOZO really want this still?  Don't think so...
(%autoprove rank-of-rw.eqtrace->subtraces-weak
            (%enable default rw.eqtrace->subtraces))



(%autoadmit rw.flag-eqtrace-atblp)
(%autoadmit rw.eqtrace-atblp)
(%autoadmit rw.eqtrace-list-atblp)

(%autoprove definition-of-rw.eqtrace-atblp
            (%restrict default rw.flag-eqtrace-atblp (equal x 'x))
            (%enable default rw.eqtrace-atblp rw.eqtrace-list-atblp))

(%autoprove definition-of-rw.eqtrace-list-atblp
            (%restrict default rw.flag-eqtrace-atblp (equal x 'x))
            (%enable default rw.eqtrace-atblp rw.eqtrace-list-atblp))

(%autoprove rw.flag-eqtrace-atblp-of-trace
            (%enable default rw.eqtrace-atblp))

(%autoprove rw.flag-eqtrace-atblp-of-list
            (%enable default rw.eqtrace-list-atblp))




(defmacro %rw.flag-eqtracep-induction (flag x)
  `(%induct (two-nats-measure (rank ,x) (if (equal ,flag 'trace) '1 '0))
            ((equal ,flag 'trace)
             (((,flag 'list) (,x (rw.eqtrace->subtraces ,x)))))
            ((and (not (equal ,flag 'trace))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'trace))
                  (consp ,x))
             (((,flag 'trace) (,x (car ,x)))
              ((,flag 'list) (,x (cdr ,x)))))))

(%autoprove lemma-for-booleanp-of-rw.eqtrace-atblp
            (%rw.flag-eqtracep-induction flag x)
            (%restrict default definition-of-rw.eqtrace-atblp (equal x 'x))
            (%restrict default definition-of-rw.eqtrace-list-atblp (equal x 'x)))

(%autoprove booleanp-of-rw.eqtrace-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-atblp)
                             (flag 'trace))))

(%autoprove booleanp-of-rw.eqtrace-list-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.eqtrace-atblp)
                             (flag 'list))))

(%autoprove rw.eqtrace-list-atblp-when-not-consp
            (%restrict default definition-of-rw.eqtrace-list-atblp (equal x 'x)))

(%autoprove rw.eqtrace-list-atblp-of-cons
            (%restrict default definition-of-rw.eqtrace-list-atblp (equal x '(cons a x))))

(%autoprove rw.eqtrace-atblp-of-nil
            (%restrict default definition-of-rw.eqtrace-atblp (equal x ''nil)))

(%deflist rw.eqtrace-list-atblp (x atbl)
          (rw.eqtrace-atblp x atbl))

(%autoprove forcing-logic.term-atblp-of-rw.eqtrace->lhs
            (%restrict default definition-of-rw.eqtrace-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-rw.eqtrace->rhs
            (%restrict default definition-of-rw.eqtrace-atblp (equal x 'x)))

(%autoprove forcing-rw.eqtrace-list-atblp-of-rw.eqtrace->subtraces
            (%restrict default definition-of-rw.eqtrace-atblp (equal x 'x)))




(%autoadmit rw.eqtrace)
(%noexec rw.eqtrace)

(%autoprove rw.eqtrace->method-of-rw.eqtrace
            (%enable default rw.eqtrace rw.eqtrace->method))

(%autoprove rw.eqtrace->iffp-of-rw.eqtrace
            (%enable default rw.eqtrace rw.eqtrace->iffp))

(%autoprove rw.eqtrace->lhs-of-rw.eqtrace
            (%enable default rw.eqtrace rw.eqtrace->lhs))

(%autoprove rw.eqtrace->rhs-of-rw.eqtrace
            (%enable default rw.eqtrace rw.eqtrace->rhs))

(%autoprove rw.eqtrace->subtraces-of-rw.eqtrace
            (%enable default rw.eqtrace rw.eqtrace->subtraces))

(%autoprove forcing-rw.eqtracep-of-rw.eqtrace
            (%restrict default definition-of-rw.eqtracep (equal x '(CONS (CONS LHS RHS) (CONS IFFP (CONS METHOD SUBTRACES)))))
            (%enable default rw.eqtrace))

(%autoprove forcing-rw.eqtrace-atblp-of-rw.eqtrace
            (%restrict default definition-of-rw.eqtrace-atblp
                       (equal x '(rw.eqtrace method iffp lhs rhs subtraces))))

(%autoprove rw.eqtrace-under-iff
            (%enable default rw.eqtrace))


(defsection rw.trace-list-iffps
  (local (%disable default forcing-booleanp-of-rw.eqtrace->iffp))
  (%defprojection :list (rw.eqtrace-list-iffps x)
                  :element (rw.eqtrace->iffp x)
                  :nil-preservingp t))

(defsection rw.eqtrace-list-lhses
  (local (%disable default forcing-booleanp-of-rw.eqtrace->iffp))
  (%defprojection :list (rw.eqtrace-list-lhses x)
                  :element (rw.eqtrace->lhs x)
                  :nil-preservingp t))

(defsection rw.eqtrace-list-rhses
  (local (%disable default forcing-booleanp-of-rw.eqtrace->iffp))
  (%defprojection :list (rw.eqtrace-list-rhses x)
                  :element (rw.eqtrace->rhs x)
                  :nil-preservingp t))

(%autoprove forcing-logic.term-listp-of-rw.eqtrace-list-lhses (%cdr-induction x))
(%autoprove forcing-logic.term-listp-of-rw.eqtrace-list-rhses (%cdr-induction x))
(%autoprove forcing-logic.term-list-atblp-of-rw.eqtrace-list-lhses (%cdr-induction x))
(%autoprove forcing-logic.term-list-atblp-of-rw.eqtrace-list-rhses (%cdr-induction x))
(%autoprove rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps (%cdr-induction row))
(%autoprove rw.eqtrace->iffp-when-all-equalp-of-rw.eqtrace-list-iffps-alt)


(%autoprove rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses
            (%cdr-induction x))

(%autoprove rw.eqtrace->lhs-when-all-equalp-of-rw.eqtrace-list-lhses-alt)

(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/eqtracep")

