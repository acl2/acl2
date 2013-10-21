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
(%interactive)

(%autoprove rank-of-cdr-of-lookup-weak
            (%cdr-induction map))

(%autoprove rank-of-cdr-of-cdr-of-cdr-of-cdr-weak
            (%restrict default rank (memberp x '(x (cdr x) (cdr (cdr x)) (cdr (cdr (cdr x)))))))


(%autoadmit rw.flag-tracep)
(%autoadmit rw.tracep)
(%autoadmit rw.trace-listp)

(%autoprove definition-of-rw.tracep
            (%enable default rw.tracep rw.trace-listp)
            (%restrict default rw.flag-tracep (equal x 'x)))

(%autoprove definition-of-rw.trace-listp
            (%enable default rw.tracep rw.trace-listp)
            (%restrict default rw.flag-tracep (equal x 'x)))

(defmacro %rw.raw-trace-induction (flag x)
  `(%induct (two-nats-measure (rank ,x)
                              (if (equal ,flag 'term) '1 '0))
            ((equal ,flag 'term)
             (((,x (cdr (cdr (cdr (cdr ,x))))) (,flag 'list))))
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,x (car ,x)) (,flag 'term))
              ((,x (cdr ,x)) (,flag 'list))))))

(%autoprove rw.trace-listp-when-not-consp
            (%restrict default definition-of-rw.trace-listp (equal x 'x)))

(%autoprove rw.trace-listp-of-cons
            (%restrict default definition-of-rw.trace-listp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.tracep
            (%rw.raw-trace-induction flag x)
            (%restrict default definition-of-rw.tracep (equal x 'x)))

(%autoprove booleanp-of-rw.tracep
            (%use (%instance (%thm lemma-for-booleanp-of-rw.tracep)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-listp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.tracep)
                             (flag 'list))))

(%deflist rw.trace-listp (x)
          (rw.tracep x))

(%deflist rw.trace-list-listp (x)
          (rw.trace-listp x))



(%autoadmit rw.trace->method)
(%autoadmit rw.trace->hypbox)
(%autoadmit rw.trace->lhs)
(%autoadmit rw.trace->rhs)
(%autoadmit rw.trace->iffp)
(%autoadmit rw.trace->subtraces)
(%autoadmit rw.trace->extras)

(%defprojection :list (rw.trace-list-iffps x)
                :element (rw.trace->iffp x))

(%defprojection :list (rw.trace-list-lhses x)
                :element (rw.trace->lhs x))

(%defprojection :list (rw.trace-list-rhses x)
                :element (rw.trace->rhs x))

(%defprojection :list (rw.trace-list-hypboxes x)
                :element (rw.trace->hypbox x))

(%defprojection :list (rw.trace-list-list-rhses x)
                :element (rw.trace-list-rhses x))



(%autoadmit rw.trace)

(%autoprove rw.trace-under-iff
            (%enable default rw.trace))

(%autoprove rw.trace->method-of-rw.trace
            (%enable default rw.trace rw.trace->method))

(%autoprove rw.trace->hypbox-of-rw.trace
            (%enable default rw.trace rw.trace->hypbox))

(%autoprove rw.trace->lhs-of-rw.trace
            (%enable default rw.trace rw.trace->lhs))

(%autoprove rw.trace->rhs-of-rw.trace
            (%enable default rw.trace rw.trace->rhs))

(%autoprove rw.trace->iffp-of-rw.trace
            (%enable default rw.trace rw.trace->iffp))

(%autoprove rw.trace->subtraces-of-rw.trace
            (%enable default rw.trace rw.trace->subtraces))

(%autoprove rw.trace->extras-of-rw.trace
            (%enable default rw.trace rw.trace->extras))

(%autoprove forcing-rw.tracep-of-rw.trace
            (%enable default rw.trace)
            (%restrict default definition-of-rw.tracep
                       (equal x '(CONS (CONS METHOD RHS)
                                       (CONS (CONS LHS IFFP)
                                             (CONS HYPBOX (CONS EXTRAS SUBTRACES)))))))

(%autoprove forcing-symbolp-of-rw.trace->method
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->method))

(%autoprove forcing-rw.hypboxp-of-rw.trace->hypbox
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->hypbox))

(%autoprove forcing-logic.termp-of-rw.trace->lhs
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->lhs))

(%autoprove forcing-logic.termp-of-rw.trace->rhs
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->rhs))

(%autoprove forcing-booleanp-of-rw.trace->iffp
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->iffp))

(%autoprove forcing-rw.trace-listp-of-rw.trace->subtraces
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->subtraces))

(%autoprove forcing-logic.term-listp-of-rw.trace-list-lhses
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-rw.trace-list-rhses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-rw.trace-list-list-rhses
            (%cdr-induction x))

(%autoprove cons-listp-of-rw.trace-list-list-rhses
            (%cdr-induction x))




(%autoprove rw.trace->lhs-under-iff
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->lhs))

(%autoprove rw.trace->rhs-under-iff
            (%restrict default definition-of-rw.tracep (equal x 'x))
            (%enable default rw.trace->rhs))

(%autoprove rank-of-rw.trace->subtraces-weak
            (%enable default rw.trace->subtraces))




(%autoadmit rw.flag-trace-atblp)
(%autoadmit rw.trace-atblp)
(%autoadmit rw.trace-list-atblp)

(%autoprove definition-of-rw.trace-atblp
            (%enable default rw.trace-atblp rw.trace-list-atblp)
            (%restrict default rw.flag-trace-atblp (equal x 'x)))

(%autoprove definition-of-rw.trace-list-atblp
            (%enable default rw.trace-atblp rw.trace-list-atblp)
            (%restrict default rw.flag-trace-atblp (equal x 'x)))

(%autoprove rw.trace-atblp-of-nil
            (%restrict default definition-of-rw.trace-atblp (equal x ''nil)))

(defmacro %rw.trace-induction (flag x)
  `(%induct (two-nats-measure (rank ,x)
                              (if (equal ,flag 'term) '1 '0))
            ((equal ,flag 'term)
             (((x (rw.trace->subtraces ,x)) (,flag 'list))))
            ((and (not (equal ,flag 'term))
                  (not (consp ,x)))
             nil)
            ((and (not (equal ,flag 'term))
                  (consp ,x))
             (((,x (car ,x)) (,flag 'term))
              ((,x (cdr ,x)) (,flag 'list))))))

(%autoprove rw.trace-list-atblp-when-not-consp
            (%restrict default definition-of-rw.trace-list-atblp (equal x 'x)))

(%autoprove rw.trace-list-atblp-of-cons
            (%restrict default definition-of-rw.trace-list-atblp (equal x '(cons a x))))

(%autoprove lemma-for-booleanp-of-rw.trace-atblp
            (%rw.trace-induction flag x)
            (%restrict default definition-of-rw.trace-atblp (equal x 'x)))

(%autoprove booleanp-of-rw.trace-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-atblp)
                             (flag 'term))))

(%autoprove booleanp-of-rw.trace-list-atblp
            (%use (%instance (%thm lemma-for-booleanp-of-rw.trace-atblp)
                             (flag 'list))))

(%deflist rw.trace-list-atblp (x atbl)
          (rw.trace-atblp x atbl))



(%autoprove forcing-rw.hypbox-atblp-of-rw.trace->hypbox
            (%restrict default definition-of-rw.trace-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-rw.trace->lhs
            (%restrict default definition-of-rw.trace-atblp (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-rw.trace->rhs
            (%restrict default definition-of-rw.trace-atblp (equal x 'x)))

(%autoprove forcing-logic.term-list-atblp-of-rw.trace->subtraces
            (%restrict default definition-of-rw.trace-atblp (equal x 'x)))

(%autoprove forcing-logic.term-list-atblp-of-rw.trace-list-lhses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-rw.trace-list-rhses
            (%cdr-induction x))

(%autoprove forcing-rw.trace-atblp-of-rw.trace
            (%restrict default definition-of-rw.trace-atblp
                       (equal x '(rw.trace method hypbox lhs rhs iffp subtraces extras))))



(%autoadmit rw.trace-conclusion-formula)
(%noexec rw.trace-conclusion-formula)
(%autoprove forcing-logic.formulap-of-rw.trace-conclusion-formula
            (%enable default rw.trace-conclusion-formula))
(%autoprove forcing-logic.formula-atblp-of-rw.trace-conclusion-formula
            (%enable default rw.trace-conclusion-formula))


(%defprojection :list (rw.trace-list-conclusion-formulas x)
                :element (rw.trace-conclusion-formula x))
(%autoprove forcing-logic.formula-listp-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))
(%autoprove forcing-logic.formula-list-atblp-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))

(%autoadmit rw.trace-formula)
(%autoprove forcing-logic.formulap-of-rw.trace-formula
            (%enable default rw.trace-formula))
(%autoprove forcing-logic.formula-atblp-of-rw.trace-formula
            (%enable default rw.trace-formula))

(%defprojection :list (rw.trace-list-formulas x)
                :element (rw.trace-formula x))
(%autoprove forcing-logic.formula-listp-of-rw.trace-list-formulas
            (%cdr-induction x))
(%autoprove forcing-logic.formula-list-atblp-of-rw.trace-list-formulas
            (%cdr-induction x))


(local (%enable default rw.trace-conclusion-formula rw.trace-formula))

(%autoprove logic.all-atomicp-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))
(%autoprove logic.all-atomicp-of-rw.trace-list-conclusion-formulas-free)

(%autoprove logic.=rhses-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x)
            (%auto)
            ;; BOZO why?? I had to add this after adding outside-in rules.
            (%fertilize (LOGIC.=RHSES (RW.TRACE-LIST-CONCLUSION-FORMULAS X2))
                        (REPEAT ''T (LEN X2))))
(%autoprove logic.=rhses-of-rw.trace-list-conclusion-formulas-free)

(%autoprove logic.all-functionsp-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))
(%autoprove logic.all-functionsp-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free)

(%autoprove logic.strip-function-names-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))
(%autoprove logic.strip-function-names-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free)

(%autoprove strip-lens-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-conclusion-formulas
            (%cdr-induction x))
(%autoprove strip-lens-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-conclusion-formulas-free)

(%autoprove strip-firsts-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses
            (%cdr-induction x))
(%autoprove strip-firsts-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses-free)

(%autoprove strip-seconds-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses
            (%cdr-induction x))
(%autoprove strip-seconds-of-logic.strip-function-args-of-logic.=lhses-of-rw.trace-list-lhses-free)

(local (%enable default forcing-equal-of-logic.por-list-rewrite))

(%autoprove rw.trace-list-formulas-when-all-equalp-of-rw.trace-list-hypboxes
            (%cdr-induction x)
            (%splitlimit 10))



(%autoadmit rw.faster-flag-tracep)
(%autoadmit rw.faster-tracep)
(%autoadmit rw.faster-trace-listp)

(%autoprove definition-of-rw.faster-tracep
            (%restrict default rw.faster-flag-tracep (equal x 'x))
            (%enable default rw.faster-tracep rw.faster-trace-listp))

(%autoprove definition-of-rw.faster-trace-listp
            (%restrict default rw.faster-flag-tracep (equal x 'x))
            (%enable default rw.faster-tracep rw.faster-trace-listp))

(%autoprove rw.faster-flag-tracep-of-term
            (%enable default rw.faster-tracep))

(%autoprove rw.faster-flag-tracep-of-list
            (%enable default rw.faster-trace-listp))

(%autoprove rw.faster-trace-listp-when-not-consp
            (%restrict default definition-of-rw.faster-trace-listp (equal x 'x)))

(%autoprove rw.faster-trace-listp-of-cons
            (%restrict default definition-of-rw.faster-trace-listp (equal x '(cons a x))))

(%autoprove lemma-for-rw.faster-tracep-removal
            (%autoinduct rw.faster-flag-tracep flag x hypbox)
            (%forcingp nil)
            (%restrict default definition-of-rw.faster-tracep (equal x 'x))
            (%restrict default definition-of-rw.tracep (equal x 'x)))

(%autoprove rw.faster-tracep-removal
            (%use (%instance (%thm lemma-for-rw.faster-tracep-removal)
                             (flag 'term))))

(%autoprove rw.faster-trace-listp-removal
            (%use (%instance (%thm lemma-for-rw.faster-tracep-removal)
                             (flag 'list))))



(%ensure-exactly-these-rules-are-missing "../../rewrite/traces/tracep")

