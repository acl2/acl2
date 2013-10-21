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
(include-book "add-equality")
(include-book "smart-negate")
(include-book "assmctrl")
(%interactive)


(defsection rw.assmsp

  (%autoadmit rw.assmsp)
  (%autoadmit rw.assms)
  (%autoadmit rw.assms->hypbox)
  (%autoadmit rw.assms->contradiction)
  (%autoadmit rw.assms->eqdatabase)
  (%autoadmit rw.assms->trueterms)
  (%autoadmit rw.assms->ctrl)
  (%autoadmit rw.assms-atblp)

  (local (%enable default
                  rw.assmsp
                  rw.assms
                  rw.assms->hypbox
                  rw.assms->contradiction
                  rw.assms->eqdatabase
                  rw.assms->trueterms
                  rw.assms->ctrl
                  rw.assms-atblp))

  (%autoprove booleanp-of-rw.assmsp)
  (%autoprove booleanp-of-rw.assms-atblp)
  (%autoprove forcing-rw.assmsp-of-rw.assms)
  (%autoprove forcing-rw.assms-atblp-of-rw.assms)
  (%autoprove rw.assms->hypbox-of-rw.assms)
  (%autoprove rw.assms->contradiction-of-rw.assms)
  (%autoprove rw.assms->eqdatabase-of-rw.assms)
  (%autoprove rw.assms->trueterms-of-rw.assms)
  (%autoprove rw.assms->ctrl-of-rw.assms)
  (%autoprove forcing-rw.hypboxp-of-rw.assms->hypbox)
  (%autoprove forcing-rw.hypbox-atblp-of-rw.assms->hypbox)
  (%autoprove forcing-rw.eqdatabasep-of-rw.assms->eqdatabase)
  (%autoprove forcing-rw.eqdatabase-okp-of-rw.assms->eqdatabase)
  (%autoprove forcing-rw.eqdatabase-atblp-of-rw.assms->eqdatabase)
  (%autoprove rw.assms->contradiction-when-no-assumptions)
  (%autoprove forcing-rw.eqtracep-of-rw.assms->contradiction)
  (%autoprove forcing-rw.eqtrace-contradictionp-of-rw.assms->contradiction)
  (%autoprove forcing-rw.eqtrace-okp-of-rw.assms->contradiction-and-rw.assms->hypbox)
  (%autoprove forcing-logic.term-listp-of-rw.assms->trueterms)
  (%autoprove forcing-logic.term-list-atblp-of-rw.assms->trueterms)
  (%autoprove forcing-rw.assmctrlp-of-rw.assms->ctrl)
  (%autoprove forcing-equal-of-rw.assms-one)
  (%autoprove forcing-equal-of-rw.assms-two)
  (%autoprove rw.assms-atblp-of-nil))

(%deflist rw.assms-listp (x)
          (rw.assmsp x))

(%deflist rw.assms-list-atblp (x atbl)
          (rw.assms-atblp x atbl))



(defsection rw.empty-eqdatabase

  (%autoadmit rw.empty-eqdatabase)
  (%noexec rw.empty-eqdatabase)

  (local (%enable default
                  rw.empty-eqdatabase
                  rw.eqdatabase-atblp
                  rw.eqdatabase-okp))

  (%autoprove rw.eqdatabasep-of-rw.empty-eqdatabase)
  (%autoprove rw.eqdatabase-atblp-of-rw.empty-eqdatabase)
  (%autoprove rw.eqdatabase-okp-of-rw.empty-eqdatabase)
  (%autoprove rw.eqdatabase->equalsets-of-rw.empty-eqdatabase)
  (%autoprove rw.eqdatabase->contradiction-of-rw.empty-eqdatabase))



(defsection rw.empty-assms

  (%autoadmit rw.empty-assms)
  (%noexec rw.empty-assms)

  (local (%enable default rw.empty-assms))

  (%autoprove rw.assmsp-of-rw.empty-assms)
  (%autoprove rw.assms-atblp-of-rw.empty-assms (%enable default rw.assms-atblp))
  (%autoprove rw.assms->hypbox-of-rw.empty-assms)
  (%autoprove rw.assms->contradiction-of-rw.empty-assms)
  (%autoprove rw.assms->eqdatabase-of-rw.empty-assms)
  (%autoprove rw.assms->trueterms-of-rw.empty-assms)
  (%autoprove rw.assms->ctrl-of-rw.empty-assms))





(%autoprove rw.eqset-atblp-when-not-consp
            (%enable default rw.eqset-atblp rw.eqset->tail))

(%autoprove forcing-rw.eqset-atblp-of-rw.find-relevant-set
            (%autoinduct rw.find-relevant-eqset term sets)
            (%restrict default rw.find-relevant-eqset (equal eqsets 'sets)))



(defsection rw.assume-left

  (%autoadmit rw.assume-left)

  (%autoprove lemma-for-rw.assume-left
              (%disable default rw.eqdatabase-okp-in-extended-hypbox)
              (%use (%instance (%thm rw.eqdatabase-okp-in-extended-hypbox)
                               (sub (rw.assms->hypbox assms))
                               (sup (rw.hypbox (cons nhyp (rw.hypbox->left (rw.assms->hypbox assms)))
                                               (rw.hypbox->right (rw.assms->hypbox assms))))
                               (x (rw.assms->eqdatabase assms)))))

  (local (%enable default
                  rw.assume-left
                  lemma-for-rw.assume-left))

  (%autoprove forcing-rw.assmsp-of-rw.assume-left)
  (%autoprove forcing-rw.assms-atblp-of-rw.assume-left)
  (%autoprove rw.assms->hypbox-of-rw.assume-left))



(defsection rw.assume-right

  (%autoadmit rw.assume-right)

  (%autoprove lemma-for-rw.assume-right
              (%disable default rw.eqdatabase-okp-in-extended-hypbox)
              (%use (%instance (%thm rw.eqdatabase-okp-in-extended-hypbox)
                               (sub (rw.assms->hypbox assms))
                               (sup (rw.hypbox (rw.hypbox->left (rw.assms->hypbox assms))
                                               (cons nhyp (rw.hypbox->right (rw.assms->hypbox assms)))))
                               (x (rw.assms->eqdatabase assms)))))

  (local (%enable default
                  rw.assume-right
                  lemma-for-rw.assume-right))

  (%autoprove forcing-rw.assmsp-of-rw.assume-right)
  (%autoprove forcing-rw.assms-atblp-of-rw.assume-right)
  (%autoprove rw.assms->hypbox-of-rw.assume-right))



(defsection rw.assume-left-list

  (%autoadmit rw.assume-left-list)

  (%autoprove rw.assume-left-list-when-not-consp
              (%restrict default rw.assume-left-list (equal nhyps 'nhyps)))

  (%autoprove rw.assume-left-list-of-cons
              (%restrict default rw.assume-left-list (equal nhyps '(cons nhyp nhyps))))

  (%autoprove forcing-rw.assmsp-of-rw.assume-left-list
              (%cdr-induction nhyps))

  (%autoprove forcing-rw.assms-atblp-of-rw.assume-left-list
              (%cdr-induction nhyps))

  (%autoprove forcing-rw.assms->nhyps-of-rw.assume-left-list
              (%cdr-induction nhyps)))



(defsection rw.assume-right-list

  (%autoadmit rw.assume-right-list)

  (%autoprove rw.assume-right-list-when-not-consp
              (%restrict default rw.assume-right-list (equal nhyps 'nhyps)))

  (%autoprove rw.assume-right-list-of-cons
              (%restrict default rw.assume-right-list (equal nhyps '(cons nhyp nhyps))))

  (%autoprove forcing-rw.assmsp-of-rw.assume-right-list
              (%cdr-induction nhyps))

  (%autoprove forcing-rw.assms-atblp-of-rw.assume-right-list
              (%cdr-induction nhyps))

  (%autoprove forcing-rw.assms->hypbox-right-of-rw.assume-right-list
              (%cdr-induction nhyps)))





(%autoadmit rw.assms-emptyp)

(%autoprove booleanp-of-rw.assms-emptyp
            (%enable default rw.assms-emptyp))

(%autoprove rw.assms-emptyp-of-rw.empty-assms
            (%enable default rw.assms-emptyp))



(%autoadmit rw.assms-formula)

(%autoprove forcing-logic.formulap-of-rw.assms-formula
            (%enable default rw.assms-formula rw.assms-emptyp))

(%autoprove forcing-logic.formula-atblp-of-rw.assms-formula
            (%enable default rw.assms-formula rw.assms-emptyp))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/assmsp")

