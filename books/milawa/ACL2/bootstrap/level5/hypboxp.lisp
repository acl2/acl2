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

(%autoadmit rw.hypboxp)
(%autoadmit rw.hypbox)
(%autoadmit rw.hypbox->left)
(%autoadmit rw.hypbox->right)

(encapsulate
 ()
 (local (%enable default rw.hypboxp rw.hypbox rw.hypbox->left rw.hypbox->right))
 (%autoprove booleanp-of-rw.hypboxp)
 (%autoprove forcing-rw.hypboxp-of-rw.hypbox)
 (%autoprove rw.hypbox->left-of-rw.hypbox)
 (%autoprove rw.hypbox->right-of-rw.hypbox)
 (%autoprove forcing-logic.term-listp-of-rw.hypbox->left)
 (%autoprove forcing-logic.term-listp-of-rw.hypbox->right)
 (%autoprove forcing-true-listp-of-rw.hypbox->left)
 (%autoprove forcing-true-listp-of-rw.hypbox->right)
 (%autoprove forcing-equal-of-rw.hypbox-one)
 (%autoprove forcing-equal-of-rw.hypbox-two))

(%autoadmit rw.hypbox-atblp)

(encapsulate
 ()
 (local (%enable default rw.hypbox-atblp))
 (%autoprove booleanp-of-rw.hypbox-atblp)
 (%autoprove forcing-rw.hypbox-atblp-of-quote-nil)
 (%autoprove forcing-logic.term-list-atblp-of-rw.hypbox->left)
 (%autoprove forcing-logic.term-list-atblp-of-rw.hypbox->right)
 (%autoprove forcing-rw.hypbox-atblp-of-rw.hypbox)
 (%autoprove rw.hypbox-atblp-of-nil))

(%autoadmit rw.hypbox-formula)
(%autoprove forcing-logic.formulap-of-rw.hypbox-formula
            (%enable default rw.hypbox-formula))
(%autoprove forcing-logic.formula-atblp-of-rw.hypbox-formula
            (%enable default rw.hypbox-formula))


(%deflist rw.hypbox-listp (x)
  (rw.hypboxp x))

(%deflist rw.hypbox-list-atblp (x atbl)
  (rw.hypbox-atblp x atbl))

(%autoadmit logic.true-term-listp)

(%autoprove logic.true-term-listp-removal
            (%cdr-induction x)
            (%restrict default logic.true-term-listp (equal x 'x)))

(%autoadmit rw.faster-hypboxp)

(%autoprove rw.faster-hypboxp-removal
            (%enable default rw.faster-hypboxp rw.hypboxp))


(%ensure-exactly-these-rules-are-missing "../../rewrite/assms/hypboxp")

