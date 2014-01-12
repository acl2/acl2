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
(include-book "proofp-1")
(%interactive)



(%autoadmit logic.make-basis-step)

(%autoprove forcing-logic.formulap-of-logic.make-basis-step
            (%enable default logic.make-basis-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-basis-step
            (%enable default logic.make-basis-step))



(%autoadmit logic.make-induction-step)

(%autoprove forcing-logic.formulap-of-logic.make-induction-step
            (%enable default logic.make-induction-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-induction-step
            (%enable default logic.make-induction-step))



(%autoadmit logic.make-induction-steps)

(defmacro %logic.make-induction-steps-induction (qs all-sigmas)
  `(%induct (rank ,qs)
            ((not (consp ,qs))
             nil)
            ((consp ,qs)
             (((,qs         (cdr ,qs))
               (,all-sigmas (cdr ,all-sigmas)))))))

(%autoprove true-listp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove len-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove forcing-logic.formula-listp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-induction-steps
            (%logic.make-induction-steps-induction qs all-sigmas)
            (%restrict default logic.make-induction-steps (equal qs 'qs)))



(%autoadmit logic.make-ordinal-step)

(%autoprove forcing-logic.formulap-of-logic.make-ordinal-step
            (%enable default logic.make-ordinal-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-ordinal-step
            (%enable default logic.make-ordinal-step))



(%autoadmit logic.make-measure-step)

(%autoprove forcing-logic.formulap-of-logic.make-measure-step
            (%enable default logic.make-measure-step))

(%autoprove forcing-logic.formula-atblp-of-logic.make-measure-step
            (%enable default logic.make-measure-step))



(%autoadmit logic.make-measure-steps)

(%autoprove forcing-logic.formula-listp-of-logic.make-measure-steps
            (%cdr-induction sigmas-i)
            (%restrict default logic.make-measure-steps (equal sigmas-i 'sigmas-i)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-measure-steps
            (%cdr-induction sigmas-i)
            (%restrict default logic.make-measure-steps (equal sigmas-i 'sigmas-i)))



(%autoadmit logic.make-all-measure-steps)

(defmacro %logic.make-all-measure-steps-induction (qs all-sigmas)
  `(%induct (rank ,all-sigmas)
            ((not (consp ,all-sigmas))
             nil)
            ((consp ,all-sigmas)
             (((qs         (cdr ,qs))
               (all-sigmas (cdr ,all-sigmas)))))))

(%autoprove true-listp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

(%autoprove forcing-logic.formula-listp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

(%autoprove forcing-logic.formula-list-atblp-of-logic.make-all-measure-steps
            (%logic.make-all-measure-steps-induction qs all-sigmas)
            (%restrict default logic.make-all-measure-steps (equal all-sigmas 'all-sigmas)))

