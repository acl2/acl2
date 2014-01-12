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

(defsection build.reflexivity-list
  (%autoadmit build.reflexivity-list)
  (local (%restrict default build.reflexivity-list (equal x 'x)))
  (%autoprove forcing-logic.appeal-listp-of-build.reflexivity-list (%cdr-induction x))
  (%autoprove forcing-logic.strip-conclusions-of-build.reflexivity-list (%cdr-induction x))
  (%autoprove forcing-logic.proof-listp-of-build.reflexivity-list (%cdr-induction x)))

;; There isn't really any reason to bother optimizing these; the
;; modus-ponens-list steps get optimized in level 3 anyway so these will only
;; be like two steps.

(defsection build.pequal-by-args
  (%autoadmit build.pequal-by-args)
  (local (%enable default logic.functional-axiom build.pequal-by-args))
  (%autoprove forcing-build.pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.pequal-by-args))

(defsection build.disjoined-pequal-by-args
  (%autoadmit build.disjoined-pequal-by-args)
  (local (%enable default logic.functional-axiom build.disjoined-pequal-by-args))
  (%autoprove forcing-build.disjoined-pequal-by-args-under-iff)
  (%autoprove forcing-logic.appealp-of-build.disjoined-pequal-by-args)
  (%autoprove forcing-logic.conclusion-of-build.disjoined-pequal-by-args)
  (%autoprove forcing-logic.proofp-of-build.disjoined-pequal-by-args))

