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

;; NOTE: magic evaluation is not used anymore, because it was a lot easier
;; to take it out than try to explain why it is sound. :)

;; (include-book
;;  "../../../rewrite/magic-evaluator")
;; (include-book "evaluator-bldr-2")
;; (%interactive)


;; (%defchoose evaluable-termp-witness n (x defs)
;;             (generic-evaluator x defs n))

;; (defsection evaluable-termp
;;   (%defun evaluable-termp (x defs)
;;           (let ((n (evaluable-termp-witness x defs)))
;;             (generic-evaluator x defs n)))
;;   (%admit))

;; (%autoprove evaluable-termp-suff
;;             (%use (build.axiom (defchoose-axiom-for-evaluable-termp-witness)))
;;             (%use (%instance (%thm evaluable-termp))))

;; (%autoadmit magic-evaluator)

;; (%autoprove forcing-logic.constantp-of-magic-evaluator
;;             (%enable default magic-evaluator))




;; (%autoadmit magic-evaluator-bldr)

;; (%autoprove forcing-logic.appealp-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

;; (%autoprove forcing-logic.conclusion-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

;; (%autoprove forcing-logic.proofp-of-magic-evaluator-bldr
;;             (%enable default magic-evaluator magic-evaluator-bldr))

