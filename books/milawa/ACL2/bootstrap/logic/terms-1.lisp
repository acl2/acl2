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


(%autoadmit logic.variablep)

(%autoprove booleanp-of-logic.variablep
            (%enable default logic.variablep))

(%autoprove symbolp-when-logic.variablep
            (%enable default logic.variablep))

(%autoprove logic.variablep-when-consp
            (%enable default logic.variablep))



(%autoadmit logic.constantp)

(%autoprove booleanp-of-logic.constantp
            (%enable default logic.constantp))

(%autoprove logic.constantp-when-not-consp
            (%enable default logic.constantp))

(%autoprove logic.constantp-of-list-quote
            (%enable default logic.constantp))



(%autoadmit logic.unquote)

(%autoprove logic.unquote-of-list-quote
            (%enable default logic.unquote))

(%autoprove logic.unquote-under-iff-when-logic.constantp
            (%enable default logic.constantp logic.unquote))

(%autoprove equal-of-logic.unquote-and-logic.unquote
            (%enable default logic.constantp logic.unquote)
            (%restrict default tuplep (memberp n '('2 '1))))

(%autoprove logic.variablep-when-logic.constantp
            (%enable default logic.variablep logic.constantp))

(%autoprove logic.constantp-when-logic.variablep)


(%autoadmit logic.function-namep)

(%autoprove booleanp-of-logic.function-namep
            (%enable default logic.function-namep))

(%autoprove symbolp-when-logic.function-namep
            (%enable default logic.function-namep))

(%autoprove logic.function-namep-when-consp
            (%enable default logic.function-namep))

(%autoprove logic.constantp-when-cons-of-logic.function-namep
            (%enable default logic.constantp))

(%autoprove logic.variablep-of-cons-when-logic.function-namep
            (%enable default logic.variablep))

