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

(%autoadmit logic.=lhses-of-strip-conclusions)
(%autoprove logic.=lhses-of-strip-conclusions-removal
            (%restrict default logic.=lhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=rhses-of-strip-conclusions)
(%autoprove logic.=rhses-of-strip-conclusions-removal
            (%restrict default logic.=rhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.vrhses-of-strip-conclusions)
(%autoprove logic.vrhses-of-strip-conclusions-removal
            (%restrict default logic.vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.vlhses-of-strip-conclusions)
(%autoprove logic.vlhses-of-strip-conclusions-removal
            (%restrict default logic.vlhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=lhses-of-vrhses-of-strip-conclusions)
(%autoprove logic.=lhses-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.=lhses-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.=rhses-of-vrhses-of-strip-conclusions)
(%autoprove logic.=rhses-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.=rhses-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-atomicp-of-strip-conclusions)
(%autoprove logic.all-atomicp-of-strip-conclusions-removal
            (%restrict default logic.all-atomicp-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-disjunctionsp-of-strip-conclusions)
(%autoprove logic.all-disjunctionsp-of-strip-conclusions-removal
            (%restrict default logic.all-disjunctionsp-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

(%autoadmit logic.all-atomicp-of-vrhses-of-strip-conclusions)
(%autoprove logic.all-atomicp-of-vrhses-of-strip-conclusions-removal
            (%restrict default logic.all-atomicp-of-vrhses-of-strip-conclusions (equal x 'x))
            (%cdr-induction x))

